"""Priority scheduler for DKPS speech pages with cooperative cancellation.

The scheduler owns only in-process work. Completed recordings live in the
existing content-addressed audio cache; it does not persist pending tasks.
"""
from __future__ import annotations

from concurrent.futures import Future
from dataclasses import dataclass, field
import heapq
import threading
import time
from typing import Callable


class GenerationCancelled(Exception):
    """Cancelled before a page can be published."""


PRIORITY = {'playback': 0, 'cache': 10, 'prefetch': 20}


@dataclass
class SpeechTask:
    key: str
    callback: Callable
    kind: str
    lecture_id: str
    page: int
    words: int
    config_key: str
    sequence: int
    queued_at: float = field(default_factory=time.monotonic)
    started_at: float | None = None
    finished_at: float | None = None
    future: Future = field(default_factory=Future)
    cancel_event: threading.Event = field(default_factory=threading.Event)
    progress: dict = field(default_factory=dict)
    cancelled: bool = False
    revision: int = 0

    @property
    def priority(self):
        return PRIORITY[self.kind]

    def check_cancelled(self):
        if self.cancel_event.is_set():
            raise GenerationCancelled('Speech generation cancelled')


class SpeechQueue:
    def __init__(self, workers=2, limit=8):
        if workers < 1 or limit < workers:
            raise ValueError('Speech queue capacity must be >= workers >= 1')
        self.limit = limit
        self.condition = threading.Condition()
        self.tasks: dict[str, SpeechTask] = {}
        self.heap = []
        self.sequence = 0
        self.closed = False
        self.threads = [threading.Thread(target=self._work, daemon=True,
                                         name=f'dkps-speech-{i}') for i in range(workers)]
        for thread in self.threads:
            thread.start()

    def submit(self, key, callback, *, kind, lecture_id, page, words, config_key):
        if kind not in PRIORITY:
            raise ValueError('Unknown speech job priority')
        with self.condition:
            previous = self.tasks.get(key)
            if previous and not previous.future.done() and not previous.cancel_event.is_set():
                if PRIORITY[kind] < previous.priority and previous.started_at is None:
                    previous.kind = kind
                    previous.revision += 1
                    heapq.heappush(self.heap, (previous.priority, previous.sequence,
                                               previous.revision, key))
                    self.condition.notify()
                return previous
            count = sum(not task.future.done() and not task.cancel_event.is_set()
                        for task in self.tasks.values())
            if count >= self.limit:
                raise OverflowError('Audio generation queue is full; cancel an old job or retry')
            self.sequence += 1
            task = SpeechTask(key, callback, kind, lecture_id, page, words, config_key, self.sequence)
            self.tasks[key] = task
            heapq.heappush(self.heap, (task.priority, task.sequence, task.revision, key))
            self.condition.notify()
            # Bound task history independently of the durable audio cache.
            if len(self.tasks) > 256:
                old = sorted((t for t in self.tasks.values() if t.future.done()),
                             key=lambda t: t.finished_at or t.queued_at)
                for gone in old[:max(0, len(self.tasks)-192)]:
                    if self.tasks.get(gone.key) is gone:
                        self.tasks.pop(gone.key, None)
            return task

    def _work(self):
        while True:
            with self.condition:
                while not self.heap and not self.closed:
                    self.condition.wait()
                if self.closed:
                    return
                _, _, revision, key = heapq.heappop(self.heap)
                task = self.tasks.get(key)
                if (task is None or task.revision != revision
                        or task.started_at is not None or task.cancel_event.is_set()):
                    continue
                if not task.future.set_running_or_notify_cancel():
                    continue
                task.started_at = time.monotonic()
            try:
                task.check_cancelled()
                result = task.callback(task)
                task.check_cancelled()
                task.future.set_result(result)
            except BaseException as error:
                task.cancelled = task.cancel_event.is_set() or isinstance(error, GenerationCancelled)
                task.future.set_exception(error)
            finally:
                task.finished_at = time.monotonic()
                with self.condition:
                    self.condition.notify_all()

    def task(self, key):
        with self.condition:
            return self.tasks.get(key)

    def describe(self, task, *, seconds_per_word=None):
        with self.condition:
            result = dict(state='cancelled' if task.cancelled or (task.cancel_event.is_set() and task.future.done())
                          else 'canceling' if task.cancel_event.is_set()
                          else 'error' if task.future.done() and task.future.exception()
                          else 'missing' if task.future.done()
                          else 'rendering' if task.started_at is not None else 'queued',
                          lecture_id=task.lecture_id, page=task.page, kind=task.kind,
                          words=task.words)
            if result['state'] == 'error':
                result['error'] = str(task.future.exception())[:500]
            if result['state'] == 'queued':
                pending = sorted((t.priority, t.sequence, t.key) for t in self.tasks.values()
                                 if t.started_at is None and not t.future.done()
                                 and not t.cancel_event.is_set())
                result['queued_position'] = next((i+1 for i, row in enumerate(pending)
                                                  if row[2] == task.key), None)
            if task.started_at is not None:
                result['elapsed_seconds'] = round(max(0, (task.finished_at or time.monotonic()) - task.started_at), 1)
            if task.progress:
                result['progress'] = dict(task.progress)
            if seconds_per_word is not None and result['state'] in ('queued', 'rendering', 'canceling'):
                elapsed = result.get('elapsed_seconds', 0)
                completed = max(0, min(task.words, task.progress.get('completed_words', 0)))
                remaining = (task.words - completed) * seconds_per_word
                if not completed:
                    remaining = task.words * seconds_per_word - elapsed
                # No reliable time remains estimate once a running request
                # exceeds its forecast (or after its last word has been
                # generated but its audio is still being encoded/published).
                # Do not show "0 seconds remaining" until the job is ready.
                if result['state'] in ('rendering', 'canceling') and (
                        completed >= task.words or remaining <= 0):
                    result['estimate_exceeded_seconds'] = round(max(
                        0, elapsed - task.words * seconds_per_word))
                    result['estimate_source'] = 'overdue'
                    return result
                if result['state'] == 'queued':
                    running = (t for t in self.tasks.values()
                               if t.started_at is not None and not t.future.done())
                    workload = sum(max(0, t.words-t.progress.get('completed_words', 0))
                                   for t in running)
                    workload += sum(t.words for t in self.tasks.values()
                                    if t.started_at is None and not t.future.done()
                                    and not t.cancel_event.is_set() and
                                    (t.priority, t.sequence) < (task.priority, task.sequence))
                    workers = max(1, len(self.threads))
                    remaining += workload * seconds_per_word / workers
                result['eta_seconds'] = round(remaining)
                result['estimate_source'] = 'observed' if task.progress.get('eta_samples') else 'initial'
            return result

    def cancel(self, *, lecture_id=None, config_key=None, include_active=True):
        affected = []
        with self.condition:
            for task in self.tasks.values():
                if (lecture_id is not None and task.lecture_id != lecture_id
                        or config_key is not None and task.config_key != config_key
                        or task.future.done() or (not include_active and task.started_at is not None)):
                    continue
                task.cancel_event.set()
                if task.started_at is None:
                    task.cancelled = True
                    task.future.cancel()
                affected.append(dict(lecture_id=task.lecture_id, page=task.page,
                                     state='canceling' if task.started_at else 'cancelled'))
            self.condition.notify_all()
        return affected

    def snapshot(self, *, config_key=None, lecture_id=None, seconds_per_word=None):
        with self.condition:
            tasks = [task for task in self.tasks.values()
                     if (config_key is None or task.config_key == config_key)
                     and (lecture_id is None or task.lecture_id == lecture_id)
                     and not task.future.done()]
            return [self.describe(task, seconds_per_word=seconds_per_word) for task in
                    sorted(tasks, key=lambda t: (t.started_at is None, t.priority, t.sequence))]

    def close(self):
        with self.condition:
            self.closed = True
            for task in self.tasks.values():
                if not task.future.done():
                    task.cancel_event.set()
                    if task.started_at is None:
                        task.cancelled = True
                        task.future.cancel()
            self.condition.notify_all()
        # Workers are daemons. A running legacy HTTP request may not support
        # interruption; do not block process shutdown on it.
