"""Server-owned, bounded background preparation of cached speech pages.

Preparation survives browser navigation. It feeds the ordinary priority queue,
never bypasses cache identities, and never owns any voice/reference material.
Jobs and progress are intentionally in-memory; completed audio is durable.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import threading
import time
from typing import Callable


@dataclass
class Preparation:
    lecture_id: str
    config_key: str
    total: int
    request: Callable[[int], dict]
    status: Callable[[int], dict]
    max_inflight: int = 3
    stop: threading.Event = field(default_factory=threading.Event)
    thread: threading.Thread | None = None
    state: str = 'running'
    submitted: int = 0
    checked: int = 0
    errors: dict[int, str] = field(default_factory=dict)
    started_at: float = field(default_factory=time.monotonic)
    finished_at: float | None = None
    _lock: threading.Lock = field(default_factory=threading.Lock, repr=False)

    def snapshot(self):
        with self._lock:
            return dict(state=self.state, total=self.total, submitted=self.submitted,
                        checked=self.checked, failed=len(self.errors),
                        elapsed_seconds=round((self.finished_at or time.monotonic())
                                              - self.started_at, 1))

    def cancel(self):
        self.stop.set()
        with self._lock:
            if self.state == 'running':
                self.state = 'canceling'

    def run(self):
        pending: set[int] = set()
        next_page = 0
        try:
            while not self.stop.is_set() and (next_page < self.total or pending):
                while (not self.stop.is_set() and next_page < self.total
                       and len(pending) < self.max_inflight):
                    page = next_page
                    try:
                        # All cache requests go through the same priority queue
                        # as interactive playback. Its capacity provides backpressure.
                        # Synchronize enqueue with cancel(): no task may be
                        # submitted after cancellation reaches the DKPS queue.
                        with self._lock:
                            if self.stop.is_set():
                                break
                            result = self.request(page)
                    except OverflowError:
                        break  # Queue full; retry after an outstanding job finishes.
                    except Exception as exc:
                        with self._lock:
                            self.errors[page] = f'{type(exc).__name__}: {exc}'[:200]
                            self.checked += 1
                        next_page += 1
                        continue
                    next_page += 1
                    with self._lock:
                        self.submitted += 1
                    if result['state'] == 'ready':
                        with self._lock:
                            self.checked += 1
                    else:
                        pending.add(page)
                for page in tuple(pending):
                    try:
                        result = self.status(page)
                    except Exception as exc:
                        result = {'state': 'error', 'error': f'{type(exc).__name__}: {exc}'}
                    if result['state'] in ('ready', 'error', 'cancelled'):
                        pending.remove(page)
                        with self._lock:
                            self.checked += 1
                            if result['state'] != 'ready':
                                self.errors[page] = str(result.get('error') or result['state'])[:200]
                if not self.stop.is_set() and (next_page < self.total or pending):
                    self.stop.wait(0.45)
        finally:
            with self._lock:
                self.state = ('cancelled' if self.stop.is_set() else
                              'finished_with_errors' if self.errors else 'finished')
                self.finished_at = time.monotonic()


class PreparationManager:
    """One preparation per lecture/configuration, with deduplicated starts."""

    def __init__(self, *, max_inflight=3):
        self.max_inflight = max_inflight
        self._lock = threading.Lock()
        self._items: dict[tuple[str, str], Preparation] = {}

    def start(self, lecture_id, config_key, total, request, status):
        key = lecture_id, config_key
        with self._lock:
            previous = self._items.get(key)
            if previous is not None and previous.thread is not None and previous.thread.is_alive():
                return previous.snapshot()
            job = Preparation(lecture_id, config_key, total, request, status,
                              max_inflight=self.max_inflight)
            thread = threading.Thread(target=job.run, daemon=True,
                                      name='dkps-cache-' + lecture_id)
            job.thread = thread
            self._items[key] = job
            thread.start()
            return job.snapshot()

    def status(self, lecture_id, config_key):
        with self._lock:
            job = self._items.get((lecture_id, config_key))
        return job.snapshot() if job else None

    def cancel(self, lecture_id, config_key):
        with self._lock:
            job = self._items.get((lecture_id, config_key))
            if job:
                job.cancel()
            return bool(job and job.thread and job.thread.is_alive())

    def close(self):
        with self._lock:
            jobs = list(self._items.values())
        for job in jobs:
            job.cancel()
        for job in jobs:
            if job.thread:
                job.thread.join(timeout=2)
