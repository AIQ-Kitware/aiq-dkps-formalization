"""Background whole-lecture caching: bounded scheduling, resume and cancellation."""
from __future__ import annotations

import threading
import time

from dkvis.presentation.audio_preparation import PreparationManager


def wait_until(predicate, timeout=4):
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        if predicate():
            return
        time.sleep(.01)
    raise AssertionError('Preparation did not reach expected state')


def test_preparation_stays_active_and_limits_submissions():
    manager = PreparationManager(max_inflight=3)
    pending = set()
    calls = []
    lock = threading.Lock()

    def request(page):
        with lock:
            calls.append(page)
            pending.add(page)
        return {'state': 'queued'}

    def status(page):
        with lock:
            return {'state': 'queued' if page in pending else 'ready'}

    try:
        status0 = manager.start('123000', 'hash', 8, request, status)
        assert status0['state'] == 'running'
        wait_until(lambda: len(calls) == 3)
        assert manager.start('123000', 'hash', 8, request, status)['submitted'] == 3
        time.sleep(.06)
        assert len(calls) == 3  # Bounded backlog, not all pages at once.
        with lock:
            pending.clear()
        wait_until(lambda: manager.status('123000', 'hash')['submitted'] >= 6)
        with lock:
            pending.clear()
        wait_until(lambda: manager.status('123000', 'hash')['submitted'] == 8)
        with lock:
            pending.clear()
        wait_until(lambda: manager.status('123000', 'hash')['state'] == 'finished')
        assert manager.status('123000', 'hash')['checked'] == 8
        assert calls == list(range(8))
    finally:
        manager.close()


def test_cancel_stops_future_submissions():
    manager = PreparationManager(max_inflight=2)
    lock = threading.Lock()
    calls = []

    def request(page):
        with lock:
            calls.append(page)
        return {'state': 'queued'}

    def status(page):
        return {'state': 'queued'}

    try:
        manager.start('123000', 'hash', 30, request, status)
        wait_until(lambda: len(calls) == 2)
        assert manager.cancel('123000', 'hash')
        wait_until(lambda: manager.status('123000', 'hash')['state'] == 'cancelled')
        time.sleep(.1)
        assert calls == [0, 1]
    finally:
        manager.close()


def test_one_failed_page_does_not_abandon_other_pages():
    manager = PreparationManager(max_inflight=2)

    def request(page):
        if page == 1:
            raise ValueError('bad page')
        return {'state': 'ready'}

    try:
        manager.start('123000', 'hash', 5, request, lambda page: {'state': 'ready'})
        wait_until(lambda: manager.status('123000', 'hash')['state'] == 'finished_with_errors')
        result = manager.status('123000', 'hash')
        assert result['checked'] == 5
        assert result['failed'] == 1
    finally:
        manager.close()


def test_priority_scheduler_reserves_interactive_admission():
    from dkvis.presentation.audio_jobs import SpeechQueue

    queue = SpeechQueue(workers=1, limit=4)
    entered = threading.Event()
    release = threading.Event()
    calls = []

    def work(task):
        calls.append(task.kind)
        if len(calls) == 1:
            entered.set()
            release.wait(3)

    try:
        queue.submit('a', work, kind='cache', lecture_id='000000', page=0,
                     words=20, config_key='config')
        assert entered.wait(2)
        for name in ('b', 'c'):
            queue.submit(name, work, kind='prefetch', lecture_id='000000', page=1,
                         words=20, config_key='config')
        try:
            queue.submit('d', work, kind='cache', lecture_id='000000', page=2,
                         words=20, config_key='config')
        except OverflowError:
            pass
        else:
            raise AssertionError('Background job consumed the playback slot')
        queue.submit('interactive', work, kind='playback', lecture_id='001000', page=0,
                     words=20, config_key='config')
        release.set()
        wait_until(lambda: queue.task('interactive').future.done())
        assert calls[:2] == ['cache', 'playback']
    finally:
        release.set()
        queue.close()


def test_server_queue_wait_is_not_reported_as_inference_eta():
    from dkvis.presentation.audio_jobs import SpeechQueue
    queue = SpeechQueue(workers=1, limit=4)
    gate = threading.Event()
    entered = threading.Event()

    def work(task):
        task.progress.update(upstream_state='queued', elapsed_seconds=0,
                             total_passages=1, completed_passages=0)
        entered.set()
        gate.wait(3)

    try:
        task = queue.submit('waiting', work, kind='playback', lecture_id='000000',
                            page=0, words=40, config_key='config')
        assert entered.wait(2)
        # The DKPS worker is active, but server-side synthesis has not started.
        result = queue.describe(task, seconds_per_word=.6)
        assert result['progress']['upstream_state'] == 'queued'
        assert result['estimate_source'] == 'waiting_for_gpu'
        assert 'eta_seconds' not in result
    finally:
        gate.set()
        queue.close()
