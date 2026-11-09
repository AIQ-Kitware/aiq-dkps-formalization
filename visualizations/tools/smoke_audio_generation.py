#!/usr/bin/env python3
"""Inspect or exercise DKPS -> Breeze job progress and cancellation on a live host.

No voice names, transcript text, or reference paths are written to disk or logs.
The exercise deliberately synthesizes real pages; use --exercise to opt in.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen


class SmokeError(RuntimeError):
    pass


class ReaderClient:
    def __init__(self, base, timeout=12):
        self.base = base.rstrip('/')
        self.timeout = timeout

    def _request(self, path, body=None):
        request = Request(
            self.base + path,
            data=json.dumps(body).encode() if body is not None else None,
            headers={'Content-Type': 'application/json'} if body is not None else {},
            method='POST' if body is not None else 'GET',
        )
        try:
            with urlopen(request, timeout=self.timeout) as response:
                return json.load(response)
        except HTTPError as exc:
            raise SmokeError(f'{path.split("?")[0]} returned HTTP {exc.code} (details withheld)') from None
        except URLError as exc:
            raise SmokeError(f'Could not reach {self.base}: {type(exc.reason).__name__}') from None
        except (ValueError, UnicodeDecodeError):
            raise SmokeError(f'{path.split("?")[0]} returned invalid JSON') from None

    def get(self, path, query=None):
        if query:
            path += '?' + urlencode(query)
        return self._request(path)

    def post(self, path, body):
        return self._request(path, body)


def select_profile(data, wanted):
    profiles = data.get('profiles') or []
    if wanted:
        if not any(row.get('id') == wanted for row in profiles):
            raise SmokeError('Selected profile is not advertised by DKPS')
        return wanted
    possible = [row['id'] for row in profiles
                if 'breeze' in str(row.get('id', '')).lower()
                or 'breeze' in str(row.get('model', '')).lower()]
    if len(possible) == 1:
        return possible[0]
    raise SmokeError('Cannot select one Breeze profile automatically; export DKVIS_TTS_PROFILE locally')


def first_missing(inventory, count):
    return [index for index, state in enumerate(inventory['states'])
            if state in ('missing', 'cancelled', 'error')][:count]


def state_line(label, row):
    counts = row.get('counts', {})
    q = [job for job in row.get('queue', [])
         if job.get('lecture_id') == row.get('lecture_id')]
    paragraphs = sum(item.get('progress', {}).get('completed_passages', 0) for item in q)
    etas = [item['eta_seconds'] for item in q if isinstance(item.get('eta_seconds'), (float, int))]
    eta = f' · ETA ~{max(etas)}s' if etas else ''
    return (f'{label}: cached {row["ready"]}/{row["total"]} · '
            f'active {counts.get("rendering", 0)} · queued {counts.get("queued", 0)} · '
            f'canceling {counts.get("canceling", 0)} · completed passages {paragraphs}{eta}')


def validate_server(server_base, timeout=8):
    client = ReaderClient(server_base, timeout)
    runtime = client.get('/v1/runtime')
    jobs = runtime.get('long_form_jobs')
    if not isinstance(jobs, dict) or jobs.get('path') != '/v1/audio/jobs':
        raise SmokeError('Breeze server lacks the job API; rebuild/restart the new local-ai container')
    return jobs


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--reader-url', default='http://127.0.0.1:8001')
    p.add_argument('--breeze-url', default='http://127.0.0.1:8821')
    p.add_argument('--track', choices=('g2', 'g3'), default='g2')
    p.add_argument('--lecture-a', default='000000', help='lecture to cache, then cancel')
    p.add_argument('--lecture-b', default='001000', help='lecture to play after switching')
    p.add_argument('--pages', type=int, default=3, help='max number of lecture A pages to request')
    p.add_argument('--cancel-delay', type=float, default=4., help='time to observe before switching')
    p.add_argument('--poll', type=float, default=3.)
    p.add_argument('--timeout', type=float, default=240., help='max wait for new lecture page')
    p.add_argument('--speed', type=float, default=1.)
    p.add_argument('--exercise', action='store_true', help='opt in to generating and canceling speech jobs')
    args = p.parse_args(argv)
    if args.pages < 1 or args.pages > 7 or args.poll <= 0 or args.timeout < 1 or args.cancel_delay < 0:
        p.error('pages must be 1..7; poll/timeout positive; cancel-delay nonnegative')
    if args.lecture_a == args.lecture_b:
        p.error('lecture A and lecture B must be different')

    voice = os.environ.get('TTS_BENCH_VOICE', '').strip()
    if not voice:
        raise SmokeError('Set TTS_BENCH_VOICE locally; the script will not display its value')
    reader = ReaderClient(args.reader_url)
    jobs = validate_server(args.breeze_url)
    print(f'Breeze job API available ({jobs.get("workers", "?")} worker(s))')
    profile = select_profile(reader.get('/api/audio-profiles'), os.environ.get('DKVIS_TTS_PROFILE'))
    settings = dict(track=args.track, profile=profile, voice=voice, speed=args.speed)
    a = reader.get('/api/audio-generation/inventory', {**settings, 'lecture_id': args.lecture_a})
    b = reader.get('/api/audio-generation/inventory', {**settings, 'lecture_id': args.lecture_b})
    print(state_line('Lecture A', a))
    print(state_line('Lecture B', b))
    if not args.exercise:
        print('Read-only inspection passed. Add --exercise to request and cancel actual audio jobs.')
        return 0

    apages = first_missing(a, args.pages)
    bpages = first_missing(b, 1)
    if not apages or not bpages:
        raise SmokeError('Test needs uncached pages in both lectures; select other lecture IDs')
    if a['queue']:
        raise SmokeError('Existing speech jobs use this configuration; refusing to interfere with other work')
    print('Requesting lecture A pages:', ', '.join(str(i + 1) for i in apages))
    for index in apages:
        row = reader.post(f'/api/audio-lectures/{args.lecture_a}/pages/{index}/render',
                          {**settings, 'purpose': 'cache'})
        if row.get('state') not in ('ready', 'queued', 'rendering'):
            raise SmokeError('Unexpected response to page request: ' + str(row.get('state')))
    until = time.monotonic() + args.cancel_delay
    while time.monotonic() < until:
        row = reader.get('/api/audio-generation/inventory', {**settings, 'lecture_id': args.lecture_a})
        print(state_line('Lecture A', row))
        time.sleep(min(args.poll, max(0., until-time.monotonic())))

    print('Switching: requesting uncached lecture B page', bpages[0] + 1, 'at playback priority')
    reader.post(f'/api/audio-lectures/{args.lecture_b}/pages/{bpages[0]}/render',
                {**settings, 'purpose': 'playback'})
    cancelled = reader.post('/api/audio-generation/cancel', {**settings, 'lecture_id': args.lecture_a})
    print('Cancellation accepted for', cancelled.get('count', '?'), 'lecture A page(s)')
    if not cancelled.get('count'):
        print('Cancellation is inconclusive: lecture A may have completed before the request')

    deadline = time.monotonic() + args.timeout
    saw_active = False
    while time.monotonic() < deadline:
        a = reader.get('/api/audio-generation/inventory', {**settings, 'lecture_id': args.lecture_a})
        b = reader.get('/api/audio-generation/inventory', {**settings, 'lecture_id': args.lecture_b})
        bstate = b['states'][bpages[0]]
        saw_active |= any(b['counts'].get(key, 0) for key in ('queued', 'rendering'))
        print(state_line('Lecture A', a))
        print(state_line('Lecture B', b))
        if bstate == 'ready':
            if any(a['counts'].get(key, 0) for key in ('queued', 'rendering', 'canceling')):
                print('New lecture ready; previous lecture cancellation is still draining')
            else:
                print('PASS: new lecture ready and previous lecture has no outstanding work')
            print('Observed new lecture queued or rendering:', saw_active)
            return 0
        if bstate == 'error':
            raise SmokeError('New lecture generation failed; inspect reader logs privately')
        time.sleep(args.poll)
    raise SmokeError('Timed out waiting for the new lecture to become ready; inspect job progress and logs')


if __name__ == '__main__':
    try:
        sys.exit(main())
    except SmokeError as exc:
        print('ERROR:', exc, file=sys.stderr)
        sys.exit(1)
