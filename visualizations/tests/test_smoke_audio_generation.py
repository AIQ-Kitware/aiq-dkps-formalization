"""Offline coverage for the optional live DKPS generation smoke driver."""
import contextlib
import io
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import smoke_audio_generation as smoke


class FakeReader:
    instances = []

    def __init__(self, base):
        self.calls = []
        self.apages = ['missing', 'missing', 'missing', 'missing']
        self.bpages = ['missing', 'missing', 'missing']
        self.bpolls = 0
        self.cancelled = False
        self.__class__.instances.append(self)

    def get(self, path, query=None):
        if path == '/api/audio-profiles':
            return {'profiles': [{'id': 'math-breeze', 'model': 'breeze-tts2'}], 'default_profile': 'kokoro'}
        if path == '/api/audio-generation/inventory':
            a = query['lecture_id'] == '000000'
            if not a and self.bpages[0] == 'queued':
                self.bpolls += 1
                if self.bpolls >= 2:
                    self.bpages[0] = 'ready'
            states = self.apages if a else self.bpages
            counts = {name: states.count(name) for name in ('ready','missing','queued','rendering','canceling','cancelled','error')}
            queue = [{'lecture_id': query['lecture_id'], 'state': state, 'page': i, 'eta_seconds': 9}
                     for i, state in enumerate(states) if state in ('queued','rendering','canceling')]
            return {'lecture_id': query['lecture_id'], 'ready': counts['ready'], 'total': len(states), 'states': states[:],
                    'counts': counts, 'queue': queue}
        raise AssertionError(path)

    def post(self, path, body):
        self.calls.append((path, dict(body)))
        if path == '/api/audio-generation/cancel':
            self.cancelled = True
            count = 0
            for i, value in enumerate(self.apages):
                if value in ('queued', 'rendering'):
                    self.apages[i] = 'cancelled'
                    count += 1
            return {'count': count}
        if '/000000/' in path:
            page = int(path.split('/pages/')[1].split('/')[0])
            self.apages[page] = 'rendering' if page == 0 else 'queued'
        else:
            page = int(path.split('/pages/')[1].split('/')[0])
            self.bpages[page] = 'queued'
        return {'state': 'queued'}


class TestSmoke(unittest.TestCase):
    def test_profile_selection_and_missing_pages(self):
        data = {'profiles': [{'id': 'breeze-lecture', 'model': 'breeze-tts2'},
                             {'id': 'other', 'model': 'kokoro'}]}
        self.assertEqual(smoke.select_profile(data, None), 'breeze-lecture')
        public = {'profiles': [*data['profiles'], {'id': smoke.PUBLIC_PROFILE, 'model': 'breeze-tts2'}]}
        self.assertEqual(smoke.select_profile(public, None), smoke.PUBLIC_PROFILE)
        self.assertEqual(smoke.select_profile(data, 'other'), 'other')
        with self.assertRaises(smoke.SmokeError):
            smoke.select_profile({'profiles': data['profiles'][:1] * 2}, None)
        with self.assertRaises(smoke.SmokeError):
            smoke.select_profile(data, 'not-listed')
        self.assertEqual(smoke.first_missing({'states': ['ready','missing','rendering','cancelled','error']}, 2), [1,3])

    def test_inspection_is_read_only(self):
        FakeReader.instances.clear()
        with patch.object(smoke, 'ReaderClient', FakeReader), \
             patch.object(smoke, 'validate_server', lambda *a, **kw: {'workers': 1}), \
             patch.dict(os.environ, {'TTS_BENCH_VOICE': 'foobar'}, clear=True), \
             contextlib.redirect_stdout(io.StringIO()):
            result = smoke.main([])
        self.assertEqual(result, 0)
        self.assertEqual(FakeReader.instances[-1].calls, [])

    def test_exercise_switches_priority_and_cancels(self):
        FakeReader.instances.clear()
        output = io.StringIO()
        with patch.object(smoke, 'ReaderClient', FakeReader), \
             patch.object(smoke, 'validate_server', lambda *a, **kw: {'workers': 1}), \
             patch.dict(os.environ, {'TTS_BENCH_VOICE': 'foobar'}, clear=True), \
             contextlib.redirect_stdout(output):
            result = smoke.main(['--exercise', '--pages', '3', '--cancel-delay', '0',
                                 '--poll', '0.001', '--timeout', '1'])
        client = FakeReader.instances[-1]
        self.assertEqual(result, 0)
        self.assertTrue(client.cancelled)
        self.assertEqual([r[1]['purpose'] for r in client.calls if '/render' in r[0]],
                         ['cache', 'cache', 'cache', 'playback'])
        self.assertIn('PASS:', output.getvalue())
        self.assertNotIn('foobar', output.getvalue())

    def test_public_profile_and_voice_are_selected_without_environment(self):
        class PublicReader(FakeReader):
            def get(self, path, query=None):
                if path == '/api/audio-profiles':
                    return {'profiles': [{'id': smoke.PUBLIC_PROFILE, 'model': 'breeze-tts2',
                                          'default_voice': smoke.PUBLIC_VOICE},
                                         {'id': 'other-breeze', 'model': 'breeze-tts2'}],
                            'default_profile': smoke.PUBLIC_PROFILE}
                return super().get(path, query)

        PublicReader.instances.clear()
        with patch.object(smoke, 'ReaderClient', PublicReader), \
             patch.object(smoke, 'validate_server', lambda *a, **kw: {'workers': 1}), \
             patch.dict(os.environ, {}, clear=True), \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(smoke.main([]), 0)
        self.assertEqual(PublicReader.instances[-1].calls, [])

    def test_missing_voice_rejected_for_unconfigured_profile(self):
        with patch.object(smoke, 'ReaderClient', FakeReader), \
             patch.object(smoke, 'validate_server', lambda *a, **kw: {'workers': 1}), \
             patch.dict(os.environ, {}, clear=True), \
             contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaisesRegex(smoke.SmokeError, 'no default voice'):
                smoke.main([])


if __name__ == '__main__':
    unittest.main()
