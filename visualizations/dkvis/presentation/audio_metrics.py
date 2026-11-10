"""Local generation-duration history for approximate speech queue ETAs.

Only a hash of the effective voice/profile configuration is stored. No voice
names, transcript contents, reference audio, or request payloads are persisted.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sqlite3
from statistics import median
import time


class AudioMetrics:
    def __init__(self, cache: Path):
        self.path = Path(cache) / 'generation-times.sqlite3'

    @staticmethod
    def key(configuration):
        payload = json.dumps(configuration, ensure_ascii=False, sort_keys=True)
        return hashlib.sha256(payload.encode('utf-8')).hexdigest()

    def _connection(self):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        connection = sqlite3.connect(self.path, timeout=5)
        connection.execute('CREATE TABLE IF NOT EXISTS completed ('
                           'config_hash TEXT NOT NULL, words INTEGER NOT NULL, '
                           'seconds REAL NOT NULL, recorded_at REAL NOT NULL)')
        connection.execute('CREATE INDEX IF NOT EXISTS by_config ON completed'
                           '(config_hash, recorded_at DESC)')
        return connection

    def record(self, config_hash, words, seconds):
        if words < 1 or not 0 < seconds < 36000:
            return
        try:
            with self._connection() as connection:
                connection.execute('INSERT INTO completed VALUES (?, ?, ?, ?)',
                                   (config_hash, words, seconds, time.time()))
                # Keep bounded history for local use.
                connection.execute('DELETE FROM completed WHERE rowid IN ('
                                   'SELECT rowid FROM completed WHERE recorded_at < ?)',
                                   (time.time() - 90 * 86400,))
        except (OSError, sqlite3.Error):
            pass  # Timing diagnostics must never prevent publishing audio.

    def estimate(self, config_hash):
        try:
            with self._connection() as connection:
                rows = connection.execute(
                    'SELECT words, seconds FROM completed WHERE config_hash=? '
                    'ORDER BY recorded_at DESC LIMIT 40', (config_hash,)).fetchall()
        except (OSError, sqlite3.Error):
            rows = []
        samples = [seconds / words for words, seconds in rows if words >= 4 and seconds > 0]
        # Initial estimate is deliberately coarse; once samples exist use the
        # median to withstand retries and occasional slow generations.
        return dict(seconds_per_word=median(samples) if samples else .6,
                    sample_count=len(samples), source='observed' if samples else 'initial')
