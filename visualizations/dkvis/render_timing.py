"""Append render timings shared by the slide builder and narrated video runner."""

from __future__ import annotations

from contextlib import contextmanager
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
_CURRENT = None


class TimingLog:
    def __init__(self, context=None):
        self.run_id = os.environ.setdefault(
            "DKVIS_RENDER_RUN_ID",
            datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8],
        )
        self.path = Path(
            os.environ.setdefault(
                "DKVIS_RENDER_TIMING_LOG", str(ROOT / "renders/logs/render-timings.jsonl")
            )
        )
        self.context = dict(
            python_version=platform.python_version(),
            cpu_count=os.cpu_count(),
            platform=platform.system(),
        )
        self.context.update(json.loads(os.environ.get("DKVIS_RENDER_CONTEXT", "{}")))
        self.context.update(context or {})
        self.started = time.perf_counter()

    def set_context(self, **fields):
        self.context.update(fields)
        os.environ["DKVIS_RENDER_CONTEXT"] = json.dumps(self.context)

    def record(self, stage, elapsed_seconds, status="ok", **fields):
        event = dict(
            timestamp=datetime.now(timezone.utc).isoformat(),
            run_id=self.run_id,
            stage=stage,
            elapsed_seconds=round(elapsed_seconds, 6),
            status=status,
            hostname=platform.node(),
            pid=os.getpid(),
            **self.context,
        )
        event.update(fields)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        data = (json.dumps(event, sort_keys=True, default=str) + "\n").encode()
        # One append write keeps independently rendered scenes on separate lines.
        fd = os.open(self.path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
        try:
            os.write(fd, data)
        finally:
            os.close(fd)

    @contextmanager
    def measure(self, stage, **fields):
        start = time.perf_counter()
        status = "ok"
        try:
            yield fields
        except BaseException as error:
            status = "error"
            fields.update(error_type=type(error).__name__, error=str(error))
            raise
        finally:
            self.record(stage, time.perf_counter() - start, status, **fields)

    def report(self):
        stages = {}
        if self.path.exists():
            for line in self.path.read_text().splitlines():
                try:
                    event = json.loads(line)
                except ValueError:
                    continue  # another process may still be appending
                if event.get("run_id") != self.run_id:
                    continue
                row = stages.setdefault(
                    event["stage"],
                    dict(
                        count=0,
                        elapsed_seconds=0.0,
                        errors=0,
                        audio_seconds=0.0,
                        request_seconds=0.0,
                    ),
                )
                row["count"] += 1
                row["elapsed_seconds"] += event["elapsed_seconds"]
                row["errors"] += event["status"] == "error"
                row["request_seconds"] += event.get("request_seconds", 0.0)
                if event["status"] == "ok":
                    row["audio_seconds"] += event.get("audio_seconds", 0.0)
        requests = stages.get("tts_request", {})
        if requests.get("audio_seconds"):
            requests["realtime_factor"] = requests["request_seconds"] / requests["audio_seconds"]
        summary = dict(
            run_id=self.run_id,
            elapsed_seconds=time.perf_counter() - self.started,
            settings=self.context,
            stages=stages,
            events_file=str(self.path),
        )
        target = self.path.parent / f"render-{self.run_id}.json"
        target.write_text(json.dumps(summary, indent=2) + "\n")
        print("\nRender timings (sum of operation durations):", flush=True)
        for stage, row in sorted(stages.items(), key=lambda item: -item[1]["elapsed_seconds"]):
            print(
                f"  {stage:22s} {row['elapsed_seconds']:9.2f}s  ({row['count']} operations)",
                flush=True,
            )
        if requests.get("audio_seconds"):
            print(
                f"  TTS: {requests['audio_seconds']:.1f}s usable audio; {requests['realtime_factor']:.3f}s generation/audio second",
                flush=True,
            )
        print(f"Timings: {self.path}\nRun summary: {target}", flush=True)
        return target


def timing():
    global _CURRENT
    if _CURRENT is None:
        _CURRENT = TimingLog()
    return _CURRENT
