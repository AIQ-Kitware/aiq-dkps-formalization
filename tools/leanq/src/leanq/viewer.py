"""Self-contained interactive HTML renderer for leanq proof graphs."""

from __future__ import annotations

import html
import json
from importlib.resources import files
from pathlib import Path


_TEMPLATE = "assets/viewer.html"


def _safe_json_for_script(payload: dict) -> str:
    """JSON text safe to embed in a ``<script type=application/json>`` node."""
    text = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
    # HTML parsers recognize </script> even inside non-JavaScript script data.
    # Escaping angle brackets preserves the JSON value while preventing that
    # sentinel and keeps arbitrary declaration/documentation text inert.
    return text.replace("<", r"\u003c").replace(">", r"\u003e").replace("&", r"\u0026")


def render_graph_html(payload: dict, *, title: str | None = None) -> str:
    """Render one graph payload as a standalone, offline HTML document."""
    presentation = payload.get("presentation") or {}
    display_title = title or presentation.get("title")
    if not display_title:
        targets = payload.get("targets") or []
        display_title = "Lean proof dependencies"
        if targets:
            display_title += f": {str(targets[0]).rsplit('.', 1)[-1]}"
    template = files("leanq").joinpath(_TEMPLATE).read_text(encoding="utf-8")
    return template.replace("__LEANQ_TITLE__", html.escape(display_title)).replace(
        "__LEANQ_DATA__", _safe_json_for_script(payload)
    )


def write_graph_html(path: Path, payload: dict, *, title: str | None = None) -> Path:
    """Write a standalone graph viewer, creating parent directories as needed."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render_graph_html(payload, title=title), encoding="utf-8")
    return path
