"""Small declarative deck specifications for reusable Manim slide scenes.

A :class:`SlideUse` says which existing scene to render and how that scene is
used in one particular deck.  Presentation metadata such as ``depth`` belongs
here rather than on the reusable scene implementation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

VALID_DEPTHS = {"", "*", "**"}


@dataclass(frozen=True)
class SlideUse:
    """One use of a reusable scene inside a deck."""

    module: str
    scene: str
    depth: str = ""

    def __post_init__(self) -> None:
        if not self.module:
            raise ValueError("slide module must be non-empty")
        if not self.scene:
            raise ValueError("slide scene must be non-empty")
        if self.depth not in VALID_DEPTHS:
            raise ValueError(f"invalid slide depth {self.depth!r}; expected one of {sorted(VALID_DEPTHS)!r}")


@dataclass(frozen=True)
class DeckSpec:
    """A named presentation assembled from reusable scenes."""

    name: str
    slides: tuple[SlideUse, ...]
    description: str = ""
    footer: str | None = None
    composite_parts: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("deck name must be non-empty")
        names = self.scene_names
        repeated = sorted({name for name in names if names.count(name) > 1})
        if repeated:
            raise ValueError(f"deck {self.name!r} repeats scenes: {repeated!r}")

    @property
    def scene_names(self) -> list[str]:
        return [slide.scene for slide in self.slides]

    def slide(self, scene: str) -> SlideUse:
        for slide in self.slides:
            if slide.scene == scene:
                return slide
        raise KeyError(f"deck {self.name!r} has no scene {scene!r}")

    def grouped_by_module(self) -> list[tuple[str, list[str]]]:
        """Return scenes grouped by source module in first-use order."""
        grouped: dict[str, list[str]] = {}
        for slide in self.slides:
            grouped.setdefault(slide.module, []).append(slide.scene)
        return list(grouped.items())


def use(module: str, scene: str, *, depth: str = "") -> SlideUse:
    return SlideUse(module=module, scene=scene, depth=depth)


def uses(module: str, scenes: Iterable[str], *, depth: str = "") -> tuple[SlideUse, ...]:
    return tuple(use(module, scene, depth=depth) for scene in scenes)
