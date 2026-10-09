"""Deprecated Python import path for the completed Kitware talk.

The public deck name is now ``kitware-talk``.  This module remains only to
avoid breaking code that imports ``FRIDAY`` from the old source module.
"""

from __future__ import annotations

from dkvis.decks.kitware_talk import KITWARE_TALK

FRIDAY = KITWARE_TALK
