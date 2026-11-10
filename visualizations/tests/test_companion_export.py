"""PowerPoint and HTML exporters must share the Manim frame contract."""
from pathlib import Path

from dkvis.presentation import companion_export
from dkvis.presentation.companion_slides import SOURCE_DIR


def test_powerpoint_frame_export_uses_manim_images(tmp_path, monkeypatch):
    seen = []

    def fake_manim_frame(deck, slide, index, count, cache_dir=None):
        seen.append((deck['id'], slide['id'], index, count, cache_dir))
        return b'frame-png-' + str(index).encode('ascii')

    monkeypatch.setattr(companion_export, 'render_slide_png', fake_manim_frame)
    source = SOURCE_DIR / 'dkps-fast-path.json'
    output = companion_export.export_companion_frames(source, tmp_path / 'frames',
                                                      cache=tmp_path / 'cache', limit=2)
    assert output['rendered_count'] == 2
    assert output['slide_count'] == 12
    assert len(output['frames']) == 2
    assert [Path(p).read_bytes() for p in output['frames']] == [b'frame-png-0', b'frame-png-1']
    assert [row[2] for row in seen] == [0, 1]
    assert all(row[0] == 'dkps-fast-path' and row[3] == 12 for row in seen)
