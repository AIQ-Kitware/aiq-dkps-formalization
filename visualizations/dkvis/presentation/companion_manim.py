"""Render companion-slide source decks as Manim-composed slide images.

The HTML viewer is only a thin wrapper around these rendered slide images.  The
visual source of truth is Manim: every deck build renders each slide as a fresh
scene using the same palette and MathTex toolchain as the hand-authored talk
slides.
"""
from __future__ import annotations

from pathlib import Path
import re
import textwrap

from dkvis.palette import PALETTE, tint
from dkvis.presentation.companion_figures import figure_svg


_SENTENCE_BREAK = re.compile(r'(?<=[.!?])\s+(?=[A-Z])')


def render_slide_png(deck: dict, slide: dict, index: int, count: int, *, cache_dir: Path | None = None) -> bytes:
    """Render one companion slide to PNG bytes with Manim.

    Parameters
    ----------
    deck, slide:
        Parsed companion-slide JSON records.
    index, count:
        Zero-based slide number and deck size.
    cache_dir:
        Directory for temporary SVG assets and Manim's media output.
    """
    try:
        from manim import (
            DOWN,
            LEFT,
            RIGHT,
            UP,
            UL,
            UR,
            MathTex,
            Paragraph,
            Rectangle,
            RoundedRectangle,
            Scene,
            SVGMobject,
            SurroundingRectangle,
            Text,
            VGroup,
            config,
            tempconfig,
        )
    except ModuleNotFoundError as ex:  # pragma: no cover - exercised in user env
        raise RuntimeError(
            'Companion-slide builds now require Manim. Install the visualizations '
            'extras and run the build in that environment.'
        ) from ex

    from dkvis.slide_style import TEMPLATE

    cache_dir = Path(cache_dir or Path.cwd() / '.companion-manim-cache').resolve()
    cache_dir.mkdir(parents=True, exist_ok=True)
    figure_dir = cache_dir / 'figures'
    figure_dir.mkdir(parents=True, exist_ok=True)

    bg = PALETTE['BG']
    fg = PALETTE['FG']
    muted = PALETTE['MUTED']
    faint = PALETTE['FAINT']
    panel = PALETTE['PANEL']
    wanted = PALETTE['WANTED']
    trial = PALETTE['TRIAL']
    sine = PALETTE['SINE']

    def _materialize_diagram(kind: str) -> Path:
        path = figure_dir / f'{kind}.svg'
        if not path.exists():
            path.write_text(figure_svg(kind), encoding='utf-8')
        return path

    def _wrap(text: str, width: int) -> list[str]:
        raw = ' '.join(text.split())
        if not raw:
            return ['']
        return textwrap.wrap(raw, width=width, break_long_words=False, break_on_hyphens=False) or [raw]

    def _text_block(text: str, width: float, *, font_size: float = 26, color: str = fg,
                    line_spacing: float = 0.82, width_chars: int = 44) -> Paragraph:
        mob = Paragraph(*_wrap(text, width_chars), alignment='left', font_size=font_size,
                        color=color, line_spacing=line_spacing)
        if mob.width > width:
            mob.scale_to_fit_width(width)
        return mob

    def _paragraphs(lines: list[str], width: float, *, font_size: float = 25,
                    color: str = fg, width_chars: int = 45, buff: float = 0.22) -> VGroup:
        blocks = VGroup(*[
            _text_block(line, width, font_size=font_size, color=color,
                        width_chars=width_chars, line_spacing=0.82)
            for line in lines if line.strip()
        ])
        if len(blocks):
            blocks.arrange(DOWN, aligned_edge=LEFT, buff=buff)
        return blocks

    def _reading_beats() -> list[str]:
        beats: list[str] = []
        for paragraph in slide.get('body', []):
            sentences = _SENTENCE_BREAK.split(' '.join(paragraph.split()))
            for sentence in sentences:
                sentence = sentence.strip()
                if not sentence:
                    continue
                if beats and len(beats[-1]) + len(sentence) < 175:
                    beats[-1] += ' ' + sentence
                else:
                    beats.append(sentence)
        for bullet in slide.get('bullets', []):
            beats.append(f'• {bullet}')
        return beats

    def _split_columns(lines: list[str]) -> tuple[list[str], list[str]]:
        if len(lines) <= 4 and sum(len(line) for line in lines) < 540:
            return lines, []
        target = sum(len(line) for line in lines) / 2
        left, right, seen = [], [], 0
        for line in lines:
            if seen < target or not left:
                left.append(line)
                seen += len(line)
            else:
                right.append(line)
        return left, right

    class CompanionScene(Scene):
        def construct(self) -> None:  # pragma: no cover - exercised through render()
            frame_w, frame_h = config.frame_width, config.frame_height
            margin_x = 0.58
            top = frame_h / 2 - 0.42
            bottom = -frame_h / 2 + 0.36
            left_edge = -frame_w / 2 + margin_x
            right_edge = frame_w / 2 - margin_x

            background = Rectangle(width=frame_w, height=frame_h, stroke_width=0,
                                   fill_color=bg, fill_opacity=1.0)
            self.add(background)

            eyebrow_text = slide.get('eyebrow') or deck['title']
            eyebrow = Text(eyebrow_text.upper(), font='DejaVu Sans', font_size=20,
                           color=wanted)
            eyebrow.move_to([left_edge, top, 0], aligned_edge=UL)
            self.add(eyebrow)

            number = Text(f'{index + 1} / {count}', font='DejaVu Sans',
                          font_size=20, color=muted)
            number.move_to([right_edge, top + 0.02, 0], aligned_edge=UR)
            self.add(number)

            title = Text(slide['title'], font='DejaVu Serif', font_size=34, color=fg,
                         line_spacing=0.9)
            if title.width > frame_w - 2 * margin_x:
                title.scale_to_fit_width(frame_w - 2 * margin_x)
            title.move_to([left_edge, eyebrow.get_bottom()[1] - 0.18, 0], aligned_edge=UL)
            self.add(title)

            lead = _text_block(
                slide['lead'],
                frame_w - 2 * margin_x,
                font_size=23,
                color='#BFD6E3',
                line_spacing=0.84,
                width_chars=80,
            )
            lead.move_to([left_edge, title.get_bottom()[1] - 0.20, 0], aligned_edge=UL)
            self.add(lead)
            cursor_y = lead.get_bottom()[1] - 0.18

            math_block = None
            if slide.get('mathtex'):
                expr = MathTex(slide['mathtex'], font_size=34, color=fg, tex_template=TEMPLATE)
                if expr.width > frame_w - 2 * margin_x - 0.7:
                    expr.scale_to_fit_width(frame_w - 2 * margin_x - 0.7)
                if expr.height > 1.65:
                    expr.scale_to_fit_height(1.65)
                shell = RoundedRectangle(
                    corner_radius=0.12,
                    width=expr.width + 0.48,
                    height=expr.height + 0.36,
                    stroke_color=trial,
                    stroke_width=2,
                    fill_color=tint(trial),
                    fill_opacity=1.0,
                )
                math_block = VGroup(shell, expr.move_to(shell.get_center()))
                math_block.move_to([0, cursor_y, 0], aligned_edge=UP)
                self.add(math_block)
                cursor_y = math_block.get_bottom()[1] - 0.18
            elif slide.get('formula'):
                formula = _text_block(slide['formula'], frame_w - 2 * margin_x - 0.8,
                                      font_size=28, color=trial, width_chars=70,
                                      line_spacing=0.82)
                shell = SurroundingRectangle(
                    formula,
                    buff=0.22,
                    corner_radius=0.12,
                    color=trial,
                    stroke_width=2,
                    fill_color=tint(trial),
                    fill_opacity=1.0,
                )
                math_block = VGroup(shell, formula)
                math_block.move_to([0, cursor_y, 0], aligned_edge=UP)
                self.add(math_block)
                cursor_y = math_block.get_bottom()[1] - 0.18

            layout = slide.get('layout') or ('figure' if slide.get('diagram') else 'reading')
            has_diagram = bool(slide.get('diagram'))
            content_top = cursor_y
            content_bottom = bottom + (0.70 if slide.get('takeaway') else 0.0)
            content_height = max(1.0, content_top - content_bottom)

            if has_diagram:
                text_width = 6.2 if layout != 'opening' else 5.9
                figure_width = frame_w - 2 * margin_x - text_width - 0.6
                beats = slide.get('body', []) + [f'• {b}' for b in slide.get('bullets', [])]
                if not beats:
                    beats = _reading_beats()
                text_group = _paragraphs(
                    beats,
                    text_width,
                    font_size=24 if layout == 'opening' else 23,
                    width_chars=40 if layout == 'opening' else 43,
                    buff=0.18,
                )
                if text_group.height > content_height:
                    text_group.scale_to_fit_height(content_height)
                text_group.move_to([left_edge, content_top, 0], aligned_edge=UL)
                self.add(text_group)

                figure = SVGMobject(str(_materialize_diagram(slide['diagram'])))
                figure.scale_to_fit_width(figure_width)
                if figure.height > content_height:
                    figure.scale_to_fit_height(content_height)
                figure_card = SurroundingRectangle(
                    figure,
                    buff=0.14,
                    corner_radius=0.12,
                    color=faint,
                    stroke_width=1.5,
                    fill_color=panel,
                    fill_opacity=1.0,
                )
                figure_group = VGroup(figure_card, figure)
                figure_group.move_to([right_edge, content_top, 0], aligned_edge=UR)
                self.add(figure_group)
            else:
                beats = _reading_beats()
                left_lines, right_lines = _split_columns(beats)
                if right_lines:
                    col_width = (frame_w - 2 * margin_x - 0.55) / 2
                    left = _paragraphs(left_lines, col_width, font_size=23, width_chars=42)
                    right = _paragraphs(right_lines, col_width, font_size=23, width_chars=42)
                    columns = VGroup(left, right).arrange(RIGHT, aligned_edge=UP, buff=0.55)
                else:
                    columns = _paragraphs(left_lines, frame_w - 2 * margin_x, font_size=23, width_chars=84)
                if columns.height > content_height:
                    columns.scale_to_fit_height(content_height)
                columns.move_to([left_edge, content_top, 0], aligned_edge=UL)
                self.add(columns)

            if slide.get('takeaway'):
                takeaway = _text_block(
                    f'Key point. {slide["takeaway"]}',
                    frame_w - 2 * margin_x - 0.35,
                    font_size=21,
                    color='#E7D3A8',
                    width_chars=95,
                    line_spacing=0.80,
                )
                box = SurroundingRectangle(
                    takeaway,
                    buff=0.18,
                    corner_radius=0.10,
                    color=sine,
                    stroke_width=1.6,
                    fill_color=tint(sine),
                    fill_opacity=1.0,
                )
                takeaway_group = VGroup(box, takeaway)
                takeaway_group.move_to([left_edge, bottom + 0.08, 0], aligned_edge=LEFT + DOWN)
                self.add(takeaway_group)

            footer = Text(deck['title'], font='DejaVu Sans', font_size=18, color=muted)
            footer.move_to([left_edge, bottom, 0], aligned_edge=LEFT + DOWN)
            self.add(footer)

    import tempfile

    with tempfile.TemporaryDirectory(prefix='dkps-companion-manim-') as tmp:
        media_dir = Path(tmp) / 'media'
        with tempconfig({
            'media_dir': str(media_dir),
            'output_file': f'{deck["id"]}-{index + 1:02d}',
            'write_to_movie': False,
            'save_last_frame': True,
            'disable_caching': True,
            'format': 'png',
            'pixel_width': 1920,
            'pixel_height': 1080,
            'frame_rate': 1,
            'background_color': bg,
        }):
            scene = CompanionScene()
            scene.render()
            image_path = getattr(scene.renderer.file_writer, 'image_file_path', None)
            if image_path and Path(image_path).is_file():
                return Path(image_path).read_bytes()
            matches = sorted(media_dir.rglob('*.png'))
            if matches:
                return matches[-1].read_bytes()
    raise RuntimeError(f'Unable to locate rendered PNG for {deck["id"]}:{slide.get("id", index)}')
