"""Behavioral tests for presentation helpers, never assertions about slide copy.

Slide wording, captions, counts, and layout are iterated by reviewing the
rendered presentation. Tests here cover helper behavior and asset integrity.
"""

import ast
from pathlib import Path
import xml.etree.ElementTree as ET


ROOT = Path(__file__).resolve().parents[1]


def test_robot_icon_is_valid_svg():
    svg_path = ROOT / 'dkvis/assets/robot.svg'
    assert ET.parse(svg_path).getroot().tag == '{http://www.w3.org/2000/svg}svg'


def test_lean_header_extractor_reads_a_declaration_and_optional_witness(tmp_path):
    """The source reader extracts a header without leaking adjacent proofs."""
    # The helper is isolated from optional Manim dependencies for this test.
    source = (ROOT / 'dkvis/slides_prop44.py').read_text()
    tree = ast.parse(source)
    func = next(
        node for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == '_lean_statement'
    )
    namespace = {'Path': Path}
    exec(compile(ast.Module(body=[func], type_ignores=[]), '<lean-excerpt>', 'exec'), namespace)
    read = namespace['_lean_statement']

    lean_file = tmp_path / 'example.lean'
    lean_file.write_text(
        'theorem first :\n'
        '    True := by\n'
        '  trivial\n'
        '\n'
        'theorem witness :\n'
        '    True :=\n'
        '  trivial\n'
        '\n'
        'theorem after :\n'
        '    True := by\n'
        '  trivial\n'
    )
    assert read(lean_file, 'first') == ['theorem first :', '    True := by']
    assert read(lean_file, 'witness', include_witness=True) == [
        'theorem witness :', '    True :=', '  trivial',
    ]
