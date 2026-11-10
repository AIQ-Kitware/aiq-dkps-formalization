"""Regression tests for the mathematics-first G2 lecture additions."""
from __future__ import annotations

import cmath
import math

from dkvis.presentation.audio_library import SOURCE_DIRECTORY, narration_extractor
from dkvis.presentation.course_graph import build_course_graph

MATH_IDS = {'091250', '091500', '092250', '099500'}


def test_mathematics_lectures_are_spoken_self_contained():
    matched = [p for p in SOURCE_DIRECTORY.glob('[0-9]*-*.md') if p.name[:6] in MATH_IDS]
    assert {p.name[:6] for p in matched} == MATH_IDS
    for p in matched:
        raw = p.read_text(encoding='utf8')
        assert raw.count('<!-- BEGIN SPOKEN LECTURE -->') == 1
        assert raw.count('<!-- END SPOKEN LECTURE -->') == 1
        spoken = narration_extractor(p)
        assert len(spoken.split()) >= 850
        lower = spoken.lower()
        for forbidden in ('tau ceti', 'tauceti', 'lean 4', 'proof assistant',
                          'the previous lecture', 'in the next lecture',
                          'in an earlier lecture', 'our formalization'):
            assert forbidden not in lower, (p, forbidden)
        assert '\\' not in spoken  # Raw LaTeX belongs in the display-only appendix.
        assert '```' not in spoken


def test_mathematics_lectures_are_catalogued_in_dependency_order():
    graph = build_course_graph()
    g2_path = next(t['path'] for t in graph['tracks'] if t['id'] == 'g2')
    assert len(g2_path) >= 154
    assert g2_path.index('g2:091000') < g2_path.index('g2:091250')
    assert g2_path.index('g2:091250') < g2_path.index('g2:091500')
    assert g2_path.index('g2:091500') < g2_path.index('g2:092000')
    assert g2_path.index('g2:092000') < g2_path.index('g2:092250')
    assert g2_path.index('g2:099000') < g2_path.index('g2:099500') < g2_path.index('g2:100000')
    assert graph['nodes']['g2:099500']['topic'] == 'operator-ideals'
    assert graph['nodes']['g2:091250']['topic'] == 'unbounded'
    deps = {(e['from'], e['to']) for e in graph['edges'] if e['type'] == 'hard_depends_on'}
    assert ('g2:092250', 'g2:091250') in deps
    assert ('g2:099500', 'g2:099000') in deps


def test_yosida_resolvent_example_matches_both_formulas():
    for radius in (1.0, 2.0, 10.0):
        for spectral_value in (-8.0, -1.0, 0.0, 3.0, 20.0):
            rational = radius**2 * spectral_value / (radius**2 + spectral_value**2)
            resolvent = radius**2 / 2 * (
                1/(spectral_value-1j*radius) + 1/(spectral_value+1j*radius))
            assert abs(rational-resolvent) < 1e-12
            assert abs(rational) <= radius/2 + 1e-12
    for lam in (1.0, 5.0, 30.0):
        for n in (1, 2, 10, 200):
            regularized = -lam*n/(lam+n)
            assert -lam <= regularized <= 0
            assert abs(math.exp(regularized*0.3)) <= 1


def test_strong_resolvent_counterexamples_are_numerically_consistent():
    # For fixed radius, high diagonal eigenvalues see f_R(n) ~ 0,
    # whereas the original n-th eigenvalue tends to infinity.
    radius = 5.0
    n = 10**7
    reg = radius**2*n/(radius**2+n**2)
    resolvent_difference = abs(1/(reg-1j) - 1/(n-1j))
    assert resolvent_difference > 0.999
    # A_n = 1/n I, A = 0: norm-resolvent convergence but sharp
    # projection onto (-infinity,0] jumps from 0 to 1.
    assert abs(1/(1/10000-1j) - 1/(0-1j)) < 0.001
    assert int(1/10000 <= 0) == 0
    assert int(0 <= 0) == 1


def test_charbonnier_bounds_and_ideal_distinction():
    tau = 0.6
    M = 3.0
    for s in (0.0, 0.001, 0.3, 1.0, M):
        penalty = math.hypot(tau,s) - tau
        assert s*s/(math.hypot(tau,M)+tau) <= penalty + 1e-12
        assert penalty <= s*s/(2*tau) + 1e-12
    # The diagonal (1/n) has square-summable but not summable singular values.
    nmax=5000
    square_sum=sum(1/n**2 for n in range(1,nmax+1))
    linear_sum=sum(1/n for n in range(1,nmax+1))
    penalty_sum=sum(math.hypot(tau,1/n)-tau for n in range(1,nmax+1))
    assert square_sum < 2.0
    assert linear_sum > 9.0
    assert 0 < penalty_sum <= square_sum/(2*tau) + 1e-10
