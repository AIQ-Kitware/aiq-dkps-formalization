"""Matrix identities illustrated by the matching study scenes."""
import math
import numpy as np
import pytest

from dkvis.matching_math import (
    displacement_power, pair_direct_rotation, pair_parameters, pair_transporter,
    paired_power_cost, phase_cost, phase_derivative, phase_level_roots,
    phase_rectangle_edge, rotation, skew_gradient,
)


def test_pair_attainers_transport_the_actual_source_and_have_the_stated_power_cost():
    source = np.diag([1., 1., 0., 0.])
    for degrees in [(0, 0), (0, 75), (30, 45), (80, 65), (90, 90)]:
        theta, psi = np.radians(degrees)
        h, d = pair_parameters(theta, psi)
        direct = pair_direct_rotation(theta, psi)
        target = direct @ source @ direct.T
        for tau in [d, (d+h)/2, h]:
            w = pair_transporter(theta, psi, tau)
            assert np.allclose(w.T @ w, np.eye(4), atol=1e-12)
            assert np.allclose(w @ source @ w.T, target, atol=1e-12)
            for p in [1., 1.5, 1.9]:
                assert displacement_power(w, p) == pytest.approx(
                    float(paired_power_cost(theta, psi, tau, p)), abs=1e-12)
        assert displacement_power(pair_transporter(theta, psi, h), 1) == pytest.approx(4*math.sin(h))


def test_skew_gradient_matches_general_mixing_directions():
    rng = np.random.default_rng(4)
    w = np.zeros((6, 6))
    w[:2,:2], w[2:4,2:4] = rotation(.7), rotation(2.)
    w[4,4], w[5,5] = 1., -1.
    # Exact planar derivative, with scalar +/-1 blocks contributing zero.
    g = skew_gradient(w, 1.5)
    assert np.allclose(g[:2,:2], phase_derivative(.7, 1.5)*rotation(math.pi/2), atol=1e-12)
    for _ in range(10):
        raw = rng.normal(size=(6,6))
        b = raw - raw.T
        eps = 1e-6
        # iB is Hermitian; its eigendecomposition gives exp(tB) using NumPy.
        values, basis = np.linalg.eigh(1j*b)
        forward = ((basis*np.exp(-1j*eps*values)) @ basis.conj().T).real
        backward = ((basis*np.exp(1j*eps*values)) @ basis.conj().T).real
        derivative = (displacement_power(w @ forward, 1.5)
                      - displacement_power(w @ backward, 1.5))/(2*eps)
        assert derivative == pytest.approx(-np.trace(g @ b), abs=2e-6)


def test_edge_reduction_decreases_both_folded_phases():
    rng = np.random.default_rng(9)
    for _ in range(100):
        theta, psi = rng.uniform(0, math.pi/2, 2)
        h, d = pair_parameters(theta, psi)
        x, y = rng.uniform(h, math.pi-h), rng.uniform(d, math.pi-d)
        x, y, tau = phase_rectangle_edge(x, y, h, d)
        assert d-1e-12 <= tau <= h+1e-12
        assert h+tau <= x+y+1e-12
        assert h-tau <= abs(x-y)+1e-12
        old = 2*(phase_cost(x+y, 1.5)+phase_cost(abs(x-y),1.5))
        assert float(paired_power_cost(theta,psi,tau,1.5)) <= old+1e-12


def test_positive_gradient_level_has_one_root_on_each_monotone_side():
    p, level = 1.5, .8
    a,b = phase_level_roots(p,level)
    critical = 2*math.atan(math.sqrt(p-1))
    assert 0 < a < critical < b < math.pi
    assert phase_derivative(a,p) == pytest.approx(level)
    assert phase_derivative(b,p) == pytest.approx(level)
    assert len(phase_level_roots(p,float(phase_derivative(critical,p)))) == 1
