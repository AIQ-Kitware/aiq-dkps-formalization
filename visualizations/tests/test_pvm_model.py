"""The displayed finite example obeys projection, mass and integration identities."""
import numpy as np
from dkvis.learning.pvm.model import EIGENVALUES,eigenbasis,projection,spectral_function,atom_masses,example_vector


def test_spectral_window_selects_a_whole_repeated_eigenspace():
    p=projection(1.5,2.5)
    np.testing.assert_allclose(p@p,p,atol=1e-14)
    np.testing.assert_allclose(p.T,p)
    assert np.linalg.matrix_rank(p)==2
    q=eigenbasis()
    np.testing.assert_allclose(p@q[:,1:3],q[:,1:3],atol=1e-14)
    np.testing.assert_allclose(p@q[:,[0,3]],0,atol=1e-14)


def test_set_operations_and_spectral_integration():
    p=projection(1,2);q=projection(2,4)
    np.testing.assert_allclose(p@q,projection(2,2),atol=1e-14)
    identity=projection(-np.inf,np.inf)
    np.testing.assert_allclose(identity-p,projection(3,5),atol=1e-14)
    np.testing.assert_allclose(projection(1,1)+projection(2,2),p,atol=1e-14)
    a=spectral_function(EIGENVALUES)
    np.testing.assert_allclose(spectral_function(EIGENVALUES**2),a@a,atol=1e-14)


def test_scalar_measure_is_energy_not_rank():
    x=example_vector();p=projection(1.5,2.5)
    np.testing.assert_allclose(atom_masses(x),[.25,.5,.25],atol=1e-14)
    assert np.isclose(np.linalg.norm(p@x)**2,.5)
    z=np.array([1+2j,2-1j,0,3j])
    assert np.isclose(sum(atom_masses(z)),np.linalg.norm(z)**2)
