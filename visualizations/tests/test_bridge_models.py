"""The numerical pictures satisfy the claims they illustrate."""
import numpy as np
from dkvis.learning.uniform_minima.model import band_cost, moving_dip


def test_one_tolerance_contains_the_entire_displayed_cost():
    x=np.linspace(-2,2,2001)
    for tolerance in [.8,.3,.1,0.]:
        error=np.abs(band_cost(x,tolerance)-x*x)
        assert np.max(error)<=tolerance+1e-14


def test_dip_minimum_moves_without_losing_depth():
    for n in [2,5,20,100]:
        assert moving_dip(1/n,n)==-1
        assert moving_dip(0,n)==0
        assert moving_dip(2/n,n)==0
    # Every chosen positive location eventually misses the support entirely.
    for x in [.01,.2,.7,1.]:
        n=int(np.ceil(2/x))
        assert moving_dip(x,n)==0
