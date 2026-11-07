# Source and scope

Two real-valued costs on the same nonempty set; minimizers are supplied as
hypotheses. The two closing Lean examples are direct applications of Mathlib
order transitivity and subtraction monotonicity. They state the upper and lower
comparison separately. Together with a uniform band, they prove value control.
They make no assertion of convergence of minimizing points.

Counterexample: on [0,1], for integer n≥2,
f_n(x)=-max(0,1-3n|x-1/n|). The dip has support within
[2/(3n),4/(3n)], minimum -1 at 1/n, and pointwise limit zero. Each f_n is
continuous and attains a minimum. The animation interpolates n for movement;
the sequence argument uses integer n.

The second example g_n(x)=(-1)^n x/n converges uniformly to zero but has
alternating unique minimizing endpoints. These examples separate value and
location convergence. Numerical tests support the formulas used in the
pictures; the displayed comparison argument proves the all-candidate claim.
