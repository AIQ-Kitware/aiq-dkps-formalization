# Experimental root parking policy

The historical `DavisKahan.Experimental` aggregate intentionally retains every
candidate route. It is therefore not the authoritative count of active proof
debt. `dev/experimental-root-status.json` classifies the currently known root
failures as active or parked, and `scripts/check_experimental_root_status.py`
validates that classification.

Parking preserves source files, declaration signatures, imports, and proof-plan
archaeology. It does not assert compilation and does not promote a module.
Reactivation requires an explicit architectural decision and a registry change.

The ambient PVM, contour, Riesz-projection, and incomplete-RCLike functional
calculus routes are parked because pinned Mathlib does not supply their required
substrate. The finite graph and tan-two-theta files are parked because their
historical bodies mix incompatible operator spaces. The finite planar Sharpness
root remains active.
