# Coordination and standalone repositories

Repositories under this directory are **not DKPS build dependencies**. A normal clone
with no submodules initialized must still support the ordinary DKPS build. Do not add
a Lake `path` dependency, default-build input, or required checker input that points
through a gitlink here.

The repositories have two roles.

## Standalone delivery repositories

The Davis--Kahan and Yu--Wang--Samworth standalone repositories own their own
submission artifacts: Challenge/Solution modules, metadata, comparator configuration,
readiness scripts, and submission-specific planning.

DKPS remains authoritative for the mathematics. The workflow is:

1. make every mathematical, proof, source-fidelity, and public-API improvement in
   DKPS;
2. build and audit DKPS;
3. mechanically refresh the relevant standalone repository from that committed state;
4. make only packaging/statement-adapter/submission changes in the standalone repo;
5. if standalone work discovers a mathematical or API defect, return to DKPS and fix
   it there before refreshing again.

Do not maintain a second copy of the production theorem design in a standalone repo,
and do not recreate standalone Challenge/Solution or submission metadata in DKPS.
Submission scope and submission-policy details belong in the standalone repository.

## Coordination/reference repositories

Tau Ceti roadmap/review and related tooling repositories are external review or
coordination surfaces. Some optional tools can inspect them when present, but absence
must not break the ordinary build. Use the explicit path/environment-variable
interfaces documented in `external/README.md` and the relevant script.
