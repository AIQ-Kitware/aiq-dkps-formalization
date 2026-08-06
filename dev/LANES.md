# Lane system — retired

The multi-agent lane system was retired on 2026-08-02. One agent now works this
repository on `main`, so lane claims, the nine-step lane loop, the branch
protocol, and the live board are no longer part of the workflow.

Follow [`AGENTS.md`](../AGENTS.md) for current repository policy. In particular:

- do not claim or add lane rows;
- do not use `scripts/lane.py` to choose or coordinate work;
- report progress in terms of proved mathematics and compiling declarations;
- preserve a green build while making dependency-ordered changes on `main`.

The retired board remains available in Git history. Completed lane records and
their proof-engineering notes remain in
[`LANES-COMPLETED.md`](LANES-COMPLETED.md) as historical evidence, not active
instructions.

If parallel development resumes, the human maintainer must establish a new
coordination policy explicitly. Do not reactivate the retired process from Git
history or from planning documents that still refer to it.
