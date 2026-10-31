# Verification instructions

This is a Lean proof artifact, not an application. Read README.md first.

- The complete check is `python verify.py`, from the repository root.
- Preserve the pinned Lean toolchain and dependency lockfile.
- Do not add axioms, `sorry`, `admit`, or weaken statements to obtain a pass.
- Report whether Lean actually ran. `--recorded-only` validates archived
  evidence and must never be reported as a fresh Lean build.
- `--resume` checks source and object hashes; disclose its use.
- New reports are in `.lake/verification/`; inspect the final status and
  failing logs. A missing toolchain or interrupted run is not a successful check.
- Use PaperIndex.lean and docs/correspondence.md to find paper results.
- Distinguish Lean's kernel check from mathematical review of the paper
  correspondence and from the seven declared external mathematical inputs.
- This repository is private. Do not change visibility or publish its contents.
