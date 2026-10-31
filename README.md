# Paying for Fractional Error — Lean verification

Formalization of **Paying for Fractional Error: Tight Constant-Round
Approximation of Covering Problems with Short Broadcasts**.

## Verify

Requires Git, Python 3.10+ and [Elan](https://github.com/leanprover/elan#installation).
Lean 4.29.0 and Mathlib are pinned.

```sh
git clone https://github.com/wwawrzy/paying-for-fractional-error-lean.git
cd paying-for-fractional-error-lean
python verify.py
```

Use `python3` if needed. This compiles 1612 library modules and supplementary
checks, audits axioms, and checks the mapping to 81 paper statements.
Results: `.lake/verification/`. Failures return a nonzero exit code.

Default: two workers, 6 GiB limit each. Use `--jobs 1` for less memory or
`--jobs 9` on a 64 GiB machine. Use `--resume` after an interruption.

## Paper correspondence

- [PaperIndex.lean](PaperIndex.lean): paper results and Lean declarations.
- [Statement map](docs/correspondence.md): all 81 statements.
- [Verification and axioms](docs/verification.md): scope and assumptions.
- [AGENTS.md](AGENTS.md): instructions for AI reviewers.

Archived evidence covers 73 statements with standard Lean axioms and eight
with additional assumptions. `python verify.py --recorded-only` checks that
evidence without running Lean. A new full rebuild of this export remains
incomplete. Comment-only edits since the archived build are recorded separately.

## License and citation

The Lean code and verification scripts are licensed under [Apache 2.0](LICENSE).
Existing third-party notices remain applicable.

If you use this formalization, please cite the accompanying paper using
the metadata in [CITATION.cff](CITATION.cff).
