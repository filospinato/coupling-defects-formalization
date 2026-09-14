# Coupling defects

Lean formalization and finite certificate accompanying
*Coupling defects of large-prime fibres in optimal path partitions of the divisor
graph* by Filippo Cavallari.

The [paper-to-Lean audit](formalization/PAPER_LEAN_AUDIT.md) records the formalized
statements and external assumptions.

## Lean

With [Lean installed](https://leanprover-community.github.io/get_started.html),
run from the repository root:

```bash
cd formalization
lake exe cache get
lake build
```

## Finite certificate

With Python 3.10 or later, run from the repository root:

```bash
python3 ancillary/verify_certificate.py
```

## License

Copyright (c) Filippo Cavallari. Licensed under [Apache-2.0](LICENSE).
The license covers this supplement; the paper and third-party dependencies are
excluded.
