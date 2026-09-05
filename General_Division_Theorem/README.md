# General Divisor Theorem

This directory provides a Lean formalization benchmark for the
General Divisor Theorem and a complete machine-checked solution.

## Source

https://goodmath.app/divisor.pdf

## Objective

Translate the theorem's exact hypotheses, admissibility split,
minimal period, count, density, and correction factor into Lean and
produce a machine-checkable certificate.

## Benchmark

The benchmark separates the theorem statements from their completed
proofs.

- `Challenge/GeneralDivisionTheorem.lean`
  contains seven theorem proof holes expressed with `sorry`.

- `Solution/GeneralDivisionTheorem.lean`
  contains complete proofs of the seven theorem statements with no
  `sorry`.

The benchmark includes:

1. the empty case for inadmissible residue classes;
2. periodicity with period `Tmin = mR`;
3. exact minimality of `Tmin`;
4. the exact count `φ(R)` per period;
5. the exact density decomposition;
6. the correction-factor identity; and
7. the packaged General Divisor Theorem.

## Verification

The challenge file compiles with the seven expected `sorry` warnings:

```bash
lake env lean Challenge/GeneralDivisionTheorem.lean
```

The completed solution compiles with no `sorry`:

```bash
lake env lean Solution/GeneralDivisionTheorem.lean
```

The complete project also builds successfully:

```bash
lake build
```

A successful build verifies the General Divisor Theorem solution
against Lean and Mathlib.
