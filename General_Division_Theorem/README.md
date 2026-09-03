# General Divisor Theorem

This directory tests whether the Lean verification workflow used in
ZetaZeros can be applied to the General Divisor Theorem.

## Source

https://goodmath.app/divisor.pdf

## Objective

Translate the theorem's exact hypotheses, admissibility split,
minimal period, count, and density into Lean and produce a
machine-checkable certificate.

## Workflow

1. Specify the theorem in Lean.
2. Confirm the required definitions are available in Mathlib.
3. Separate the empty and admissible cases.
4. Prove the periodicity and exact count.
5. Verify the complete theorem with Lean.
