/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Source: thinkthoughts, "The General Divisor Theorem: Exact Density Correction under
Residue Conditioning", Draft v3.3, Theorem 3 (§2.2).
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Finset.Basic

/-! # The General Divisor Theorem (Theorem 3)

Exact density correction for integers in a fixed residue class mod `m` that are also
coprime to `N`. Source: thinkthoughts, Draft v3.3, Theorem 3 (§2.2). -/

@[expose] public section

namespace GDT

/-- The radical of `n`: the product of the distinct primes dividing `n`. `rad 1 = 1`. -/
def rad (n : ℕ) : ℕ := n.primeFactors.prod id

/-- `d = rad(gcd(m, N))`: the radical of the primes shared between `m` and `N`. -/
def d (N m : ℕ) : ℕ := rad (Nat.gcd m N)

/-- `R = rad(N) / d`. -/
def R (N m : ℕ) : ℕ := rad N / d N m

/-- The claimed exact minimal period `Tmin = mR`. -/
def Tmin (N m : ℕ) : ℕ := m * R N m

/-- `a` is admissible for `(N, m)` exactly when `gcd(a, d) = 1`, via `a.natAbs` so the
condition is stated without depending on `Int.gcd`'s exact signature. -/
def Admissible (N m : ℕ) (a : ℤ) : Prop :=
  Nat.gcd a.natAbs (d N m) = 1

/-- The acceptance indicator: `n ≡ a (mod m)` and `n` coprime to `N`. -/
def accepted (N m : ℕ) (a : ℤ) (n : ℕ) : Prop :=
  (n : ℤ) ≡ a [ZMOD (m : ℤ)] ∧ Nat.gcd n N = 1

instance acceptedDecidable (N m : ℕ) (a : ℤ) :
    DecidablePred (accepted N m a) := by
  intro n
  unfold accepted
  infer_instance

/-- `S(N, L, m, a) = {1 ≤ n ≤ L : n ≡ a (mod m), gcd(n, N) = 1}`. -/
def S (N L m : ℕ) (a : ℤ) : Finset ℕ :=
  (Finset.Icc 1 L).filter (accepted N m a)

/-- `t` is a period of the acceptance indicator. -/
def IsPeriod (N m : ℕ) (a : ℤ) (t : ℕ) : Prop :=
  ∀ n : ℕ, accepted N m a (n + t) ↔ accepted N m a n

end GDT

namespace GDT.Challenge

open GDT

/-- **`gdt_empty`.** For positive `N, m`: if `gcd(a, d) > 1`, the accepted set is empty
for every `L`. -/
theorem gdt_empty {N m L : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : ¬ Admissible N m a) :
    S N L m a = ∅ :=
  sorry

/-- **`gdt_periodic`.** For positive `N, m` and admissible `a`, `Tmin = mR` is a period. -/
theorem gdt_periodic {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) :
    IsPeriod N m a (Tmin N m) :=
  sorry

/-- **`gdt_minimal_period`.** For positive `N, m` and admissible `a`, every positive period
is a multiple of `Tmin` — in particular `Tmin` is the exact minimal period. -/
theorem gdt_minimal_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) {t : ℕ} (ht : 0 < t) (hp : IsPeriod N m a t) :
    Tmin N m ∣ t :=
  sorry

/-- **`gdt_count_per_period`.** For positive `N, m` and admissible `a`, every run of
`Tmin` consecutive integers starting at `b` — i.e. `Ico b (b + Tmin)` — contains exactly
`φ(R)` accepted values, for any `b`. -/
theorem gdt_count_per_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) (b : ℕ) :
    ((Finset.Ico b (b + Tmin N m)).filter (accepted N m a)).card =
      Nat.totient (R N m) :=
  sorry

/-- **`gdt_density`.** Writing `L = q·Tmin + s`, §3.4's `R(s)` is literally
`{1 ≤ n ≤ s : ...}` — the same interval-from-`1` convention as `S` itself — so the exact
count is `q` full periods at `φ(R)` each plus `(S N s m a).card` verbatim, not a
reindexed or shifted form of it. -/
theorem gdt_density {N m q s : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) (hs : s < Tmin N m) :
    (S N (q * Tmin N m + s) m a).card =
      q * Nat.totient (R N m) + (S N s m a).card :=
  sorry

/-- **`gdt_correction_factor`.** `C(N,m) = d/φ(d)`, stated division-free:
`φ(R)·N·φ(d) = d·R·φ(N)`. Holds for every positive `N, m` — the paper's "Ratio" step
never uses admissibility of `a`. -/
theorem gdt_correction_factor {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    Nat.totient (R N m) * N * Nat.totient (d N m) =
      d N m * R N m * Nat.totient N :=
  sorry

/-- **`general_divisor_theorem`.** Theorem 3 packaged in full, for positive `N, m`. -/
theorem general_divisor_theorem {N m L : ℕ} (hN : 0 < N) (hm : 0 < m) (a : ℤ) :
    (¬ Admissible N m a → S N L m a = ∅) ∧
    (Admissible N m a →
      IsPeriod N m a (Tmin N m) ∧
      (∀ t : ℕ, 0 < t → IsPeriod N m a t → Tmin N m ∣ t) ∧
      (∀ b : ℕ,
        ((Finset.Ico b (b + Tmin N m)).filter (accepted N m a)).card =
          Nat.totient (R N m))) ∧
    Nat.totient (R N m) * N * Nat.totient (d N m) =
      d N m * R N m * Nat.totient N :=
  sorry

end GDT.Challenge
