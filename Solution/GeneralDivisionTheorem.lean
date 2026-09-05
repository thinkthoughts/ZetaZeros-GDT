module

public import ZetaZeros.GDT
public import Mathlib.Data.Nat.Squarefree

@[expose] public section

namespace GDT.Challenge

open GDT

theorem gdt_empty {N m L : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : ¬ Admissible N m a) :
    S N L m a = ∅ := by
  have h' : Nat.gcd a.natAbs (d N m) ≠ 1 := h
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h'
  have hpa : p ∣ a.natAbs := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpd : p ∣ d N m := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hp_mem : p ∈ (Nat.gcd m N).primeFactors := by
    have hgcd_ne : Nat.gcd m N ≠ 0 := (Nat.gcd_pos_of_pos_left N hm).ne'
    have hrad_dvd : rad (Nat.gcd m N) ∣ Nat.gcd m N :=
      Nat.prod_primeFactors_dvd (Nat.gcd m N)
    unfold d at hpd
    exact Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hrad_dvd, hgcd_ne⟩
  have hp_gcd : p ∣ Nat.gcd m N := Nat.dvd_of_mem_primeFactors hp_mem
  have hpm : p ∣ m := hp_gcd.trans (Nat.gcd_dvd_left _ _)
  have hpN : p ∣ N := hp_gcd.trans (Nat.gcd_dvd_right _ _)
  have hpa' : (p : ℤ) ∣ a := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpa)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  simp only [S, Finset.mem_filter, accepted] at hn
  obtain ⟨-, hmod, hcop⟩ := hn
  have hmodp : (n : ℤ) ≡ a [ZMOD (p : ℤ)] :=
    Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hpm) hmod
  have ha0 : a ≡ 0 [ZMOD (p : ℤ)] := Int.modEq_zero_iff_dvd.mpr hpa'
  have hn0 : (n : ℤ) ≡ 0 [ZMOD (p : ℤ)] := hmodp.trans ha0
  have hpn : (p : ℤ) ∣ (n : ℤ) := Int.modEq_zero_iff_dvd.mp hn0
  have hpn' : p ∣ n := by exact_mod_cast hpn
  have hp_dvd_one : p ∣ 1 := hcop ▸ Nat.dvd_gcd hpn' hpN
  exact absurd (Nat.le_of_dvd one_pos hp_dvd_one) (not_le.mpr hp.one_lt)

/-- `d N m` divides `rad N`. -/
lemma d_dvd_rad {N m : ℕ} (hN : 0 < N) : d N m ∣ rad N := by
  unfold d rad
  have hdvd : Nat.gcd m N ∣ N := Nat.gcd_dvd_right m N
  have hsub : (Nat.gcd m N).primeFactors ⊆ N.primeFactors :=
    Nat.primeFactors_mono hdvd hN.ne'
  exact Finset.prod_dvd_prod_of_subset _ _ id hsub

/-- `d N m * R N m = rad N`. -/
lemma d_mul_R_eq_rad {N m : ℕ} (hN : 0 < N) : d N m * R N m = rad N := by
  unfold R
  exact Nat.mul_div_cancel' (d_dvd_rad hN)

lemma prime_coprime_prod {a : ℕ} (ha : a.Prime) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (ha_not : a ∉ s) :
    Nat.Coprime a (∏ p ∈ s, p) := by
  revert hs ha_not
  induction s using Finset.induction with
  | empty =>
      intro hs ha_not
      simp
  | @insert b t hb ih =>
      intro hs ha_not
      rw [Finset.prod_insert hb]
      have hbprime : b.Prime :=
        hs b (Finset.mem_insert_self b t)
      have habne : a ≠ b := by
        intro hab
        subst b
        exact ha_not (Finset.mem_insert_self a t)
      have hab : Nat.Coprime a b :=
        (Nat.coprime_primes ha hbprime).mpr habne
      have hs_t : ∀ p ∈ t, p.Prime := by
        intro p hp
        exact hs p (Finset.mem_insert_of_mem hp)
      have ha_not_t : a ∉ t := by
        intro hat
        exact ha_not (Finset.mem_insert_of_mem hat)
      exact hab.mul_right (ih hs_t ha_not_t)

lemma prod_primes_squarefree {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty =>
      simpa using Nat.squarefree_one
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hpa : a.Prime :=
        hs a (Finset.mem_insert_self a s)
      have hs' : ∀ p ∈ s, p.Prime := by
        intro p hp
        exact hs p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
        prime_coprime_prod hpa hs' ha
      exact Nat.squarefree_mul_iff.mpr
        ⟨hcop, hpa.squarefree, ih hs'⟩

lemma rad_squarefree (n : ℕ) : Squarefree (rad n) := by
  unfold rad
  exact prod_primes_squarefree
    (fun p hp => Nat.prime_of_mem_primeFactors hp)

theorem gdt_periodic {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) :
    IsPeriod N m a (Tmin N m) := by
  sorry

theorem gdt_minimal_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) {t : ℕ} (ht : 0 < t) (hp : IsPeriod N m a t) :
    Tmin N m ∣ t := by
  sorry

theorem gdt_count_per_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) (b : ℕ) :
    ((Finset.Ico b (b + Tmin N m)).filter (accepted N m a)).card =
      Nat.totient (R N m) := by
  sorry

theorem gdt_density {N m q s : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) (hs : s < Tmin N m) :
    (S N (q * Tmin N m + s) m a).card =
      q * Nat.totient (R N m) + (S N s m a).card := by
  sorry

theorem gdt_correction_factor {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    Nat.totient (R N m) * N * Nat.totient (d N m) =
      d N m * R N m * Nat.totient N := by
  sorry

theorem general_divisor_theorem {N m L : ℕ} (hN : 0 < N) (hm : 0 < m) (a : ℤ) :
    (¬ Admissible N m a → S N L m a = ∅) ∧
    (Admissible N m a →
      IsPeriod N m a (Tmin N m) ∧
      (∀ t : ℕ, 0 < t → IsPeriod N m a t → Tmin N m ∣ t) ∧
      (∀ b : ℕ,
        ((Finset.Ico b (b + Tmin N m)).filter (accepted N m a)).card =
          Nat.totient (R N m))) ∧
    Nat.totient (R N m) * N * Nat.totient (d N m) =
      d N m * R N m * Nat.totient N := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact gdt_empty hN hm h
  · intro h
    refine ⟨gdt_periodic hN hm h, ?_, ?_⟩
    · intro t ht hp
      exact gdt_minimal_period hN hm h ht hp
    · intro b
      exact gdt_count_per_period hN hm h b
  · exact gdt_correction_factor hN hm

end GDT.Challenge
