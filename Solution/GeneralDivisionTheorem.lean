module

public import ZetaZeros.GDT

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
    unfold d rad at hpd
    obtain ⟨i, hi_mem, hpi⟩ := (hp.prime.dvd_finset_prod_iff id).mp hpd
    have hi_prime : i.Prime := Nat.prime_of_mem_primeFactors hi_mem
    have hpi_eq : p = i := (Nat.prime_dvd_prime_iff_eq hp hi_prime).mp hpi
    rwa [hpi_eq]
  have hp_gcd : p ∣ Nat.gcd m N := Nat.dvd_of_mem_primeFactors hp_mem
  have hpm : p ∣ m := hp_gcd.trans (Nat.gcd_dvd_left _ _)
  have hpN : p ∣ N := hp_gcd.trans (Nat.gcd_dvd_right _ _)
  have hpa' : (p : ℤ) ∣ a := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpa)
  apply Finset.eq_empty_iff_forall_not_mem.mpr
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
