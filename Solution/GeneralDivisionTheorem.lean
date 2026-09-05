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

lemma coprime_d_R {N m : ℕ} (hN : 0 < N) :
    Nat.Coprime (d N m) (R N m) := by
  have heq : d N m * R N m = rad N := d_mul_R_eq_rad hN
  have hsf : Squarefree (d N m * R N m) := heq ▸ rad_squarefree N
  exact (Nat.squarefree_mul_iff.mp hsf).1

/-- `rad n` divides `n`. -/
lemma rad_dvd_self (n : ℕ) : rad n ∣ n := by
  unfold rad
  exact Nat.prod_primeFactors_dvd n

/-- `k` is coprime to `n` iff `k` is coprime to `rad n`. -/
lemma coprime_iff_coprime_rad {k n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime k n ↔ Nat.Coprime k (rad n) := by
  constructor
  · intro h
    by_contra hne
    have hne' : Nat.gcd k (rad n) ≠ 1 := hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne'
    have hpk : p ∣ k := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hprad : p ∣ rad n := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpn : p ∣ n := hprad.trans (rad_dvd_self n)
    have hcontra : p ∣ Nat.gcd k n := Nat.dvd_gcd hpk hpn
    have heq : Nat.gcd k n = 1 := h
    rw [heq] at hcontra
    exact absurd (Nat.le_of_dvd one_pos hcontra) (not_le.mpr hp.one_lt)
  · intro h
    by_contra hne
    have hne' : Nat.gcd k n ≠ 1 := hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne'
    have hpk : p ∣ k := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpn : p ∣ n := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hp_mem : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩
    have hprad_mem : p ∈ (rad n).primeFactors := by
      unfold rad
      change p ∈ (∏ q ∈ n.primeFactors, q).primeFactors
      rw [Nat.primeFactors_prod
        (fun q hq => Nat.prime_of_mem_primeFactors hq)]
      exact hp_mem
    have hprad : p ∣ rad n :=
      Nat.dvd_of_mem_primeFactors hprad_mem
    have hcontra : p ∣ Nat.gcd k (rad n) :=
      Nat.dvd_gcd hpk hprad
    have heq : Nat.gcd k (rad n) = 1 := h
    rw [heq] at hcontra
    exact absurd (Nat.le_of_dvd one_pos hcontra) (not_le.mpr hp.one_lt)

/-- If `k ≡ a (mod e)` and `gcd(a.natAbs, e) = 1`, then `k` is coprime to `e`. -/
lemma coprime_of_modEq_natAbs {k : ℕ} {a : ℤ} {e : ℕ}
    (hk : (k : ℤ) ≡ a [ZMOD (e : ℤ)]) (ha : Nat.gcd a.natAbs e = 1) :
    Nat.Coprime k e := by
  by_contra hne
  have hne' : Nat.gcd k e ≠ 1 := hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne'
  have hpk : p ∣ k := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpe : p ∣ e := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hpe' : (p : ℤ) ∣ (e : ℤ) := Int.natCast_dvd_natCast.mpr hpe
  have hkp : (k : ℤ) ≡ a [ZMOD (p : ℤ)] := Int.ModEq.of_dvd hpe' hk
  have hpk' : (p : ℤ) ∣ (k : ℤ) := Int.natCast_dvd_natCast.mpr hpk
  have hk0 : (k : ℤ) ≡ 0 [ZMOD (p : ℤ)] := Int.modEq_zero_iff_dvd.mpr hpk'
  have ha0 : a ≡ 0 [ZMOD (p : ℤ)] := hkp.symm.trans hk0
  have hpa_int : (p : ℤ) ∣ a := Int.modEq_zero_iff_dvd.mp ha0
  have hpa_nat : p ∣ a.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hpa_int
    simpa using h
  have hcontra : p ∣ Nat.gcd a.natAbs e := Nat.dvd_gcd hpa_nat hpe
  rw [ha] at hcontra
  exact absurd (Nat.le_of_dvd one_pos hcontra) (not_le.mpr hp.one_lt)

lemma gcd_with_N_iff_gcd_with_R
    {N m k : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (ha : Admissible N m a)
    (hk : (k : ℤ) ≡ a [ZMOD (m : ℤ)]) :
    Nat.gcd k N = 1 ↔ Nat.gcd k (R N m) = 1 := by
  have hd_dvd_m : d N m ∣ m :=
    (rad_dvd_self (Nat.gcd m N)).trans (Nat.gcd_dvd_left m N)
  have hkd : (k : ℤ) ≡ a [ZMOD (d N m : ℤ)] :=
    Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hd_dvd_m) hk
  have hcop_d : Nat.Coprime k (d N m) :=
    coprime_of_modEq_natAbs hkd ha
  have hcoN : Nat.Coprime k N ↔ Nat.Coprime k (rad N) :=
    coprime_iff_coprime_rad hN.ne'
  rw [← d_mul_R_eq_rad hN] at hcoN
  rw [Nat.coprime_mul_iff_right] at hcoN
  show Nat.Coprime k N ↔ Nat.Coprime k (R N m)
  rw [hcoN]
  exact ⟨fun h => h.2, fun h => ⟨hcop_d, h⟩⟩

/-- Adding a multiple of `e` to `k` doesn't change coprimality with `e`. -/
lemma coprime_add_mul_right {k c e : ℕ} :
    Nat.Coprime (k + e * c) e ↔ Nat.Coprime k e := by
  constructor
  · intro h
    by_contra hne
    have hne' : Nat.gcd k e ≠ 1 := hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne'
    have hpk : p ∣ k := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpe : p ∣ e := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpsum : p ∣ k + e * c := hpk.add (hpe.mul_right c)
    have hcontra : p ∣ Nat.gcd (k + e * c) e := Nat.dvd_gcd hpsum hpe
    have heq : Nat.gcd (k + e * c) e = 1 := h
    rw [heq] at hcontra
    exact absurd (Nat.le_of_dvd one_pos hcontra) (not_le.mpr hp.one_lt)
  · intro h
    by_contra hne
    have hne' : Nat.gcd (k + e * c) e ≠ 1 := hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne'
    have hpsum : p ∣ k + e * c := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpe : p ∣ e := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpec : p ∣ e * c := hpe.mul_right c
    have hpk : p ∣ k := (Nat.dvd_add_right hpec).mp (by rwa [add_comm] at hpsum)
    have hcontra : p ∣ Nat.gcd k e := Nat.dvd_gcd hpk hpe
    have heq : Nat.gcd k e = 1 := h
    rw [heq] at hcontra
    exact absurd (Nat.le_of_dvd one_pos hcontra) (not_le.mpr hp.one_lt)

theorem gdt_periodic {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} (h : Admissible N m a) :
    IsPeriod N m a (Tmin N m) := by
  intro n
  unfold accepted
  have hTmin_eq : Tmin N m = R N m * m := by unfold Tmin; ring
  have hm_dvd_Tmin : (m : ℤ) ∣ (Tmin N m : ℤ) := by
    have : m ∣ Tmin N m := ⟨R N m, rfl⟩
    exact_mod_cast this
  have hshift_m : ((n : ℤ) + Tmin N m) ≡ (n : ℤ) [ZMOD (m : ℤ)] := by
    have hz : (Tmin N m : ℤ) ≡ 0 [ZMOD (m : ℤ)] := Int.modEq_zero_iff_dvd.mpr hm_dvd_Tmin
    simpa using Int.ModEq.add_left (n : ℤ) hz
  have hcast_eq : ((n + Tmin N m : ℕ) : ℤ) = (n : ℤ) + Tmin N m := by push_cast; ring
  constructor
  · rintro ⟨hmod, hgcd⟩
    have hR1 : Nat.gcd (n + Tmin N m) (R N m) = 1 :=
      (gcd_with_N_iff_gcd_with_R hN hm h hmod).mp hgcd
    have hmod_n : (n : ℤ) ≡ a [ZMOD (m : ℤ)] := hshift_m.symm.trans (hcast_eq ▸ hmod)
    refine ⟨hmod_n, ?_⟩
    have hR0 : Nat.gcd n (R N m) = 1 := by
      rw [hTmin_eq] at hR1
      exact coprime_add_mul_right.mp hR1
    exact (gcd_with_N_iff_gcd_with_R hN hm h hmod_n).mpr hR0
  · rintro ⟨hmod, hgcd⟩
    have hmod' : ((n + Tmin N m : ℕ) : ℤ) ≡ a [ZMOD (m : ℤ)] := by
      rw [hcast_eq]; exact hshift_m.trans hmod
    refine ⟨hmod', ?_⟩
    have hR0 : Nat.gcd n (R N m) = 1 := (gcd_with_N_iff_gcd_with_R hN hm h hmod).mp hgcd
    have hR1 : Nat.gcd (n + Tmin N m) (R N m) = 1 := by
      rw [hTmin_eq]
      exact coprime_add_mul_right.mpr hR0
    exact (gcd_with_N_iff_gcd_with_R hN hm h hmod').mpr hR1

theorem gdt_minimal_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) {t : ℕ} (ht : 0 < t) (hp : IsPeriod N m a t) :
    Tmin N m ∣ t := by
  sorry

/-- If a predicate on `ℕ` is invariant under adding `T`, then the count of elements
satisfying it is the same over any window of length `T`, regardless of start point. -/
lemma periodic_window_card_eq {P : ℕ → Prop} [DecidablePred P] {T : ℕ}
    (hP : ∀ n, P (n + T) ↔ P n) (b : ℕ) :
    ((Finset.Ico b (b + T)).filter P).card =
      ((Finset.Ico 0 T).filter P).card := by
  induction b with
  | zero =>
      simp
  | succ k ih =>
      rcases Nat.eq_zero_or_pos T with hT0 | hT
      · simp [hT0]
      ·
        have hk_notmem : k ∉ Finset.Ico (k + 1) (k + T) := by
          simp only [Finset.mem_Ico]
          omega

        have hkT_notmem : (k + T) ∉ Finset.Ico (k + 1) (k + T) := by
          simp only [Finset.mem_Ico]
          omega

        have hsplit_left :
            Finset.Ico k (k + T) =
              insert k (Finset.Ico (k + 1) (k + T)) := by
          ext n
          simp only [Finset.mem_Ico, Finset.mem_insert]
          omega

        have hsplit_right :
            Finset.Ico (k + 1) (k + 1 + T) =
              insert (k + T) (Finset.Ico (k + 1) (k + T)) := by
          ext n
          simp only [Finset.mem_Ico, Finset.mem_insert]
          omega

        have hcard_left :
            ((Finset.Ico k (k + T)).filter P).card =
              ((Finset.Ico (k + 1) (k + T)).filter P).card +
                (if P k then 1 else 0) := by
          rw [hsplit_left, Finset.filter_insert]
          by_cases hp : P k
          · simp [hp, hk_notmem]
          · simp [hp]

        have hcard_right :
            ((Finset.Ico (k + 1) (k + 1 + T)).filter P).card =
              ((Finset.Ico (k + 1) (k + T)).filter P).card +
                (if P (k + T) then 1 else 0) := by
          rw [hsplit_right, Finset.filter_insert]
          by_cases hp : P (k + T)
          · simp [hp, hkT_notmem]
          · simp [hp]

        have hif_eq :
            (if P k then 1 else 0) =
              (if P (k + T) then 1 else 0) := by
          by_cases hp : P k
          · simp [hp, (hP k).mpr hp]
          ·
            have hnot : ¬ P (k + T) := fun hc => hp ((hP k).mp hc)
            simp [hp, hnot]

        calc
          ((Finset.Ico (k + 1) (k + 1 + T)).filter P).card
              = ((Finset.Ico (k + 1) (k + T)).filter P).card +
                  (if P (k + T) then 1 else 0) := hcard_right
          _ = ((Finset.Ico (k + 1) (k + T)).filter P).card +
                  (if P k then 1 else 0) := by
                rw [← hif_eq]
          _ = ((Finset.Ico k (k + T)).filter P).card := hcard_left.symm
          _ = ((Finset.Ico 0 T).filter P).card := ih

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
