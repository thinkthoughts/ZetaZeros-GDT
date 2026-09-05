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

lemma exists_accepted {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) : ∃ n, accepted N m a n := by
  set aN : ℕ := (a % (m : ℤ)).toNat with haN_def

  have haN_nonneg : (0 : ℤ) ≤ a % (m : ℤ) :=
    Int.emod_nonneg a (by exact_mod_cast hm.ne')

  have haN_eq : (aN : ℤ) = a % (m : ℤ) :=
    Int.toNat_of_nonneg haN_nonneg

  have haN_cong : (aN : ℤ) ≡ a [ZMOD (m : ℤ)] := by
    show (aN : ℤ) % (m : ℤ) = a % (m : ℤ)
    rw [haN_eq, Int.emod_emod_of_dvd a (dvd_refl (m : ℤ))]

  obtain ⟨k, hk1, hk2⟩ :=
    Nat.chineseRemainder (coprime_m_R hN) aN 1

  refine ⟨k, ?_⟩
  unfold accepted

  have hcongm : ((k : ℕ) : ℤ) ≡ a [ZMOD (m : ℤ)] := by
    have hk1' : ((k : ℕ) : ℤ) ≡ (aN : ℤ) [ZMOD (m : ℤ)] := by
      exact_mod_cast hk1
    exact hk1'.trans haN_cong

  refine ⟨hcongm, ?_⟩

  have hgcdR : Nat.gcd k (R N m) = 1 := by
    rw [gcd_mod_eq, hk2]

  exact (gcd_with_N_iff_gcd_with_R hN hm h hcongm).mpr hgcdR

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

/-- `m` and `R N m` share no prime factor. -/
lemma coprime_m_R {N m : ℕ} (hN : 0 < N) :
    Nat.Coprime m (R N m) := by
  by_contra hne
  have hne' : Nat.gcd m (R N m) ≠ 1 := hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne'

  have hpm : p ∣ m :=
    hpdvd.trans (Nat.gcd_dvd_left _ _)

  have hpR : p ∣ R N m :=
    hpdvd.trans (Nat.gcd_dvd_right _ _)

  have hpradN : p ∣ rad N := by
    have hR_dvd : R N m ∣ rad N := by
      refine ⟨d N m, ?_⟩
      rw [← d_mul_R_eq_rad hN]
      ring
    exact hpR.trans hR_dvd

  have hpN : p ∣ N :=
    hpradN.trans (rad_dvd_self N)

  have hp_gcd_mN : p ∣ Nat.gcd m N :=
    Nat.dvd_gcd hpm hpN

  have hgcd_ne : Nat.gcd m N ≠ 0 := by
    exact (Nat.gcd_pos_of_pos_right m hN).ne'

  have hp_mem : p ∈ (Nat.gcd m N).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hp_gcd_mN, hgcd_ne⟩

  have hpd : p ∣ d N m := by
    unfold d rad
    apply Nat.dvd_of_mem_primeFactors
    change p ∈ (∏ q ∈ (Nat.gcd m N).primeFactors, q).primeFactors
    rw [Nat.primeFactors_prod
      (fun q hq => Nat.prime_of_mem_primeFactors hq)]
    exact hp_mem

  have hcontra : p ∣ Nat.gcd (d N m) (R N m) :=
    Nat.dvd_gcd hpd hpR

  have heq : Nat.gcd (d N m) (R N m) = 1 :=
    coprime_d_R hN

  rw [heq] at hcontra

  exact absurd
    (Nat.le_of_dvd one_pos hcontra)
    (not_le.mpr hp.one_lt)

lemma accepted_iff_coprime_R {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) (n : ℕ) :
    accepted N m a n ↔
      (n : ℤ) ≡ a [ZMOD (m : ℤ)] ∧ Nat.gcd n (R N m) = 1 := by
  unfold accepted
  constructor
  · rintro ⟨hmod, hgcd⟩
    exact ⟨hmod, (gcd_with_N_iff_gcd_with_R hN hm h hmod).mp hgcd⟩
  · rintro ⟨hmod, hgcdR⟩
    exact ⟨hmod, (gcd_with_N_iff_gcd_with_R hN hm h hmod).mpr hgcdR⟩

/-- `rad n` is always positive. -/
lemma rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad
  exact Finset.prod_pos
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

/-- `R N m` is positive when `N > 0`. -/
lemma R_pos {N m : ℕ} (hN : 0 < N) : 0 < R N m := by
  have heq := d_mul_R_eq_rad (N := N) (m := m) hN
  have hrad_pos := rad_pos N
  rcases Nat.eq_zero_or_pos (R N m) with hR0 | hR
  · rw [hR0, mul_zero] at heq
    omega
  · exact hR

/-- Every residue `r < R N m` has a representative in the canonical window
with the prescribed residue mod `m`. -/
lemma exists_repr_mod_R {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {r : ℕ}
    (hr : r < R N m) :
    ∃ n, n < Tmin N m ∧
      (n : ℤ) ≡ a [ZMOD (m : ℤ)] ∧
      n % R N m = r := by
  set aN : ℕ := (a % (m : ℤ)).toNat with haN_def
  have haN_nonneg : (0 : ℤ) ≤ a % (m : ℤ) :=
    Int.emod_nonneg a (by exact_mod_cast hm.ne')
  have haN_eq : (aN : ℤ) = a % (m : ℤ) :=
    Int.toNat_of_nonneg haN_nonneg
  have haN_cong : (aN : ℤ) ≡ a [ZMOD (m : ℤ)] := by
    show (aN : ℤ) % (m : ℤ) = a % (m : ℤ)
    rw [haN_eq, Int.emod_emod_of_dvd a (dvd_refl (m : ℤ))]
  obtain ⟨k, hk1, hk2⟩ :=
    Nat.chineseRemainder (coprime_m_R hN) aN r
  have hTmin_pos : 0 < Tmin N m := by
    unfold Tmin
    exact Nat.mul_pos hm (R_pos hN)
  have hTdvd_m : m ∣ Tmin N m := ⟨R N m, rfl⟩
  have hTdvd_R : R N m ∣ Tmin N m := ⟨m, by
    unfold Tmin
    ring⟩
  refine ⟨k % Tmin N m, Nat.mod_lt k hTmin_pos, ?_, ?_⟩
  · have hstep : k % Tmin N m ≡ k [MOD m] :=
      Nat.ModEq.of_dvd hTdvd_m (Nat.mod_modEq k (Tmin N m))
    have hnm : k % Tmin N m ≡ aN [MOD m] :=
      hstep.trans hk1
    have hz :
        ((k % Tmin N m : ℕ) : ℤ) ≡ (aN : ℤ) [ZMOD (m : ℤ)] := by
      exact_mod_cast hnm
    exact hz.trans haN_cong
  · have hstep : k % Tmin N m ≡ k [MOD R N m] :=
      Nat.ModEq.of_dvd hTdvd_R (Nat.mod_modEq k (Tmin N m))
    have hnR : k % Tmin N m ≡ r [MOD R N m] :=
      hstep.trans hk2
    calc
      k % Tmin N m % R N m = r % R N m := hnR
      _ = r := Nat.mod_eq_of_lt hr

/-- Two canonical-window representatives agreeing mod `m` and mod `R` are equal. -/
lemma repr_unique {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {n1 n2 : ℕ}
    (h1 : n1 < Tmin N m) (h2 : n2 < Tmin N m)
    (hmod1 : (n1 : ℤ) ≡ a [ZMOD (m : ℤ)])
    (hmod2 : (n2 : ℤ) ≡ a [ZMOD (m : ℤ)])
    (hReq : n1 % R N m = n2 % R N m) : n1 = n2 := by
  have hmodm : n1 ≡ n2 [MOD m] := by
    have h : (n1 : ℤ) ≡ (n2 : ℤ) [ZMOD (m : ℤ)] :=
      hmod1.trans hmod2.symm
    exact_mod_cast h
  have hmodR : n1 ≡ n2 [MOD R N m] := hReq
  have hmodTmin : n1 ≡ n2 [MOD Tmin N m] := by
    have hcomb :=
      (Nat.modEq_and_modEq_iff_modEq_mul (coprime_m_R hN)).mp
        ⟨hmodm, hmodR⟩
    unfold Tmin
    exact hcomb
  have heq := hmodTmin
  unfold Nat.ModEq at heq
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at heq

/-- Coprimality with `R` depends only on the residue modulo `R`. -/
lemma gcd_mod_eq (n R : ℕ) :
    Nat.gcd n R = Nat.gcd (n % R) R := by
  rw [Nat.gcd_comm n R, Nat.gcd_rec R n]

theorem gdt_minimal_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) {t : ℕ} (ht : 0 < t) (hp : IsPeriod N m a t) :
    Tmin N m ∣ t := by
  obtain ⟨n0, hn0⟩ := exists_accepted hN hm h

  have hn0t : accepted N m a (n0 + t) :=
    (hp n0).mpr hn0

  have hmt : m ∣ t := by
    have hmod0 : (n0 : ℤ) ≡ a [ZMOD (m : ℤ)] :=
      hn0.1

    have hmodt : ((n0 + t : ℕ) : ℤ) ≡ a [ZMOD (m : ℤ)] :=
      hn0t.1

    have hdiff :
        ((n0 : ℤ) + (t : ℤ)) ≡ (n0 : ℤ) [ZMOD (m : ℤ)] := by
      push_cast at hmodt
      exact hmodt.trans hmod0.symm

    have hmtZ : (m : ℤ) ∣ (t : ℤ) := by
      simpa using (Int.modEq_iff_dvd.mp hdiff.symm)

    exact_mod_cast hmtZ

  sorry

lemma canonical_window_card_eq_range_coprime {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) :
    ((Finset.Ico 0 (Tmin N m)).filter
        (fun (n : ℕ) => (n : ℤ) ≡ a [ZMOD (m : ℤ)] ∧ Nat.gcd n (R N m) = 1)).card =
      ((Finset.range (R N m)).filter
        (fun r => Nat.gcd r (R N m) = 1)).card := by
  apply Finset.card_bij (fun n _ => n % R N m)
  · rintro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    obtain ⟨⟨-, hlt⟩, hmod, hgcd⟩ := hn
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt n (R_pos hN), by rwa [← gcd_mod_eq]⟩
  · rintro n1 hn1 n2 hn2 heq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn1 hn2
    obtain ⟨⟨-, hlt1⟩, hmod1, -⟩ := hn1
    obtain ⟨⟨-, hlt2⟩, hmod2, -⟩ := hn2
    exact repr_unique hN hm hlt1 hlt2 hmod1 hmod2 heq
  · rintro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrlt, hrcop⟩ := hr
    obtain ⟨n, hnlt, hnmod, hnmodR⟩ := exists_repr_mod_R (a := a) hN hm hrlt
    refine ⟨n, ?_, hnmodR⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Nat.zero_le n, hnlt⟩, hnmod, by rw [gcd_mod_eq, hnmodR]; exact hrcop⟩

lemma count_canonical_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) :
    ((Finset.Ico 0 (Tmin N m)).filter (accepted N m a)).card =
      Nat.totient (R N m) := by
  rw [Finset.filter_congr (fun n _ => accepted_iff_coprime_R hN hm h n),
      canonical_window_card_eq_range_coprime hN hm h,
      Nat.totient_eq_card_coprime]
  apply congrArg Finset.card
  exact Finset.filter_congr (fun r _ => by
    change Nat.gcd r (R N m) = 1 ↔ Nat.gcd (R N m) r = 1
    rw [Nat.gcd_comm])

theorem gdt_count_per_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) (b : ℕ) :
    ((Finset.Ico b (b + Tmin N m)).filter (accepted N m a)).card =
      Nat.totient (R N m) := by
  rw [periodic_window_card_eq (gdt_periodic hN hm h) b]
  exact count_canonical_period hN hm h

lemma card_filter_Ico_split {P : ℕ → Prop} [DecidablePred P] {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    ((Finset.Ico a c).filter P).card =
      ((Finset.Ico a b).filter P).card + ((Finset.Ico b c).filter P).card := by
  have hunion : Finset.Ico a c = Finset.Ico a b ∪ Finset.Ico b c := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ico a b) (Finset.Ico b c) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_Ico] at hn1 hn2
    omega
  rw [hunion, Finset.filter_union,
      Finset.card_union_of_disjoint
        (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

lemma S_eq_filter_Ico (N L m : ℕ) (a : ℤ) :
    S N L m a =
      (Finset.Ico 1 (L + 1)).filter (accepted N m a) := by
  unfold S
  apply Finset.ext
  intro n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  simp [Nat.lt_succ_iff]

theorem gdt_density {N m q s : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) (hs : s < Tmin N m) :
    (S N (q * Tmin N m + s) m a).card =
      q * Nat.totient (R N m) + (S N s m a).card := by
  induction q with
  | zero => simp
  | succ k ih =>
    have hsplit : (k + 1) * Tmin N m + s =
        (k * Tmin N m + s) + Tmin N m := by
      ring
    rw [hsplit, S_eq_filter_Ico]
    rw [card_filter_Ico_split
      (a := 1)
      (b := k * Tmin N m + s + 1)
      (c := k * Tmin N m + s + Tmin N m + 1)
      (by omega) (by omega)]
    have hfirst :
        ((Finset.Ico 1 (k * Tmin N m + s + 1)).filter
          (accepted N m a)).card =
          k * Nat.totient (R N m) + (S N s m a).card := by
      rw [← S_eq_filter_Ico]
      exact ih
    have hsecond :
        ((Finset.Ico (k * Tmin N m + s + 1)
          (k * Tmin N m + s + Tmin N m + 1)).filter
          (accepted N m a)).card =
          Nat.totient (R N m) := by
      have heq :
          k * Tmin N m + s + Tmin N m + 1 =
            (k * Tmin N m + s + 1) + Tmin N m := by
        ring
      rw [heq]
      exact gdt_count_per_period hN hm h (k * Tmin N m + s + 1)
    rw [hfirst, hsecond]
    ring

/-- Exponent-blindness: `φ(n)/n` depends only on `rad n`. -/
lemma totient_rad_mul (n : ℕ) (hn : 0 < n) :
    n * Nat.totient (rad n) = rad n * Nat.totient n := by
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
