import DivisorF.CrossingPacking
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact multiplicity thresholds and the quotient-interval barrier

Project-original finite layer from Section 7.  The two `BudgetForces...`
predicates deliberately encode only the information content of the numerical
same-type budget

` t * d ≤ 2 * (s - 1) `.

Their converse directions assert numerical compatibility only; they do not
claim that the trial values `d = 1` or `d = 2` are realised by divisor graphs.
-/

namespace DivisorF

/-- The exact multiplicity `t`, together with the same-type budget alone,
forces zero defect. -/
def BudgetForcesZero (s t : ℕ) : Prop :=
  ∀ d : ℕ, t * d ≤ 2 * (s - 1) → d = 0

/-- The exact multiplicity `t`, together with the same-type budget alone,
forces binary defect. -/
def BudgetForcesBinary (s t : ℕ) : Prop :=
  ∀ d : ℕ, t * d ≤ 2 * (s - 1) → d ≤ 1

/-- **Proposition 7.1 candidate (exact zero threshold).**
Knowing only `t` and `t*d ≤ 2(s-1)` forces `d=0` exactly when
`t > 2(s-1)`. -/
theorem budgetForcesZero_iff (s t : ℕ) :
    BudgetForcesZero s t ↔ 2 * (s - 1) < t := by
  constructor
  · intro hforce
    by_contra hnot
    have hle : t ≤ 2 * (s - 1) := Nat.le_of_not_gt hnot
    have hz : (1 : ℕ) = 0 := hforce 1 (by simpa using hle)
    omega
  · intro hthreshold d hbudget
    by_contra hd
    have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
    have ht_le : t ≤ t * d := by
      simpa using Nat.mul_le_mul_left t hdpos
    have : t ≤ 2 * (s - 1) := le_trans ht_le hbudget
    omega

/-- **Proposition 7.2 candidate (exact binary threshold).**
Knowing only `t` and `t*d ≤ 2(s-1)` forces `d≤1` exactly when
`t > s-1`. -/
theorem budgetForcesBinary_iff (s t : ℕ) :
    BudgetForcesBinary s t ↔ s - 1 < t := by
  constructor
  · intro hforce
    by_contra hnot
    have hle : t ≤ s - 1 := Nat.le_of_not_gt hnot
    have hbudget : t * 2 ≤ 2 * (s - 1) := by
      nlinarith
    have := hforce 2 hbudget
    omega
  · intro hthreshold d hbudget
    by_contra hnot
    have hd : 2 ≤ d := by omega
    have htwo : t * 2 ≤ t * d := Nat.mul_le_mul_left t hd
    have hcap : t * 2 ≤ 2 * (s - 1) := le_trans htwo hbudget
    nlinarith

/-- Paper-facing form of Proposition 7.1 for the actual quotient-type
multiplicity.  Occupancy is retained because it is part of the manuscript
statement, although the numerical equivalence itself is stronger. -/
theorem exact_zero_threshold
    {N s : ℕ} (_hocc : TypeOccupied N s) :
    BudgetForcesZero s (typeMultiplicity N s) ↔
      2 * (s - 1) < typeMultiplicity N s := by
  exact budgetForcesZero_iff _ _

/-- Paper-facing form of Proposition 7.2 for the actual quotient-type
multiplicity. -/
theorem exact_binary_threshold
    {N s : ℕ} (_hocc : TypeOccupied N s) :
    BudgetForcesBinary s (typeMultiplicity N s) ↔
      s - 1 < typeMultiplicity N s := by
  exact budgetForcesBinary_iff _ _

/-- Width of the exact quotient interval
`(floor(N/(s+1)), floor(N/s)]`. -/
def quotientIntervalWidth (N s : ℕ) : ℕ :=
  N / s - N / (s + 1)

/-- A large prime has quotient type `s` exactly when its value lies in the
corresponding quotient interval. -/
theorem mem_typePrimes_iff_quotient_interval
    {N s : ℕ} (hs : 0 < s) {q : LargePrime N} :
    q ∈ typePrimes N s ↔
      N / (s + 1) < q.val ∧ q.val ≤ N / s := by
  rw [mem_typePrimes]
  constructor
  · intro htype
    have hs_mul_le : s * q.val ≤ N := by
      rw [← htype]
      exact Nat.div_mul_le_self N q.val
    have hupper : q.val ≤ N / s := by
      apply (Nat.le_div_iff_mul_le hs).2
      simpa [Nat.mul_comm] using hs_mul_le
    refine ⟨?_, hupper⟩
    by_contra hnot
    have hqle : q.val ≤ N / (s + 1) := Nat.le_of_not_gt hnot
    have hqmul : q.val * (s + 1) ≤ N :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos s)).1 hqle
    have hs1le : s + 1 ≤ N / q.val := by
      apply (Nat.le_div_iff_mul_le q.pos).2
      simpa [Nat.mul_comm] using hqmul
    change s + 1 ≤ q.quotientType at hs1le
    rw [htype] at hs1le
    omega
  · rintro ⟨hlower, hupper⟩
    have hsle : s ≤ N / q.val := by
      apply (Nat.le_div_iff_mul_le q.pos).2
      have hmul : q.val * s ≤ N :=
        (Nat.le_div_iff_mul_le hs).1 hupper
      simpa [Nat.mul_comm] using hmul
    have hlt : N / q.val < s + 1 := by
      by_contra hnot
      have hs1le : s + 1 ≤ N / q.val := Nat.le_of_not_gt hnot
      have hmul : (s + 1) * q.val ≤ N :=
        (Nat.le_div_iff_mul_le q.pos).1 hs1le
      have hqle : q.val ≤ N / (s + 1) := by
        apply (Nat.le_div_iff_mul_le (Nat.succ_pos s)).2
        simpa [Nat.mul_comm] using hmul
      exact (Nat.not_lt_of_ge hqle) hlower
    unfold LargePrime.quotientType
    omega

private theorem largePrime_val_injective {N : ℕ} :
    Function.Injective (fun q : LargePrime N => q.val) := by
  intro q r h
  cases q with
  | mk qval qprime qlarge qle =>
      cases r with
      | mk rval rprime rlarge rle =>
          simp only at h
          subst rval
          rfl

/-- Values of the large primes of quotient type `s`. -/
noncomputable def typePrimeValues (N s : ℕ) : Finset ℕ :=
  (typePrimes N s).image (fun q => q.val)

/-- Passing from a large prime to its value loses no cardinality. -/
theorem typePrimeValues_card_eq_typeMultiplicity (N s : ℕ) :
    (typePrimeValues N s).card = typeMultiplicity N s := by
  unfold typePrimeValues typeMultiplicity
  exact Finset.card_image_of_injective _ largePrime_val_injective

/-- The values of all type-`s` large primes lie in the exact quotient
interval. -/
theorem typePrimeValues_subset_quotient_interval
    {N s : ℕ} (hs : 0 < s) :
    typePrimeValues N s ⊆ Finset.Ioc (N / (s + 1)) (N / s) := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
  exact Finset.mem_Ioc.mpr
    ((mem_typePrimes_iff_quotient_interval hs).mp hq)

/-- The exact multiplicity is at most the width of its quotient interval. -/
theorem typeMultiplicity_le_quotientIntervalWidth
    {N s : ℕ} (hs : 0 < s) :
    typeMultiplicity N s ≤ quotientIntervalWidth N s := by
  rw [← typePrimeValues_card_eq_typeMultiplicity]
  calc
    (typePrimeValues N s).card
        ≤ (Finset.Ioc (N / (s + 1)) (N / s)).card :=
      Finset.card_le_card (typePrimeValues_subset_quotient_interval hs)
    _ = quotientIntervalWidth N s := by
      simp [quotientIntervalWidth]

/-- **Lemma 7.3 candidate (quotient-interval width).** -/
theorem quotientIntervalWidth_le_ceil
    {N s : ℕ} (hs : 1 ≤ s) :
    quotientIntervalWidth N s ≤
      Nat.ceil ((N : ℝ) / ((s * (s + 1) : ℕ) : ℝ)) := by
  let a : ℕ := N / s
  let b : ℕ := N / (s + 1)
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs
  have hbmul1 : b * (s + 1) ≤ N := by
    simpa [b] using Nat.div_mul_le_self N (s + 1)
  have hbmul : b * s ≤ N := by
    calc
      b * s ≤ b * (s + 1) := Nat.mul_le_mul_left b (Nat.le_succ s)
      _ ≤ N := hbmul1
  have hba : b ≤ a := by
    dsimp [a]
    exact (Nat.le_div_iff_mul_le hspos).2 hbmul
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hspos
  have hs1R : 0 < ((s + 1 : ℕ) : ℝ) := by positivity
  have hamul : a * s ≤ N := by
    simpa [a] using Nat.div_mul_le_self N s
  have ha_le : (a : ℝ) ≤ (N : ℝ) / (s : ℝ) := by
    apply (le_div_iff₀ hsR).2
    exact_mod_cast hamul
  have hupperNat : N < (b + 1) * (s + 1) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos s)).1
    simp [b]
  have hb_lower :
      (N : ℝ) / ((s + 1 : ℕ) : ℝ) < (b : ℝ) + 1 := by
    apply (div_lt_iff₀ hs1R).2
    exact_mod_cast hupperNat
  have hdiff :
      (N : ℝ) / (s : ℝ) - (N : ℝ) / ((s + 1 : ℕ) : ℝ) =
        (N : ℝ) / ((s * (s + 1) : ℕ) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hsR]
    ring
  have hwlt :
      ((a - b : ℕ) : ℝ) <
        (N : ℝ) / ((s * (s + 1) : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hba, ← hdiff]
    nlinarith
  have hfinal :
      a - b ≤ Nat.ceil ((N : ℝ) / ((s * (s + 1) : ℕ) : ℝ)) := by
    by_cases hwzero : a - b = 0
    · simp [hwzero]
    · have hone : 1 ≤ a - b := Nat.one_le_iff_ne_zero.mpr hwzero
      have hpredCast :
          (((a - b) - 1 : ℕ) : ℝ) = ((a - b : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub hone]
        norm_num
      have hpredlt :
          (((a - b) - 1 : ℕ) : ℝ) <
            (N : ℝ) / ((s * (s + 1) : ℕ) : ℝ) := by
        rw [hpredCast]
        exact (sub_lt_iff_lt_add).2 hwlt
      have hceil := (Nat.lt_ceil).2 hpredlt
      omega
  simpa [quotientIntervalWidth, a, b] using hfinal

/-- A positive occupied quotient type. -/
theorem typeOccupied_type_pos {N s : ℕ} (hocc : TypeOccupied N s) : 0 < s := by
  rcases hocc with ⟨q, hq⟩
  have htype := mem_typePrimes.mp hq
  have hone : 1 ≤ N / q.val := by
    apply (Nat.le_div_iff_mul_le q.pos).2
    simpa using q.le_N
  change 1 ≤ q.quotientType at hone
  rw [htype] at hone
  omega

/-- A real quotient bounded by an integer `C` has natural ceiling at most
`C`; packaged in the exact denominator needed for Section 7. -/
theorem ceil_quotient_scale_le
    {N s C : ℕ} (hs : 0 < s)
    (hN : N ≤ C * (s * (s + 1))) :
    Nat.ceil ((N : ℝ) / ((s * (s + 1) : ℕ) : ℝ)) ≤ C := by
  apply (Nat.ceil_le).2
  have hden : 0 < (((s * (s + 1) : ℕ) : ℝ)) := by positivity
  apply (div_le_iff₀ hden).2
  exact_mod_cast hN

/-- Any upper bound on the quotient-interval width at or below the zero
capacity threshold is already enough to certify that multiplicity-plus-budget
information cannot force zero defect. -/
theorem not_budgetForcesZero_of_quotientIntervalWidth_le
    {N s : ℕ} (hs : 0 < s)
    (hwidth : quotientIntervalWidth N s ≤ 2 * (s - 1)) :
    ¬ BudgetForcesZero s (typeMultiplicity N s) := by
  rw [budgetForcesZero_iff]
  have hmult := typeMultiplicity_le_quotientIntervalWidth (N := N) hs
  omega

/-- Binary analogue of `not_budgetForcesZero_of_quotientIntervalWidth_le`. -/
theorem not_budgetForcesBinary_of_quotientIntervalWidth_le
    {N s : ℕ} (hs : 0 < s)
    (hwidth : quotientIntervalWidth N s ≤ s - 1) :
    ¬ BudgetForcesBinary s (typeMultiplicity N s) := by
  rw [budgetForcesBinary_iff]
  have hmult := typeMultiplicity_le_quotientIntervalWidth (N := N) hs
  omega

private theorem sq_sub_one_eq_pred_mul_succ {s : ℕ} (hs : 1 ≤ s) :
    s ^ 2 - 1 = (s - 1) * (s + 1) := by
  have hpred : s = (s - 1) + 1 := (Nat.sub_add_cancel hs).symm
  calc
    s ^ 2 - 1 = ((s - 1) + 1) ^ 2 - 1 := by rw [← hpred]
    _ = (s - 1) * ((s - 1) + 2) := by
      have hsq :
          ((s - 1) + 1) ^ 2 = (s - 1) * ((s - 1) + 2) + 1 := by
        ring
      omega
    _ = (s - 1) * (s + 1) := by
      have hsucc : (s - 1) + 2 = s + 1 := by omega
      rw [hsucc]

/-- **Theorem 7.4 candidate (zero-defect multiplicity barrier).** -/
theorem zero_defect_multiplicity_barrier
    {N s : ℕ} (hocc : TypeOccupied N s)
    (hN : N ≤ 2 * s * (s ^ 2 - 1)) :
    ¬ BudgetForcesZero s (typeMultiplicity N s) := by
  have hspos := typeOccupied_type_pos hocc
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hspos)
  have hfactor := sq_sub_one_eq_pred_mul_succ hs
  have hscaled : N ≤ (2 * (s - 1)) * (s * (s + 1)) := by
    calc
      N ≤ 2 * s * (s ^ 2 - 1) := hN
      _ = (2 * (s - 1)) * (s * (s + 1)) := by
        rw [hfactor]
        ring
  have hceil := ceil_quotient_scale_le (N := N) (s := s)
    (C := 2 * (s - 1)) hspos hscaled
  have hwidth : quotientIntervalWidth N s ≤ 2 * (s - 1) :=
    le_trans (quotientIntervalWidth_le_ceil (N := N) hs) hceil
  exact not_budgetForcesZero_of_quotientIntervalWidth_le hspos hwidth

/-- **Theorem 7.5 candidate (binary-defect multiplicity barrier).** -/
theorem binary_defect_multiplicity_barrier
    {N s : ℕ} (hocc : TypeOccupied N s)
    (hN : N ≤ s * (s ^ 2 - 1)) :
    ¬ BudgetForcesBinary s (typeMultiplicity N s) := by
  have hspos := typeOccupied_type_pos hocc
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hspos)
  have hfactor := sq_sub_one_eq_pred_mul_succ hs
  have hscaled : N ≤ (s - 1) * (s * (s + 1)) := by
    calc
      N ≤ s * (s ^ 2 - 1) := hN
      _ = (s - 1) * (s * (s + 1)) := by
        rw [hfactor]
        ring
  have hceil := ceil_quotient_scale_le (N := N) (s := s)
    (C := s - 1) hspos hscaled
  have hwidth : quotientIntervalWidth N s ≤ s - 1 :=
    le_trans (quotientIntervalWidth_le_ceil (N := N) hs) hceil
  exact not_budgetForcesBinary_of_quotientIntervalWidth_le hspos hwidth

end DivisorF
