import DivisorF.TailMass
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact finite tail defect level sets

Original Section 3.5 corollaries of the finite large-prime tail-mass theorem.
The level-set argument is purely finite: nonnegative integral defect plus the
exact total tail mass bound.  No prime-distribution input is used here.
-/

namespace DivisorF

open scoped BigOperators

/-- Tail fibres with defect at least the positive integer level `r`. -/
noncomputable def tailLevelPrimes (N : ℕ) (Q : ℝ) (r : ℕ) :
    Finset (LargePrime N) := by
  classical
  exact (tailPrimes N Q).filter fun q => r ≤ Int.toNat (fibreDefect q)

@[simp]
theorem mem_tailLevelPrimes
    {N r : ℕ} {Q : ℝ} {q : LargePrime N} :
    q ∈ tailLevelPrimes N Q r ↔
      q ∈ tailPrimes N Q ∧ r ≤ Int.toNat (fibreDefect q) := by
  classical
  simp [tailLevelPrimes]

/-- Natural defect mass agrees with the integer-valued paper tail sum. -/
theorem tailDefectNatSum_cast
    {N : ℕ} {Q : ℝ} :
    ((∑ q ∈ tailPrimes N Q, Int.toNat (fibreDefect q) : ℕ) : ℤ)
      = tailDefectSum N Q := by
  unfold tailDefectSum
  push_cast
  apply Finset.sum_congr rfl
  intro q _
  rw [Int.toNat_of_nonneg (fibreDefect_nonneg q)]

/-- Every fibre in the `r`-level contributes at least `r` units of defect. -/
theorem tailLevel_weight_le_natDefectSum
    {N r : ℕ} {Q : ℝ} :
    r * (tailLevelPrimes N Q r).card
      ≤ ∑ q ∈ tailPrimes N Q, Int.toNat (fibreDefect q) := by
  classical
  calc
    r * (tailLevelPrimes N Q r).card
        = ∑ _q ∈ tailLevelPrimes N Q r, r := by
            simp [Nat.mul_comm]
    _ ≤ ∑ q ∈ tailLevelPrimes N Q r, Int.toNat (fibreDefect q) := by
          apply Finset.sum_le_sum
          intro q hq
          exact (mem_tailLevelPrimes.mp hq).2
    _ ≤ ∑ q ∈ tailPrimes N Q, Int.toNat (fibreDefect q) := by
          apply Finset.sum_le_sum_of_subset
          intro q hq
          exact (mem_tailLevelPrimes.mp hq).1

/-- **Corollary 3.14 candidate:** exact tail `r`-level bound. -/
theorem tailLevel_card_le
    {N r : ℕ} {Q : ℝ}
    (hN : 2 ≤ N)
    (hQ : Real.sqrt (N : ℝ) ≤ Q)
    (hr : 0 < r) :
    (tailLevelPrimes N Q r).card
      ≤ (2 * tailEndpointCount N Q) / r := by
  apply (Nat.le_div_iff_mul_le hr).2
  have hweight := tailLevel_weight_le_natDefectSum
    (N := N) (Q := Q) (r := r)
  have hmassZ := tailDefectSum_le (N := N) (Q := Q) hN hQ
  have hmassNat :
      (∑ q ∈ tailPrimes N Q, Int.toNat (fibreDefect q) : ℕ)
        ≤ 2 * tailEndpointCount N Q := by
    have hcast := tailDefectNatSum_cast (N := N) (Q := Q)
    rw [← hcast] at hmassZ
    exact_mod_cast hmassZ
  calc
    (tailLevelPrimes N Q r).card * r
        = r * (tailLevelPrimes N Q r).card := Nat.mul_comm _ _
    _ ≤ ∑ q ∈ tailPrimes N Q, Int.toNat (fibreDefect q) := hweight
    _ ≤ 2 * tailEndpointCount N Q := hmassNat

/-- Positive-defect tail support, expressed as the exact `r=1` level. -/
noncomputable def positiveDefectTailPrimes (N : ℕ) (Q : ℝ) :
    Finset (LargePrime N) :=
  tailLevelPrimes N Q 1

@[simp]
theorem mem_positiveDefectTailPrimes
    {N : ℕ} {Q : ℝ} {q : LargePrime N} :
    q ∈ positiveDefectTailPrimes N Q ↔
      q ∈ tailPrimes N Q ∧ 0 < fibreDefect q := by
  rw [positiveDefectTailPrimes, mem_tailLevelPrimes]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have hnonneg := fibreDefect_nonneg q
    have htoNat : 0 < Int.toNat (fibreDefect q) := by omega
    have hcast : (Int.toNat (fibreDefect q) : ℤ) = fibreDefect q :=
      Int.toNat_of_nonneg hnonneg
    omega
  · intro h
    refine ⟨h.1, ?_⟩
    have hnonneg := fibreDefect_nonneg q
    have hcast : (Int.toNat (fibreDefect q) : ℤ) = fibreDefect q :=
      Int.toNat_of_nonneg hnonneg
    omega

/-- **Corollary 3.13 candidate:** exact positive-defect tail support. -/
theorem positiveDefectTail_card_le
    {N : ℕ} {Q : ℝ}
    (hN : 2 ≤ N)
    (hQ : Real.sqrt (N : ℝ) ≤ Q) :
    (positiveDefectTailPrimes N Q).card ≤ 2 * tailEndpointCount N Q := by
  simpa [positiveDefectTailPrimes] using
    (tailLevel_card_le (N := N) (Q := Q) (r := 1) hN hQ (by decide))

end DivisorF
