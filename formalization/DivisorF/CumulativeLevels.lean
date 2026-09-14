import DivisorF.GlobalSlack
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Cumulative defect level sets

Original Corollary 3.9 consequences of the cumulative boundary budget.
-/

namespace DivisorF

/-- Fibres in `𝓕_K(N)` whose defect is at least the positive integer level `r`. -/
noncomputable def cumulativeLevelFibres (N K r : ℕ) : Finset (LargePrime N) := by
  classical
  exact (cumulativeFibres N K).filter fun q => (r : ℤ) ≤ fibreDefect q

@[simp]
theorem mem_cumulativeLevelFibres {N K r : ℕ} {q : LargePrime N} :
    q ∈ cumulativeLevelFibres N K r ↔
      q ∈ cumulativeFibres N K ∧ (r : ℤ) ≤ fibreDefect q := by
  classical
  simp [cumulativeLevelFibres]

/-- Weighted counting form of the universal cumulative level-set hierarchy. -/
theorem cumulativeLevel_weight_le
    {N K r : ℕ} :
    ((r * (cumulativeLevelFibres N K r).card : ℕ) : ℤ)
      ≤ cumulativeDefectSum N K := by
  classical
  unfold cumulativeDefectSum cumulativeLevelFibres
  calc
    ((r * ((cumulativeFibres N K).filter
        (fun q => (r : ℤ) ≤ fibreDefect q)).card : ℕ) : ℤ)
        = ∑ _q ∈ (cumulativeFibres N K).filter
            (fun q => (r : ℤ) ≤ fibreDefect q), (r : ℤ) := by
              simp [mul_comm]
    _ ≤ ∑ q ∈ (cumulativeFibres N K).filter
            (fun q => (r : ℤ) ≤ fibreDefect q), fibreDefect q := by
          apply Finset.sum_le_sum
          intro q hq
          exact (Finset.mem_filter.mp hq).2
    _ ≤ ∑ q ∈ cumulativeFibres N K, fibreDefect q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            exact (Finset.mem_filter.mp hq).1
          · intro q hq _
            exact fibreDefect_nonneg q

/-- **Corollary 3.9 candidate:** `r * a_r(N,K) ≤ 2(K-1)`. -/
theorem cumulativeLevel_card_mul_le
    {N K r : ℕ} :
    r * (cumulativeLevelFibres N K r).card ≤ 2 * (K - 1) := by
  have hlevel := cumulativeLevel_weight_le (N := N) (K := K) (r := r)
  have hbudget := cumulativeDefectSum_le (N := N) (K := K)
  have hcap :
      (cumulativeBoundaryCapacity K : ℤ) = ((2 * (K - 1) : ℕ) : ℤ) := rfl
  rw [hcap] at hbudget
  exact_mod_cast le_trans hlevel hbudget

/-- Integer-floor form of Corollary 3.9. -/
theorem cumulativeLevel_card_le
    {N K r : ℕ} (hr : 0 < r) :
    (cumulativeLevelFibres N K r).card ≤ (2 * (K - 1)) / r := by
  apply (Nat.le_div_iff_mul_le hr).2
  simpa [Nat.mul_comm] using
    (cumulativeLevel_card_mul_le (N := N) (K := K) (r := r))

/-- At most `K-1` cumulative fibres can be nonbinary. -/
theorem cumulativeNonbinary_card_le {N K : ℕ} :
    (cumulativeLevelFibres N K 2).card ≤ K - 1 := by
  have h := cumulativeLevel_card_le
    (N := N) (K := K) (r := 2) (by decide)
  omega

end DivisorF
