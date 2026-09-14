import DivisorF.Rigidity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Extremal fibre rigidity

Equality-case fibre geometry for the original Proposition 3.10 and
Corollary 3.11.  Once the cumulative nonbinary count saturates `K-1`, the
global restriction-loss sum vanishes.  Because every individual fibre and
complement restriction loss is nonnegative, both losses vanish separately on
every counted fibre.  Thus the exact defect decomposition becomes `D_B=m_B`
inside the same maximum forest.
-/

namespace DivisorF

/--
At extremality, both restriction losses vanish separately for every fibre in
the cumulative family.
-/
theorem restrictionLosses_eq_zero_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeFibres N K) :
    fibreRestrictionLoss q L = 0 ∧ complementRestrictionLoss q L = 0 := by
  have htotal := (extremalRigidity_terms_vanish hL hmax hsat).2.1
  have hsum_nonneg :
      ∀ r ∈ cumulativeFibres N K,
        0 ≤ fibreRestrictionLoss r L + complementRestrictionLoss r L := by
    intro r _
    exact add_nonneg
      (fibreRestrictionLoss_nonneg r hL)
      (complementRestrictionLoss_nonneg r hL)
  have hqle :
      fibreRestrictionLoss q L + complementRestrictionLoss q L
        ≤ cumulativeRestrictionLoss K L := by
    unfold cumulativeRestrictionLoss
    exact Finset.single_le_sum hsum_nonneg hq
  rw [htotal] at hqle
  have hfi := fibreRestrictionLoss_nonneg q hL
  have hco := complementRestrictionLoss_nonneg q hL
  constructor <;> omega

/--
At extremality, the selected crossing count of every cumulative fibre equals
its defect in the same maximum forest.
-/
theorem crossingCount_eq_fibreDefect_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeFibres N K) :
    (crossingCount q L : ℤ) = fibreDefect q := by
  obtain ⟨hfi, hco⟩ := restrictionLosses_eq_zero_of_extremal
    hL hmax hsat hq
  rw [fibreDefect_eq_crossing_sub_losses q hmax, hfi, hco]
  ring

/-- Every cumulative fibre has defect either zero or exactly two at extremality. -/
theorem fibreDefect_eq_zero_or_two_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeFibres N K) :
    fibreDefect q = 0 ∨ fibreDefect q = 2 := by
  by_cases htwo : (2 : ℤ) ≤ fibreDefect q
  · right
    apply fibreDefect_eq_two_of_extremal hL hmax hsat
    exact mem_cumulativeLevelFibres.mpr ⟨hq, htwo⟩
  · have hlt : fibreDefect q < 2 := lt_of_not_ge htwo
    have hnonneg := fibreDefect_nonneg q
    by_cases hone : fibreDefect q = 1
    · have hmem : q ∈ cumulativeDefectOneFibres N K :=
        mem_cumulativeDefectOneFibres.mpr ⟨hq, hone⟩
      have hempty := no_defect_one_of_extremal hL hmax hsat
      rw [hempty] at hmem
      simp at hmem
    · left
      omega

/--
Consequently every cumulative fibre has either zero or two selected crossings
in every maximum forest at extremality.
-/
theorem crossingCount_eq_zero_or_two_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeFibres N K) :
    crossingCount q L = 0 ∨ crossingCount q L = 2 := by
  have hcross := crossingCount_eq_fibreDefect_of_extremal hL hmax hsat hq
  rcases fibreDefect_eq_zero_or_two_of_extremal hL hmax hsat hq with hzero | htwo
  · left
    rw [hzero] at hcross
    exact_mod_cast hcross
  · right
    rw [htwo] at hcross
    exact_mod_cast hcross

/-- Every nonbinary cumulative fibre has exactly two selected crossings. -/
theorem crossingCount_eq_two_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeLevelFibres N K 2) :
    crossingCount q L = 2 := by
  have hqcum := (mem_cumulativeLevelFibres.mp hq).1
  have hcross := crossingCount_eq_fibreDefect_of_extremal hL hmax hsat hqcum
  have hdef := fibreDefect_eq_two_of_extremal hL hmax hsat hq
  rw [hdef] at hcross
  exact_mod_cast hcross

/-- Every cumulative fibre outside the nonbinary level has zero selected crossings. -/
theorem crossingCount_eq_zero_of_not_nonbinary_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeFibres N K)
    (hqnot : q ∉ cumulativeLevelFibres N K 2) :
    crossingCount q L = 0 := by
  rcases crossingCount_eq_zero_or_two_of_extremal hL hmax hsat hq with hzero | htwo
  · exact hzero
  · exfalso
    have hdef := crossingCount_eq_fibreDefect_of_extremal hL hmax hsat hq
    rw [htwo] at hdef
    have htwoDef : fibreDefect q = 2 := by omega
    apply hqnot
    exact mem_cumulativeLevelFibres.mpr ⟨hq, by omega⟩

end DivisorF
