import DivisorF.ExceptionalEndpointThickening
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Literal geometry of the real thickening in Lemma 6.1

The fixed-error discretisation in Section 6 thickens every bad integer centre
`n` to the real interval `[n-h,n+h]`.  The measure-theoretic double count has two
logically separate project-owned ingredients:

* each thickened interval is contained in the enlarged real exceptional set;
* because the centres are integers, a real point belongs to at most
  `2 h + O(1)` such intervals.

`ExceptionalEndpointThickening` already records the final real-valued double
count as the narrow certificate consumed by the rest of the formalization.
This module discharges the second ingredient at the literal interval level for
an integer radius `H`: every real point lies in at most `2H+1` intervals
centred at an arbitrary finite set of integers.  Thus the remaining
measure-theoretic bridge no longer has any hidden combinatorial overlap claim;
it only has to integrate this pointwise estimate together with the interval
containment supplied by the manuscript's shift-stability argument.
-/

namespace DivisorF

/-- The closed real interval of radius `H` around an integer centre `n`. -/
def integerThickeningInterval (n H : ℕ) : Set ℝ :=
  Set.Icc ((n : ℝ) - (H : ℝ)) ((n : ℝ) + (H : ℝ))

/-- The bad integer centres whose radius-`H` thickening contains `u`. -/
noncomputable def integerThickeningCentres (bad : Finset ℕ) (H : ℕ) (u : ℝ) :
    Finset ℕ :=
  bad.filter fun n => |(n : ℝ) - u| ≤ (H : ℝ)

/-- Membership in a real thickening interval is classically decidable; naming
one instance keeps every filter below on the same decision procedure. -/
noncomputable local instance memIntegerThickeningIntervalDecidablePred
    (u : ℝ) (H : ℕ) :
    DecidablePred fun n : ℕ => u ∈ integerThickeningInterval n H :=
  fun _ => Classical.dec _

/-- Membership in the literal thickening interval is the expected absolute-value
condition. -/
theorem mem_integerThickeningInterval_iff
    {n H : ℕ} {u : ℝ} :
    u ∈ integerThickeningInterval n H ↔ |(n : ℝ) - u| ≤ (H : ℝ) := by
  rw [integerThickeningInterval, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨hleft, hright⟩
    constructor <;> linarith
  · rintro ⟨hleft, hright⟩
    constructor <;> linarith

/-- **Bounded-overlap geometry for Lemma 6.1.**

For any finite collection of integer centres and any real point `u`, at most
`2H+1` radius-`H` thickening intervals can contain `u`.  This is the exact
integer-centre version of the manuscript's `2h+O(1)` multiplicity statement.
-/
theorem integerThickeningCentres_card_le
    (bad : Finset ℕ) (H : ℕ) (u : ℝ) :
    (integerThickeningCentres bad H u).card ≤ 2 * H + 1 := by
  classical
  let S := integerThickeningCentres bad H u
  by_cases hS : S.Nonempty
  · let m : ℕ := S.min' hS
    have hmS : m ∈ S := Finset.min'_mem S hS
    have hmnear : |(m : ℝ) - u| ≤ (H : ℝ) := by
      exact (Finset.mem_filter.mp hmS).2
    have hsubset : S ⊆ Finset.Icc m (m + 2 * H) := by
      intro n hn
      have hmn : m ≤ n := Finset.min'_le S n hn
      have hnnear : |(n : ℝ) - u| ≤ (H : ℝ) := by
        exact (Finset.mem_filter.mp hn).2
      have hnupper : (n : ℝ) - u ≤ (H : ℝ) := (abs_le.mp hnnear).2
      have hmlower : -(H : ℝ) ≤ (m : ℝ) - u := (abs_le.mp hmnear).1
      have hreal : (n : ℝ) ≤ (m : ℝ) + 2 * (H : ℝ) := by
        linarith
      have hupper : n ≤ m + 2 * H := by
        exact_mod_cast hreal
      exact Finset.mem_Icc.mpr ⟨hmn, hupper⟩
    have hIcc : (Finset.Icc m (m + 2 * H)).card = 2 * H + 1 := by
      rw [Nat.card_Icc]
      omega
    have hcard := Finset.card_le_card hsubset
    rw [hIcc] at hcard
    exact hcard
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [S, hEmpty]

/-- Equivalent interval-membership formulation of the bounded-overlap theorem. -/
theorem integerThickeningInterval_overlap_card_le
    (bad : Finset ℕ) (H : ℕ) (u : ℝ) :
    (bad.filter fun n => u ∈ integerThickeningInterval n H).card ≤ 2 * H + 1 := by
  classical
  have hEq :
      bad.filter (fun n => u ∈ integerThickeningInterval n H) =
        integerThickeningCentres bad H u := by
    ext n
    simp [integerThickeningCentres, mem_integerThickeningInterval_iff]
  rw [hEq]
  exact integerThickeningCentres_card_le bad H u

/-- A literal finite thickening package separating the two geometric inputs to
the Lebesgue double count.

The `intervalSubset` field is exactly what the shift/symmetric-difference part
of the manuscript must prove.  Bounded overlap is *not* a field: it follows
from the integer-centre geometry above. -/
structure LiteralIntegerThickening
    (bad : Finset ℕ) (H : ℕ) where
  exceptionalSet : Set ℝ
  intervalSubset : ∀ n ∈ bad, integerThickeningInterval n H ⊆ exceptionalSet

/-- Outside the enlarged exceptional set no bad-centre thickening interval can
contain the point. -/
theorem LiteralIntegerThickening.no_centres_outside
    {bad : Finset ℕ} {H : ℕ}
    (geom : LiteralIntegerThickening bad H) {u : ℝ}
    (hu : u ∉ geom.exceptionalSet) :
    (bad.filter fun n => u ∈ integerThickeningInterval n H).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hmem := Finset.mem_filter.mp hn
  exact hu (geom.intervalSubset n hmem.1 hmem.2)

/-- The literal thickening package carries the manuscript's pointwise
multiplicity bound automatically. -/
theorem LiteralIntegerThickening.overlap_card_le
    {bad : Finset ℕ} {H : ℕ}
    (_geom : LiteralIntegerThickening bad H) (u : ℝ) :
    (bad.filter fun n => u ∈ integerThickeningInterval n H).card ≤ 2 * H + 1 := by
  exact integerThickeningInterval_overlap_card_le bad H u

end DivisorF
