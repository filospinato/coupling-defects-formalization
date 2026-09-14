import DivisorF.ExceptionalEndpointThickeningGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lebesgue mass layer for the exceptional-endpoint thickening

This module continues the project-owned real-to-integer discretisation in
Lemma 6.1.  The preceding geometry module proves the pointwise overlap bound
for the literal intervals `[n-H,n+H]`.  Here we make the Lebesgue-mass side
literal as well:

* every radius-`H` interval has real volume exactly `2H`;
* the total interval mass over a finite bad set is exactly `2H * #bad`;
* the union of the bad-centre intervals is contained in the enlarged
  exceptional set supplied by `LiteralIntegerThickening`;
* hence the real volume of that union is bounded by the exceptional-set mass;
* once the standard finite-overlap measure inequality is supplied, these
  literal data instantiate the existing `FixedErrorRealThickeningCertificate`.

The remaining support bridge is therefore exactly the standard measure fact
turning the already-proved pointwise multiplicity bound `≤ 2H+1` into

`sum_n volume I_n ≤ (2H+1) * volume (⋃ n, I_n)`.

No analytic prime theorem is formalized here.
-/

namespace DivisorF

open MeasureTheory
open scoped ENNReal

/-- The literal union of all radius-`H` intervals centred at the finite bad
integer set. -/
def integerThickeningUnion (bad : Finset ℕ) (H : ℕ) : Set ℝ :=
  ⋃ n ∈ bad, integerThickeningInterval n H

/-- A radius-`H` interval centred at an integer has Lebesgue mass exactly
`2H`, expressed using the real-valued projection of Lebesgue measure. -/
theorem volume_real_integerThickeningInterval (n H : ℕ) :
    volume.real (integerThickeningInterval n H) = 2 * (H : ℝ) := by
  rw [integerThickeningInterval, Real.volume_real_Icc_of_le]
  · ring
  · have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    linarith

/-- Summing the masses of the literal thickening intervals counts exactly
`2H` units of Lebesgue mass per bad integer centre. -/
theorem sum_volume_real_integerThickeningInterval
    (bad : Finset ℕ) (H : ℕ) :
    ∑ n ∈ bad, volume.real (integerThickeningInterval n H) =
      (2 * (H : ℝ)) * bad.card := by
  simp [volume_real_integerThickeningInterval, mul_comm, mul_left_comm]

/-- Every individual thickening interval is contained in the literal union. -/
theorem integerThickeningInterval_subset_union
    {bad : Finset ℕ} {H n : ℕ} (hn : n ∈ bad) :
    integerThickeningInterval n H ⊆ integerThickeningUnion bad H := by
  intro u hu
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn, hu⟩⟩

/-- The literal thickening package puts the whole union of bad-centre intervals
inside the enlarged exceptional set. -/
theorem LiteralIntegerThickening.union_subset_exceptionalSet
    {bad : Finset ℕ} {H : ℕ}
    (geom : LiteralIntegerThickening bad H) :
    integerThickeningUnion bad H ⊆ geom.exceptionalSet := by
  intro u hu
  rcases Set.mem_iUnion.mp hu with ⟨n, hu⟩
  rcases Set.mem_iUnion.mp hu with ⟨hn, hu⟩
  exact geom.intervalSubset n hn hu

/-- Consequently the Lebesgue volume of the literal union is bounded by the
volume of the enlarged exceptional set. -/
theorem LiteralIntegerThickening.volume_union_le_exceptionalSet
    {bad : Finset ℕ} {H : ℕ}
    (geom : LiteralIntegerThickening bad H) :
    volume (integerThickeningUnion bad H) ≤ volume geom.exceptionalSet := by
  exact measure_mono geom.union_subset_exceptionalSet

/-- Real-valued version of the previous monotonicity statement, convenient for
feeding the real-valued fixed-error certificate once finiteness of the enlarged
exceptional set is known. -/
theorem LiteralIntegerThickening.volume_real_union_le_exceptionalSet
    {bad : Finset ℕ} {H : ℕ}
    (geom : LiteralIntegerThickening bad H)
    (hfinite : volume geom.exceptionalSet ≠ ∞) :
    volume.real (integerThickeningUnion bad H) ≤ volume.real geom.exceptionalSet := by
  exact measureReal_mono geom.union_subset_exceptionalSet hfinite

/-- Literal finite-error data immediately upstream of the existing thickening
certificate.  The `finiteOverlapMeasure` field is intentionally the one
standard measure-theoretic bridge still isolated from the project-owned
geometry; all arithmetic and containment data are now concrete.

`exceptionalMassSmall` is the external real exceptional-mass estimate at the
requested fixed precision, after the manuscript's harmless enlargement to
adjacent dyadic blocks. -/
structure LiteralLebesgueThickeningData
    (bad : Finset ℕ) (H Y k : ℕ) where
  geom : LiteralIntegerThickening bad H
  radiusLarge : 1 ≤ H
  exceptionalFinite : volume geom.exceptionalSet ≠ ∞
  finiteOverlapMeasure :
    (∑ n ∈ bad, volume.real (integerThickeningInterval n H)) ≤
      ((2 * H + 1 : ℕ) : ℝ) * volume.real (integerThickeningUnion bad H)
  exceptionalMassSmall :
    volume.real geom.exceptionalSet * (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- **Literal Lebesgue thickening → fixed-error certificate.**

Once the standard finite-overlap measure inequality is available, the literal
integer-centred thickening geometry and the real exceptional-mass estimate
produce exactly the certificate consumed by the rest of Lemma 6.1.  In
particular, no prime-counting statement or analytic theorem is hidden in this
constructor. -/
noncomputable def fixedErrorRealThickeningCertificate_of_literalLebesgue
    {bad : Finset ℕ} {H Y k : ℕ}
    (data : LiteralLebesgueThickeningData bad H Y k) :
    FixedErrorRealThickeningCertificate bad Y k := by
  let M : ℝ := volume.real data.geom.exceptionalSet
  have hsum :
      (2 * (H : ℝ)) * (bad.card : ℝ) ≤
        ((2 * H + 1 : ℕ) : ℝ) * volume.real (integerThickeningUnion bad H) := by
    rw [← sum_volume_real_integerThickeningInterval bad H]
    exact data.finiteOverlapMeasure
  have hunion :
      volume.real (integerThickeningUnion bad H) ≤ M := by
    exact data.geom.volume_real_union_le_exceptionalSet data.exceptionalFinite
  have hcoef : 0 ≤ (((2 * H + 1 : ℕ) : ℝ)) := by positivity
  have hdouble :
      (2 * (H : ℝ)) * (bad.card : ℝ) ≤
        (2 * (H : ℝ) + 1) * M := by
    calc
      (2 * (H : ℝ)) * (bad.card : ℝ)
          ≤ ((2 * H + 1 : ℕ) : ℝ) *
              volume.real (integerThickeningUnion bad H) := hsum
      _ ≤ ((2 * H + 1 : ℕ) : ℝ) * M :=
        mul_le_mul_of_nonneg_left hunion hcoef
      _ = (2 * (H : ℝ) + 1) * M := by norm_num
  refine
    { h := (H : ℝ)
      exceptionalMass := M
      hLarge := ?_
      exceptionalMass_nonneg := measureReal_nonneg
      doubleCount := hdouble
      exceptionalMassSmall := ?_ }
  · exact_mod_cast data.radiusLarge
  · simpa [M] using data.exceptionalMassSmall

end DivisorF
