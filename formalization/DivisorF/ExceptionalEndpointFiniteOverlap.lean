import DivisorF.ExceptionalEndpointLebesgue
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-overlap Lebesgue double counting

This module closes the standard measure-theoretic support bridge in the
project-owned real-to-integer discretisation of Lemma 6.1.

`ExceptionalEndpointThickeningGeometry` already proves pointwise that at most
`2H+1` radius-`H` intervals centred at bad integers can contain a given real
point. Integrating the sum of their indicator functions gives the literal
finite-overlap inequality

`sum_n volume I_n <= (2H+1) * volume (union_n I_n)`.

The argument below is standard measure theory used only to connect the
project's concrete thickening geometry to its existing certificate interface;
it is not an additional mathematical target and uses no analytic prime input.
-/

namespace DivisorF

open scoped ENNReal

/-- Membership in a real thickening interval is classically decidable; naming
one instance keeps every filter below on the same decision procedure. -/
noncomputable local instance memIntegerThickeningIntervalDecidablePred'
    (u : ℝ) (H : ℕ) :
    DecidablePred fun n : ℕ => u ∈ integerThickeningInterval n H :=
  fun _ => Classical.dec _

open MeasureTheory

private theorem measurableSet_integerThickeningInterval (n H : ℕ) :
    MeasurableSet (integerThickeningInterval n H) := by
  simp [integerThickeningInterval]

private theorem measurableSet_integerThickeningUnion (bad : Finset ℕ) (H : ℕ) :
    MeasurableSet (integerThickeningUnion bad H) := by
  classical
  rw [integerThickeningUnion]
  exact Finset.measurableSet_biUnion bad fun n _ =>
    measurableSet_integerThickeningInterval n H

private theorem sum_indicator_integerThickeningInterval_eq_card
    (bad : Finset ℕ) (H : ℕ) (u : ℝ) :
    (∑ n ∈ bad,
      (integerThickeningInterval n H).indicator
        (fun _ : ℝ => (1 : ℝ≥0∞)) u) =
      ((bad.filter fun n => u ∈ integerThickeningInterval n H).card : ℝ≥0∞) := by
  classical
  induction bad using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, ih, Finset.filter_insert]
      by_cases hu : u ∈ integerThickeningInterval a H
      · rw [if_pos hu, Set.indicator_of_mem hu,
          Finset.card_insert_of_notMem
            (fun hmem => ha (Finset.mem_filter.mp hmem).1)]
        push_cast
        ring
      · rw [if_neg hu]
        simp [hu]

/-- Pointwise indicator version of the already-proved integer-centre overlap
bound. Outside the literal union the two sides are both zero; inside the union
the coefficient `2H+1` dominates the number of active intervals. -/
theorem sum_indicator_integerThickeningInterval_le
    (bad : Finset ℕ) (H : ℕ) (u : ℝ) :
    (∑ n ∈ bad,
      (integerThickeningInterval n H).indicator
        (fun _ : ℝ => (1 : ℝ≥0∞)) u) ≤
      (((2 * H + 1 : ℕ) : ℝ≥0∞) *
        (integerThickeningUnion bad H).indicator
          (fun _ : ℝ => (1 : ℝ≥0∞)) u) := by
  classical
  rw [sum_indicator_integerThickeningInterval_eq_card]
  by_cases hu : u ∈ integerThickeningUnion bad H
  · simp only [Set.indicator_of_mem hu, mul_one]
    exact_mod_cast integerThickeningInterval_overlap_card_le bad H u
  · have hfilter :
        bad.filter (fun n => u ∈ integerThickeningInterval n H) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnbad, hnu⟩
      exact hu (integerThickeningInterval_subset_union hnbad hnu)
    simp [hu, hfilter]

/-- **Integrated finite-overlap inequality.**

The sum of the Lebesgue masses of the radius-`H` intervals centred at `bad` is
at most `2H+1` times the mass of their union. This is the standard integration
step behind the manuscript's bounded-overlap double count. -/
theorem sum_volume_integerThickeningInterval_le
    (bad : Finset ℕ) (H : ℕ) :
    (∑ n ∈ bad, volume (integerThickeningInterval n H)) ≤
      ((2 * H + 1 : ℕ) : ℝ≥0∞) *
        volume (integerThickeningUnion bad H) := by
  classical
  let c : ℝ≥0∞ := ((2 * H + 1 : ℕ) : ℝ≥0∞)
  have hmeasInterval : ∀ n ∈ bad,
      Measurable
        ((integerThickeningInterval n H).indicator
          (fun _ : ℝ => (1 : ℝ≥0∞))) := by
    intro n _
    exact Measurable.indicator measurable_const
      (measurableSet_integerThickeningInterval n H)
  have hmeasUnion : MeasurableSet (integerThickeningUnion bad H) :=
    measurableSet_integerThickeningUnion bad H
  calc
    (∑ n ∈ bad, volume (integerThickeningInterval n H)) =
        ∑ n ∈ bad,
          ∫⁻ u : ℝ,
            (integerThickeningInterval n H).indicator
              (fun _ : ℝ => (1 : ℝ≥0∞)) u ∂volume := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (lintegral_indicator_one
        (measurableSet_integerThickeningInterval n H)).symm
    _ = ∫⁻ u : ℝ,
        ∑ n ∈ bad,
          (integerThickeningInterval n H).indicator
            (fun _ : ℝ => (1 : ℝ≥0∞)) u ∂volume := by
      symm
      exact lintegral_finsetSum bad hmeasInterval
    _ ≤ ∫⁻ u : ℝ,
        c * (integerThickeningUnion bad H).indicator
          (fun _ : ℝ => (1 : ℝ≥0∞)) u ∂volume := by
      apply lintegral_mono
      intro u
      exact sum_indicator_integerThickeningInterval_le bad H u
    _ = c * ∫⁻ u : ℝ,
        (integerThickeningUnion bad H).indicator
          (fun _ : ℝ => (1 : ℝ≥0∞)) u ∂volume := by
      rw [lintegral_const_mul c]
      exact Measurable.indicator measurable_const hmeasUnion
    _ = c * volume (integerThickeningUnion bad H) := by
      congr 1
      exact lintegral_indicator_one hmeasUnion
    _ = ((2 * H + 1 : ℕ) : ℝ≥0∞) *
        volume (integerThickeningUnion bad H) := rfl

/-- Real-valued form of the finite-overlap inequality. Finiteness of an
enlarged exceptional set suffices because the literal union is contained in
that set. -/
theorem LiteralIntegerThickening.finiteOverlapMeasure
    {bad : Finset ℕ} {H : ℕ}
    (geom : LiteralIntegerThickening bad H)
    (exceptionalFinite : volume geom.exceptionalSet ≠ ∞) :
    (∑ n ∈ bad, volume.real (integerThickeningInterval n H)) ≤
      ((2 * H + 1 : ℕ) : ℝ) *
        volume.real (integerThickeningUnion bad H) := by
  have hunion : volume (integerThickeningUnion bad H) ≠ ∞ :=
    ne_top_of_le_ne_top exceptionalFinite geom.volume_union_le_exceptionalSet
  have hcoef : (((2 * H + 1 : ℕ) : ℝ≥0∞)) ≠ ∞ := ENNReal.natCast_ne_top _
  have hright :
      (((2 * H + 1 : ℕ) : ℝ≥0∞) *
        volume (integerThickeningUnion bad H)) ≠ ∞ :=
    ENNReal.mul_ne_top hcoef hunion
  have hinterval : ∀ n ∈ bad,
      volume (integerThickeningInterval n H) ≠ ∞ := by
    intro n _
    simp [integerThickeningInterval]
  have hleft :
      (∑ n ∈ bad, volume (integerThickeningInterval n H)) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr hinterval
  have hreal :
      (∑ n ∈ bad, volume (integerThickeningInterval n H)).toReal ≤
        (((2 * H + 1 : ℕ) : ℝ≥0∞) *
          volume (integerThickeningUnion bad H)).toReal :=
    (ENNReal.toReal_le_toReal hleft hright).2
      (sum_volume_integerThickeningInterval_le bad H)
  rw [ENNReal.toReal_sum hinterval, ENNReal.toReal_mul,
    ENNReal.toReal_natCast] at hreal
  simpa [Measure.real] using hreal

/-- Literal thickening geometry plus the external exceptional-mass estimate now
construct the fixed-error certificate without any extra finite-overlap
hypothesis. -/
noncomputable def fixedErrorRealThickeningCertificate_of_literalFiniteOverlap
    {bad : Finset ℕ} {H Y k : ℕ}
    (geom : LiteralIntegerThickening bad H)
    (radiusLarge : 1 ≤ H)
    (exceptionalFinite : volume geom.exceptionalSet ≠ ∞)
    (exceptionalMassSmall :
      volume.real geom.exceptionalSet * (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  apply fixedErrorRealThickeningCertificate_of_literalLebesgue
    (bad := bad) (H := H) (Y := Y) (k := k)
  exact
    { geom := geom
      radiusLarge := radiusLarge
      exceptionalFinite := exceptionalFinite
      finiteOverlapMeasure := geom.finiteOverlapMeasure exceptionalFinite
      exceptionalMassSmall := exceptionalMassSmall }

end DivisorF
