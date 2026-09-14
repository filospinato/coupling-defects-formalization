import DivisorF.ExceptionalEndpointShiftLebesgue
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Quantitative shift bridge for Lemma 6.1

The manuscript proves whole-interval stability of a bad integer endpoint from
raw estimates of the form

`|Psi_eta(u) - Psi_eta(n)| << (H + 1) log Y`

and

`|u^eta - n^eta| << H Y^(eta - 1)`,

with `H` chosen as a sufficiently small multiple of `Y^eta / log Y`.

The previous `ExceptionalEndpointShiftStability` module consumed the already
normalised `delta / 8` versions of those estimates.  This module formalizes the
project-owned quantitative bookkeeping between the manuscript-shaped raw
majorants and that normalised interface.  In particular, the small-radius
choice is represented by scale-level budget inequalities, not by one
hypothesis for every centre and every nearby real point.

The final radius-normalisation layer below goes one step further: it separates
those budget inequalities into the two ingredients used literally in the
paper, namely a single sufficiently-small radius fraction and coefficient
bounds for the raw shift estimates.  The analytic estimates themselves remain
visible hypotheses; only the project's passage from them to whole-interval
stability is machine-checked here.
-/

namespace DivisorF

open scoped ENNReal

/-- Manuscript-shaped quantitative shift data at one dyadic scale.

`statisticMajorant` corresponds to the right side of (8), while
`mainMajorant` corresponds to the right side of (9).  `lowerScale` is a common
lower bound for the centre main terms (in the paper it is comparable to
`Y^eta`).  The two `...Budget` fields encode the single sufficiently-small
choice of the thickening radius. -/
structure IntegerExceptionalQuantitativeShiftData
    (bad : Finset ℕ) (H : ℕ)
    (A M : ℝ → ℝ) (delta : ℝ) where
  delta_nonneg : 0 ≤ delta
  lowerScale : ℝ
  lowerScale_nonneg : 0 ≤ lowerScale
  statisticMajorant : ℝ
  mainMajorant : ℝ
  statisticMajorant_nonneg : 0 ≤ statisticMajorant
  mainMajorant_nonneg : 0 ≤ mainMajorant
  main_nonneg : ∀ n ∈ bad, 0 ≤ M (n : ℝ)
  main_lower : ∀ n ∈ bad, lowerScale ≤ M (n : ℝ)
  badAtCentre : ∀ n ∈ bad, RealRelativeBad A M delta (n : ℝ)
  statisticShiftRaw : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    |A (n : ℝ) - A u| ≤ statisticMajorant
  mainShiftRaw : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    |M (n : ℝ) - M u| ≤ mainMajorant
  statisticBudget : statisticMajorant ≤ (delta / 8) * lowerScale
  mainBudget : mainMajorant ≤ (delta / 8) * lowerScale
  localScale : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    M u ≤ (3 / 2 : ℝ) * M (n : ℝ)

/-- The scale-level budget controls every centre because all centre main terms
are bounded below by the same `lowerScale`. -/
theorem IntegerExceptionalQuantitativeShiftData.statisticShift
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalQuantitativeShiftData bad H A M delta)
    {n : ℕ} (hn : n ∈ bad)
    {u : ℝ} (hu : u ∈ integerThickeningInterval n H) :
    |A (n : ℝ) - A u| ≤ (delta / 8) * M (n : ℝ) := by
  have hcoef : 0 ≤ delta / 8 :=
    div_nonneg data.delta_nonneg (by norm_num)
  have hlower :
      (delta / 8) * data.lowerScale ≤ (delta / 8) * M (n : ℝ) :=
    mul_le_mul_of_nonneg_left (data.main_lower n hn) hcoef
  exact (data.statisticShiftRaw n hn u hu).trans
    (data.statisticBudget.trans hlower)

/-- The same common scale converts the raw main-term majorant into the second
`delta / 8` estimate required by the whole-interval stability theorem. -/
theorem IntegerExceptionalQuantitativeShiftData.mainShift
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalQuantitativeShiftData bad H A M delta)
    {n : ℕ} (hn : n ∈ bad)
    {u : ℝ} (hu : u ∈ integerThickeningInterval n H) :
    |M (n : ℝ) - M u| ≤ (delta / 8) * M (n : ℝ) := by
  have hcoef : 0 ≤ delta / 8 :=
    div_nonneg data.delta_nonneg (by norm_num)
  have hlower :
      (delta / 8) * data.lowerScale ≤ (delta / 8) * M (n : ℝ) :=
    mul_le_mul_of_nonneg_left (data.main_lower n hn) hcoef
  exact (data.mainShiftRaw n hn u hu).trans
    (data.mainBudget.trans hlower)

/-- **Lemma 6.1 quantitative-shift reduction.**

Raw manuscript-shaped shift bounds plus one pair of scale-level radius budgets
produce exactly the `IntegerExceptionalShiftData` interface consumed by the
literal Lebesgue thickening layer. -/
theorem IntegerExceptionalQuantitativeShiftData.toShiftData
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalQuantitativeShiftData bad H A M delta) :
    IntegerExceptionalShiftData bad H A M delta where
  delta_nonneg := data.delta_nonneg
  main_nonneg := data.main_nonneg
  badAtCentre := data.badAtCentre
  statisticShift := by
    intro n hn u hu
    exact data.statisticShift hn hu
  mainShift := by
    intro n hn u hu
    exact data.mainShift hn hu
  localScale := data.localScale

/-- One-scale end-to-end form: the raw quantitative shift package, together
with the external half-error exceptional-set mass input, constructs the fixed
error real-to-integer thickening certificate. -/
noncomputable def fixedErrorRealThickeningCertificate_of_quantitativeShift
    {bad : Finset ℕ} {H Y k : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalQuantitativeShiftData bad H A M delta)
    (radiusLarge : 1 ≤ H)
    (exceptionalFinite :
      MeasureTheory.volume {u : ℝ | RealRelativeBad A M (delta / 2) u} ≠ ∞)
    (exceptionalMassSmall :
      MeasureTheory.volume.real
          {u : ℝ | RealRelativeBad A M (delta / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  exact fixedErrorRealThickeningCertificate_of_shiftStability
    data.toShiftData radiusLarge exceptionalFinite exceptionalMassSmall

/-- Family-level raw quantitative interface immediately upstream of the
manuscript's dyadic diagonalisation.  The external real-variable theorem enters
only through `exceptionalFinite` and `exceptionalMassSmall`; all shift
normalisation is project-owned and discharged here. -/
def FixedPrecisionQuantitativeShiftLebesgueBounds
    (E : ℕ → ℕ → Finset ℕ)
    (radius : ℕ → ℕ → ℕ)
    (A M : ℕ → ℕ → ℝ → ℝ)
    (delta : ℕ → ℝ)
    (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℕ, threshold k ≤ Y →
    let bad := E k Y
    let H := radius k Y
    ∃ _data : IntegerExceptionalQuantitativeShiftData
        bad H (A k Y) (M k Y) (delta k),
      1 ≤ H ∧
      MeasureTheory.volume
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} ≠ ∞ ∧
      MeasureTheory.volume.real
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- The raw quantitative family implies the already established shift/Lebesgue
family interface. -/
theorem fixedPrecisionShiftLebesgueBounds_of_quantitative
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (h : FixedPrecisionQuantitativeShiftLebesgueBounds
      E radius A M delta threshold) :
    FixedPrecisionShiftLebesgueBounds E radius A M delta threshold := by
  intro k hk Y hY
  dsimp [FixedPrecisionQuantitativeShiftLebesgueBounds] at h
  rcases h k hk Y hY with ⟨data, hH, hfinite, hmass⟩
  exact ⟨data.toShiftData, hH, hfinite, hmass⟩

/-- **Lemma 6.1 quantitative chain, global-window form.**

Once the manuscript's raw local shift estimates and scale-level radius budgets
are supplied at every fixed precision, the existing project-owned machinery
produces one global integer exceptional set whose arbitrary dyadic-scale
windows have relative density zero. -/
theorem eventuallySparseGlobalDyadicWindows_of_quantitativeShiftLebesgue
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (h : FixedPrecisionQuantitativeShiftLebesgueBounds
      E radius A M delta threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_shiftLebesgue hsupp
    (fixedPrecisionShiftLebesgueBounds_of_quantitative h)

/-!
## One-radius normalization

Equations (8)--(10) in the manuscript use one small radius choice for two
separate raw estimates.  The following package expresses exactly that
bookkeeping.  `statisticScale` and `mainScale` are the two scale factors left
after extracting their fixed constants; both are dominated by the same
`radiusFraction * lowerScale`.  Thus it is enough to choose the radius fraction
so that each fixed coefficient times that fraction is at most `delta / 8`.
-/

/-- Quantitative Lemma 6.1 data before the two `delta / 8` budgets have been
formed.  This is the formal counterpart of choosing the single constant
`c_delta` in `h = c_delta Y^eta / log Y` sufficiently small for both (8) and
(9). -/
structure IntegerExceptionalRadiusShiftData
    (bad : Finset ℕ) (H : ℕ)
    (A M : ℝ → ℝ) (delta : ℝ) where
  delta_nonneg : 0 ≤ delta
  lowerScale : ℝ
  lowerScale_nonneg : 0 ≤ lowerScale
  radiusFraction : ℝ
  radiusFraction_nonneg : 0 ≤ radiusFraction
  statisticScale : ℝ
  mainScale : ℝ
  statisticScale_nonneg : 0 ≤ statisticScale
  mainScale_nonneg : 0 ≤ mainScale
  statisticCoeff : ℝ
  mainCoeff : ℝ
  statisticCoeff_nonneg : 0 ≤ statisticCoeff
  mainCoeff_nonneg : 0 ≤ mainCoeff
  statisticScale_le : statisticScale ≤ radiusFraction * lowerScale
  mainScale_le : mainScale ≤ radiusFraction * lowerScale
  statisticCoeff_small : statisticCoeff * radiusFraction ≤ delta / 8
  mainCoeff_small : mainCoeff * radiusFraction ≤ delta / 8
  main_nonneg : ∀ n ∈ bad, 0 ≤ M (n : ℝ)
  main_lower : ∀ n ∈ bad, lowerScale ≤ M (n : ℝ)
  badAtCentre : ∀ n ∈ bad, RealRelativeBad A M delta (n : ℝ)
  statisticShiftRaw : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    |A (n : ℝ) - A u| ≤ statisticCoeff * statisticScale
  mainShiftRaw : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    |M (n : ℝ) - M u| ≤ mainCoeff * mainScale
  localScale : ∀ n ∈ bad, ∀ u ∈ integerThickeningInterval n H,
    M u ≤ (3 / 2 : ℝ) * M (n : ℝ)

/-- A single small-radius choice implies the statistic budget required by the
previous quantitative interface. -/
theorem IntegerExceptionalRadiusShiftData.statisticBudget
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalRadiusShiftData bad H A M delta) :
    data.statisticCoeff * data.statisticScale ≤
      (delta / 8) * data.lowerScale := by
  calc
    data.statisticCoeff * data.statisticScale ≤
        data.statisticCoeff * (data.radiusFraction * data.lowerScale) :=
      mul_le_mul_of_nonneg_left data.statisticScale_le
        data.statisticCoeff_nonneg
    _ = (data.statisticCoeff * data.radiusFraction) * data.lowerScale := by ring
    _ ≤ (delta / 8) * data.lowerScale :=
      mul_le_mul_of_nonneg_right data.statisticCoeff_small data.lowerScale_nonneg

/-- The same radius choice simultaneously implies the main-term budget. -/
theorem IntegerExceptionalRadiusShiftData.mainBudget
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalRadiusShiftData bad H A M delta) :
    data.mainCoeff * data.mainScale ≤
      (delta / 8) * data.lowerScale := by
  calc
    data.mainCoeff * data.mainScale ≤
        data.mainCoeff * (data.radiusFraction * data.lowerScale) :=
      mul_le_mul_of_nonneg_left data.mainScale_le data.mainCoeff_nonneg
    _ = (data.mainCoeff * data.radiusFraction) * data.lowerScale := by ring
    _ ≤ (delta / 8) * data.lowerScale :=
      mul_le_mul_of_nonneg_right data.mainCoeff_small data.lowerScale_nonneg

/-- The manuscript's one-radius package produces the already established
quantitative-shift interface, with no pointwise `delta / 8` assumptions. -/
def IntegerExceptionalRadiusShiftData.toQuantitativeShiftData
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalRadiusShiftData bad H A M delta) :
    IntegerExceptionalQuantitativeShiftData bad H A M delta where
  delta_nonneg := data.delta_nonneg
  lowerScale := data.lowerScale
  lowerScale_nonneg := data.lowerScale_nonneg
  statisticMajorant := data.statisticCoeff * data.statisticScale
  mainMajorant := data.mainCoeff * data.mainScale
  statisticMajorant_nonneg :=
    mul_nonneg data.statisticCoeff_nonneg data.statisticScale_nonneg
  mainMajorant_nonneg :=
    mul_nonneg data.mainCoeff_nonneg data.mainScale_nonneg
  main_nonneg := data.main_nonneg
  main_lower := data.main_lower
  badAtCentre := data.badAtCentre
  statisticShiftRaw := data.statisticShiftRaw
  mainShiftRaw := data.mainShiftRaw
  statisticBudget := data.statisticBudget
  mainBudget := data.mainBudget
  localScale := data.localScale

/-- The one-radius data therefore gives the normalized whole-interval shift
interface directly. -/
theorem IntegerExceptionalRadiusShiftData.toShiftData
    {bad : Finset ℕ} {H : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalRadiusShiftData bad H A M delta) :
    IntegerExceptionalShiftData bad H A M delta :=
  data.toQuantitativeShiftData.toShiftData

/-- One-scale end-to-end Lemma 6.1 reduction from a single small-radius choice
to the fixed-error real-to-integer thickening certificate. -/
noncomputable def fixedErrorRealThickeningCertificate_of_radiusShift
    {bad : Finset ℕ} {H Y k : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (data : IntegerExceptionalRadiusShiftData bad H A M delta)
    (radiusLarge : 1 ≤ H)
    (exceptionalFinite :
      MeasureTheory.volume {u : ℝ | RealRelativeBad A M (delta / 2) u} ≠ ∞)
    (exceptionalMassSmall :
      MeasureTheory.volume.real
          {u : ℝ | RealRelativeBad A M (delta / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  exact fixedErrorRealThickeningCertificate_of_quantitativeShift
    data.toQuantitativeShiftData radiusLarge exceptionalFinite exceptionalMassSmall

/-- Family-level form of the literal manuscript radius choice.  The same
`radiusFraction` at each fixed precision controls both raw shift estimates;
the external real-variable input still appears only through finiteness and
smallness of the half-error exceptional set. -/
def FixedPrecisionRadiusShiftLebesgueBounds
    (E : ℕ → ℕ → Finset ℕ)
    (radius : ℕ → ℕ → ℕ)
    (A M : ℕ → ℕ → ℝ → ℝ)
    (delta : ℕ → ℝ)
    (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℕ, threshold k ≤ Y →
    let bad := E k Y
    let H := radius k Y
    ∃ _data : IntegerExceptionalRadiusShiftData
        bad H (A k Y) (M k Y) (delta k),
      1 ≤ H ∧
      MeasureTheory.volume
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} ≠ ∞ ∧
      MeasureTheory.volume.real
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- A family of one-radius packages implies the quantitative family already
consumed by the global exceptional-set construction. -/
theorem fixedPrecisionQuantitativeShiftLebesgueBounds_of_radius
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (h : FixedPrecisionRadiusShiftLebesgueBounds
      E radius A M delta threshold) :
    FixedPrecisionQuantitativeShiftLebesgueBounds
      E radius A M delta threshold := by
  intro k hk Y hY
  dsimp [FixedPrecisionRadiusShiftLebesgueBounds] at h
  rcases h k hk Y hY with ⟨data, hH, hfinite, hmass⟩
  exact ⟨data.toQuantitativeShiftData, hH, hfinite, hmass⟩

/-- **Lemma 6.1 radius-normalised global-window chain.**

Once the two raw manuscript estimates are controlled by one sufficiently
small radius choice at every fixed precision, the existing project-owned
thickening, finite-overlap, diagonalisation, and global-window machinery gives
a single sparse integer exceptional set. -/
theorem eventuallySparseGlobalDyadicWindows_of_radiusShiftLebesgue
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (h : FixedPrecisionRadiusShiftLebesgueBounds
      E radius A M delta threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_quantitativeShiftLebesgue hsupp
    (fixedPrecisionQuantitativeShiftLebesgueBounds_of_radius h)

end DivisorF
