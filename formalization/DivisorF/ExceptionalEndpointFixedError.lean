import DivisorF.ExceptionalEndpointHalfScale

set_option linter.style.header false

/-!
# Final fixed-error interface for the project-owned part of Lemma 6.1

The manuscript chooses, for each fixed relative error, one constant radius
fraction `c_delta` and then works for all sufficiently large dyadic scales.
`ExceptionalEndpointHalfScale` already proves that the resulting concrete
integer radius is eventually at most half the dyadic scale.  This module turns
that eventual theorem into the interface actually consumed by the fixed-error
discretisation.

The important trust-boundary point is that the standard additive estimate

`|u^eta - n^eta| << H * Y^(eta-1)`

is *not* promoted to a project theorem.  It remains visible as `mainShiftRaw`,
just like the analytic von-Mangoldt/symmetric-difference majorant remains
visible as `statisticShiftRaw`.  What is discharged here is the paper's own
bookkeeping from these local estimates to the integer exceptional set.
-/

namespace DivisorF

open scoped ENNReal

/-- The fixed exponent/radius regime used by the manuscript at one error level.
The threshold is chosen from the already-proved eventual half-scale theorem. -/
structure ManuscriptRadiusRegime (eta radiusFraction : ℝ) where
  eta_nonneg : 0 ≤ eta
  eta_lt_one : eta < 1
  radiusFraction_nonneg : 0 ≤ radiusFraction
  radiusFraction_le_one : radiusFraction ≤ 1

/-- A canonical threshold after which the concrete manuscript radius satisfies
`2H <= Y`. -/
noncomputable def ManuscriptRadiusRegime.halfScaleThreshold
    {eta radiusFraction : ℝ}
    (regime : ManuscriptRadiusRegime eta radiusFraction) : ℕ :=
  Classical.choose
    (eventually_manuscriptPowerIntegerRadius_two_mul_le
      regime.eta_nonneg regime.eta_lt_one
      regime.radiusFraction_nonneg regime.radiusFraction_le_one)

/-- The defining property of `halfScaleThreshold`. -/
theorem ManuscriptRadiusRegime.radius_two_mul_le
    {eta radiusFraction : ℝ}
    (regime : ManuscriptRadiusRegime eta radiusFraction)
    {Y : ℕ}
    (hY : regime.halfScaleThreshold ≤ Y)
    (hlog : 1 ≤ Real.log (Y : ℝ)) :
    2 * manuscriptPowerIntegerRadius Y eta radiusFraction ≤ Y := by
  exact (Classical.choose_spec
    (eventually_manuscriptPowerIntegerRadius_two_mul_le
      regime.eta_nonneg regime.eta_lt_one
      regime.radiusFraction_nonneg regime.radiusFraction_le_one)) Y hY hlog

/-- Fixed-error data in the literal manuscript regime.

Compared with `IntegerExceptionalIntegerRadiusPowerMainData`, the caller no
longer supplies the half-scale inequality.  Compared with the earlier
automatic-half-scale finite package, it no longer supplies a one-scale power
domination witness either: sufficiently-large `Y` is expressed by the single
canonical threshold above.

The two raw local shift bounds remain explicit supporting/analytic inputs. -/
structure IntegerExceptionalFixedErrorData
    (bad : Finset ℕ) (Y : ℕ)
    (A : ℝ → ℝ) (delta eta radiusFraction : ℝ)
    (regime : ManuscriptRadiusRegime eta radiusFraction) where
  aboveHalfScaleThreshold : regime.halfScaleThreshold ≤ Y
  delta_nonneg : 0 ≤ delta
  Y_pos : 1 ≤ Y
  log_large : 1 ≤ Real.log (Y : ℝ)
  radiusFloorLarge :
    2 ≤ ⌊radiusFraction * manuscriptPowerRadiusScale Y eta⌋₊
  support_lower : ∀ n ∈ bad, Y ≤ n
  statisticCoeff : ℝ
  statisticCoeff_nonneg : 0 ≤ statisticCoeff
  mainCoeff : ℝ
  mainCoeff_nonneg : 0 ≤ mainCoeff
  statisticCoeff_small : statisticCoeff * radiusFraction ≤ delta / 8
  mainCoeff_small : mainCoeff * radiusFraction ≤ delta / 8
  badAtCentre : ∀ n ∈ bad,
    RealRelativeBad A (fun x => x ^ eta) delta (n : ℝ)
  statisticShiftRaw : ∀ n ∈ bad,
    ∀ u ∈ integerThickeningInterval n
      (manuscriptPowerIntegerRadius Y eta radiusFraction),
      |A (n : ℝ) - A u| ≤
        statisticCoeff *
          ((((manuscriptPowerIntegerRadius Y eta radiusFraction : ℕ) : ℝ) + 1) *
            Real.log (Y : ℝ))
  mainShiftRaw : ∀ n ∈ bad,
    ∀ u ∈ integerThickeningInterval n
      (manuscriptPowerIntegerRadius Y eta radiusFraction),
      |(n : ℝ) ^ eta - u ^ eta| ≤
        mainCoeff *
          (((manuscriptPowerIntegerRadius Y eta radiusFraction : ℕ) : ℝ) *
            manuscriptPowerVariationScale Y eta)

/-- The final fixed-error manuscript package specializes the existing literal
power-main transfer. -/
def IntegerExceptionalFixedErrorData.toPowerMainData
    {bad : Finset ℕ} {Y : ℕ}
    {A : ℝ → ℝ} {delta eta radiusFraction : ℝ}
    {regime : ManuscriptRadiusRegime eta radiusFraction}
    (data : IntegerExceptionalFixedErrorData
      bad Y A delta eta radiusFraction regime) :
    IntegerExceptionalIntegerRadiusPowerMainData bad Y A delta eta where
  delta_nonneg := data.delta_nonneg
  eta_nonneg := regime.eta_nonneg
  eta_le_one := le_of_lt regime.eta_lt_one
  Y_pos := data.Y_pos
  log_large := data.log_large
  radiusFraction := radiusFraction
  radiusFraction_nonneg := regime.radiusFraction_nonneg
  radiusFloorLarge := data.radiusFloorLarge
  radiusHalfScale :=
    regime.radius_two_mul_le data.aboveHalfScaleThreshold data.log_large
  support_lower := data.support_lower
  statisticCoeff := data.statisticCoeff
  statisticCoeff_nonneg := data.statisticCoeff_nonneg
  mainCoeff := data.mainCoeff
  mainCoeff_nonneg := data.mainCoeff_nonneg
  statisticCoeff_small := data.statisticCoeff_small
  mainCoeff_small := data.mainCoeff_small
  badAtCentre := data.badAtCentre
  statisticShiftRaw := data.statisticShiftRaw
  mainShiftRaw := data.mainShiftRaw

/-- **Lemma 6.1, fixed-error project-owned transfer.**

At one fixed error level, once the two local shift estimates and the external
smallness of the half-error real exceptional set are supplied, all remaining
radius geometry, whole-interval stability, finite-overlap Lebesgue counting and
integer counting are discharged by the formalization. -/
noncomputable def fixedErrorRealThickeningCertificate_of_manuscript
    {bad : Finset ℕ} {Y k : ℕ}
    {A : ℝ → ℝ} {delta eta radiusFraction : ℝ}
    {regime : ManuscriptRadiusRegime eta radiusFraction}
    (data : IntegerExceptionalFixedErrorData
      bad Y A delta eta radiusFraction regime)
    (exceptionalFinite :
      MeasureTheory.volume
        {u : ℝ | RealRelativeBad A (fun x => x ^ eta) (delta / 2) u} ≠ ∞)
    (exceptionalMassSmall :
      MeasureTheory.volume.real
          {u : ℝ | RealRelativeBad A (fun x => x ^ eta) (delta / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  exact fixedErrorRealThickeningCertificate_of_integerRadius_powerMain
    data.toPowerMainData exceptionalFinite exceptionalMassSmall

/-- Fixed-precision family interface with one fixed exponent/radius fraction at
each precision level and a threshold already beyond the canonical half-scale
threshold.  This is the paper-shaped input to the dyadic diagonalisation. -/
def FixedPrecisionManuscriptDiscretisationBounds
    (E : ℕ → ℕ → Finset ℕ)
    (radiusFraction : ℕ → ℝ)
    (A : ℕ → ℕ → ℝ → ℝ)
    (delta eta : ℕ → ℝ)
    (regime : ∀ k, ManuscriptRadiusRegime (eta k) (radiusFraction k))
    (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (regime k).halfScaleThreshold ≤ threshold k ∧
    ∀ Y : ℕ, threshold k ≤ Y →
      let bad := E k Y
      ∃ _data : IntegerExceptionalFixedErrorData
          bad Y (A k Y) (delta k) (eta k) (radiusFraction k) (regime k),
        MeasureTheory.volume
            {u : ℝ |
              RealRelativeBad (A k Y) (fun x => x ^ eta k) (delta k / 2) u} ≠ ∞ ∧
        MeasureTheory.volume.real
            {u : ℝ |
              RealRelativeBad (A k Y) (fun x => x ^ eta k) (delta k / 2) u} *
            (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- The final manuscript family specializes the earlier power-main family. -/
theorem fixedPrecisionIntegerRadiusPowerMainShiftLebesgueBounds_of_manuscript
    {E : ℕ → ℕ → Finset ℕ}
    {radiusFraction : ℕ → ℝ}
    {A : ℕ → ℕ → ℝ → ℝ}
    {delta eta : ℕ → ℝ}
    {regime : ∀ k, ManuscriptRadiusRegime (eta k) (radiusFraction k)}
    {threshold : ℕ → ℕ}
    (h : FixedPrecisionManuscriptDiscretisationBounds
      E radiusFraction A delta eta regime threshold) :
    FixedPrecisionIntegerRadiusPowerMainShiftLebesgueBounds
      E (fun k _ => radiusFraction k) A delta eta threshold := by
  intro k hk Y hY
  dsimp [FixedPrecisionManuscriptDiscretisationBounds] at h
  rcases h k hk with ⟨hthreshold, hfamily⟩
  rcases hfamily Y hY with ⟨data, hfinite, hmass⟩
  have habove : (regime k).halfScaleThreshold ≤ Y := hthreshold.trans hY
  have data' : IntegerExceptionalFixedErrorData
      (E k Y) Y (A k Y) (delta k) (eta k) (radiusFraction k) (regime k) :=
    { data with aboveHalfScaleThreshold := habove }
  exact ⟨data'.toPowerMainData, rfl, hfinite, hmass⟩

/-- **Lemma 6.1 project-owned discretisation chain, final family form.**

The conclusion is the single global integer exceptional set sparse in arbitrary
dyadic windows.  Upstream remain only the two manuscript local estimates and
the real exceptional-set measure input carried by
`FixedPrecisionManuscriptDiscretisationBounds`; all discrete thickening,
overlap, diagonal and global-window steps are project-owned and discharged. -/
theorem eventuallySparseGlobalDyadicWindows_of_manuscriptDiscretisation
    {E : ℕ → ℕ → Finset ℕ}
    {radiusFraction : ℕ → ℝ}
    {A : ℕ → ℕ → ℝ → ℝ}
    {delta eta : ℕ → ℝ}
    {regime : ∀ k, ManuscriptRadiusRegime (eta k) (radiusFraction k)}
    {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (h : FixedPrecisionManuscriptDiscretisationBounds
      E radiusFraction A delta eta regime threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_integerRadius_powerMain hsupp
    (fixedPrecisionIntegerRadiusPowerMainShiftLebesgueBounds_of_manuscript h)

end DivisorF
