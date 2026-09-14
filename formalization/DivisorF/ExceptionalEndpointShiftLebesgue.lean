import DivisorF.ExceptionalEndpointShiftStability
import DivisorF.ExceptionalEndpointFiniteOverlap
import DivisorF.ExceptionalEndpointThickeningGlobal

set_option linter.style.header false

/-!
# Shift-stable Lebesgue thickening certificate

This module composes the project-owned real-to-integer argument in Lemma 6.1:

* `IntegerExceptionalShiftData` turns the manuscript's symmetric-difference
  and main-term shift estimates into containment of every bad-centre interval
  in the half-error real exceptional set;
* `ExceptionalEndpointFiniteOverlap` integrates the machine-checked pointwise
  overlap bound for the literal integer-centred intervals;
* the external almost-all prime theorem remains represented only through the
  smallness/finiteness of the enlarged half-error exceptional set.

Thus finite-overlap measure control is no longer an explicit hypothesis of the
shift-stable certificate or its family-level interface.
-/

namespace DivisorF

open scoped ENNReal

open MeasureTheory

/-- **Lemma 6.1 shift stability → fixed-error real thickening certificate.**

Once the two manuscript shift estimates are available uniformly throughout
all radius-`H` intervals around the bad integer centres, their whole intervals
lie in the half-error exceptional set.  The finite-overlap measure inequality
is now derived automatically from the literal integer-centre geometry, so the
remaining real-variable input here is only finiteness and sufficiently small
mass of that exceptional set. -/
noncomputable def fixedErrorRealThickeningCertificate_of_shiftStability
    {bad : Finset ℕ} {H Y k : ℕ}
    {A M : ℝ → ℝ} {delta : ℝ}
    (shift : IntegerExceptionalShiftData bad H A M delta)
    (radiusLarge : 1 ≤ H)
    (exceptionalFinite :
      volume {u : ℝ | RealRelativeBad A M (delta / 2) u} ≠ ∞)
    (exceptionalMassSmall :
      volume.real {u : ℝ | RealRelativeBad A M (delta / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)) :
    FixedErrorRealThickeningCertificate bad Y k := by
  let geom : LiteralIntegerThickening bad H :=
    shift.toLiteralIntegerThickening
  apply fixedErrorRealThickeningCertificate_of_literalFiniteOverlap
    (bad := bad) (H := H) (Y := Y) (k := k) geom radiusLarge
  · simpa [geom, IntegerExceptionalShiftData.toLiteralIntegerThickening] using
      exceptionalFinite
  · simpa [geom, IntegerExceptionalShiftData.toLiteralIntegerThickening] using
      exceptionalMassSmall

/-- Family-level form used immediately before the manuscript's dyadic
 diagonalisation.  It records the actual shift-stability data rather than an
 opaque real-to-integer certificate.  The finite-overlap inequality is absent
because it is now a theorem of the literal thickening geometry. -/
def FixedPrecisionShiftLebesgueBounds
    (E : ℕ → ℕ → Finset ℕ)
    (radius : ℕ → ℕ → ℕ)
    (A M : ℕ → ℕ → ℝ → ℝ)
    (delta : ℕ → ℝ)
    (threshold : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Y : ℕ, threshold k ≤ Y →
    let bad := E k Y
    let H := radius k Y
    ∃ _shift : IntegerExceptionalShiftData bad H (A k Y) (M k Y) (delta k),
      1 ≤ H ∧
      volume
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} ≠ ∞ ∧
      volume.real
          {u : ℝ |
            RealRelativeBad (A k Y) (M k Y) (delta k / 2) u} *
          (2 * (k : ℝ)) ≤ (Y : ℝ)

/-- The explicit shift/Lebesgue family discharges the certificate interface
already consumed by all later parts of Lemma 6.1. -/
theorem fixedPrecisionRealThickeningBounds_of_shiftLebesgue
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (h : FixedPrecisionShiftLebesgueBounds E radius A M delta threshold) :
    FixedPrecisionRealThickeningBounds E threshold := by
  intro k hk Y hY
  dsimp [FixedPrecisionShiftLebesgueBounds] at h
  rcases h k hk Y hY with
    ⟨shift, hH, hfinite, hmass⟩
  exact ⟨fixedErrorRealThickeningCertificate_of_shiftStability
    shift hH hfinite hmass⟩

/-- End-to-end project-owned discretisation downstream of the real exceptional
mass input: explicit shift-stable Lebesgue data imply one global integer
exceptional set whose arbitrary `[Y,2Y)` windows have relative density zero. -/
theorem eventuallySparseGlobalDyadicWindows_of_shiftLebesgue
    {E : ℕ → ℕ → Finset ℕ}
    {radius : ℕ → ℕ → ℕ}
    {A M : ℕ → ℕ → ℝ → ℝ}
    {delta : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (hsupp : FixedPrecisionExceptionalSupport E)
    (h : FixedPrecisionShiftLebesgueBounds E radius A M delta threshold) :
    EventuallySparseGlobalDyadicWindows
      (globalDiagonalExceptionalSet E threshold) := by
  exact eventuallySparseGlobalDyadicWindows_of_realThickening hsupp
    (fixedPrecisionRealThickeningBounds_of_shiftLebesgue h)

end DivisorF
