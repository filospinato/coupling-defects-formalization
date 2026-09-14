import DivisorF.TranslatedEndpointPaperBounds
import DivisorF.RegularEndpointScalar
import DivisorF.RegularEndpointAsymptotic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Concrete `nu_eta / J_eta` endpoint data for Section 6

The preceding translated-endpoint modules deliberately kept the shifted interval
`(a,a+L]` abstract while formalizing quotient placement and weighted-density
transfers.  This file instantiates that interval with the actual Section 6
objects

`a = nu_eta(X) = floor (X - 3 X^eta)`,
`L = floor (nu_eta(X)^eta)`.

It also chooses the natural gap `H = X - nu_eta(X)`.  Once the manuscript's
eventual scalar bounds for `g_eta` hold, the concrete packet automatically lies
below `X`; its left endpoint is automatically `X-H`.  Thus the remaining
endpoint arithmetic is reduced to `RegularEndpointScalarBounds` for this actual
gap and to the prime-richness of the actual `J_eta(X)` packet.

No almost-all prime theorem is asserted here.  Prime-richness and exceptional
endpoint sparsity remain explicit hypotheses/interfaces.
-/

namespace DivisorF

/-- The exact integer length `floor (nu_eta(X)^eta)` used in `J_eta(X)`. -/
noncomputable def concreteTranslatedEndpointLength (eta : ℝ) (X : ℕ) : ℕ :=
  ⌊((translatedEndpointMap eta X : ℕ) : ℝ) ^ eta⌋₊

/-- The actual finite prime packet `J_eta(X)` from Section 6. -/
noncomputable def concreteTranslatedEndpointPrimePacket (eta : ℝ) (X : ℕ) : Finset ℕ :=
  shiftedPrimePacket (translatedEndpointMap eta X)
    (concreteTranslatedEndpointLength eta X)

/-- The exact distance from the endpoint `X` to its translated integer
endpoint `nu_eta(X)`. -/
noncomputable def concreteTranslatedEndpointGap (eta : ℝ) (X : ℕ) : ℕ :=
  X - translatedEndpointMap eta X

@[simp]
theorem mem_concreteTranslatedEndpointPrimePacket
    {eta : ℝ} {X p : ℕ} :
    p ∈ concreteTranslatedEndpointPrimePacket eta X ↔
      Nat.Prime p ∧ translatedEndpointMap eta X < p ∧
        p ≤ translatedEndpointMap eta X + concreteTranslatedEndpointLength eta X := by
  simp [concreteTranslatedEndpointPrimePacket]

/-- If the real translated endpoint is nonnegative and no larger than `X`, then
its natural floor is no larger than `X`. -/
theorem translatedEndpointMap_le_endpoint
    {eta : ℝ} {X : ℕ}
    (hupper : translatedEndpointReal eta X ≤ (X : ℝ)) :
    translatedEndpointMap eta X ≤ X := by
  exact Nat.floor_le_of_le hupper

/-- The concrete upper endpoint of `J_eta(X)` is at most `X` under the
paper-shaped bounds.  This is the finite form of the easy half of
`J_eta(X) ⊂ (X-4X^eta,X)`.

The proof uses only the exact formula `g_eta(X)=X-3X^eta`, positivity of `eta`,
and the two elementary floor inequalities. -/
theorem concreteTranslatedEndpoint_upper_le
    {eta : ℝ} {X : ℕ}
    (heta : 0 < eta)
    (hnonneg : 0 ≤ translatedEndpointReal eta X)
    (hupper : translatedEndpointReal eta X ≤ (X : ℝ)) :
    translatedEndpointMap eta X + concreteTranslatedEndpointLength eta X ≤ X := by
  have hmapReal :
      ((translatedEndpointMap eta X : ℕ) : ℝ) ≤ translatedEndpointReal eta X := by
    exact Nat.floor_le hnonneg
  have hmapX : ((translatedEndpointMap eta X : ℕ) : ℝ) ≤ (X : ℝ) :=
    hmapReal.trans hupper
  have hrpow :
      (((translatedEndpointMap eta X : ℕ) : ℝ) ^ eta) ≤ (X : ℝ) ^ eta := by
    exact Real.rpow_le_rpow (by positivity) hmapX (le_of_lt heta)
  have hlenReal :
      ((concreteTranslatedEndpointLength eta X : ℕ) : ℝ) ≤
        (((translatedEndpointMap eta X : ℕ) : ℝ) ^ eta) := by
    exact Nat.floor_le (Real.rpow_nonneg (by positivity) eta)
  have hpowNonneg : 0 ≤ (X : ℝ) ^ eta :=
    Real.rpow_nonneg (by positivity) eta
  have hsumReal :
      ((translatedEndpointMap eta X + concreteTranslatedEndpointLength eta X : ℕ) : ℝ)
        ≤ (X : ℝ) := by
    push_cast
    dsimp [translatedEndpointReal] at hmapReal
    linarith
  exact_mod_cast hsumReal

/-- Under the paper-shaped bounds, the actual shifted packet has the exact
finite location needed by the translated-endpoint transfer when the radius is
taken to be the true gap `X-nu_eta(X)`. -/
theorem concreteTranslatedEndpoint_location_of_paperBounds
    {eta : ℝ}
    (heta : 0 < eta)
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      X - concreteTranslatedEndpointGap eta X ≤ translatedEndpointMap eta X ∧
      translatedEndpointMap eta X + concreteTranslatedEndpointLength eta X ≤ X := by
  rcases hpaper with ⟨X₀, hpaper⟩
  refine ⟨X₀, ?_⟩
  intro X hX
  have hp := hpaper X hX
  have hnonneg : 0 ≤ translatedEndpointReal eta X := by
    linarith [hp.1]
  have hmapX : translatedEndpointMap eta X ≤ X :=
    translatedEndpointMap_le_endpoint hp.2.2.2.2
  constructor
  · dsimp [concreteTranslatedEndpointGap]
    omega
  · exact concreteTranslatedEndpoint_upper_le heta hnonneg hp.2.2.2.2

/-- Eventual regular-endpoint data after instantiating all shifted-interval
parameters with the actual Section 6 objects.  Only two substantive inputs
remain at each good endpoint:

* the scalar cone inequalities for the true gap `X-nu_eta(X)`;
* enough ordinary primes in the actual `J_eta(X)` packet.

The second item is where the external almost-all prime theorem, after the
project-owned integer discretisation, enters. -/
def EventuallyConcreteTranslatedEndpointData
    (eta : ℝ) (K : ℕ → ℕ) (E : ℕ → Finset ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E Y →
      RegularEndpointScalarBounds X (K X) (concreteTranslatedEndpointGap eta X) ∧
      (∀ s ∈ Finset.Icc 2 (K X),
        2 * (s - 1) < (concreteTranslatedEndpointPrimePacket eta X).card)

/-- The concrete `nu_eta/J_eta` package implies the abstract shifted regular
endpoint data consumed by the existing Section 6 density machinery.  In
particular, the old abstract functions `H,a,L` are now instantiated with the
actual manuscript quantities rather than being additional hypotheses. -/
theorem eventuallyShiftedRegularEndpointData_of_concreteTranslatedEndpoint
    {eta : ℝ} {K : ℕ → ℕ} {E : ℕ → Finset ℕ}
    (heta : 0 < eta)
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta)
    (hdata : EventuallyConcreteTranslatedEndpointData eta K E) :
    EventuallyShiftedRegularEndpointData K
      (concreteTranslatedEndpointGap eta)
      (translatedEndpointMap eta)
      (concreteTranslatedEndpointLength eta) E := by
  rcases hpaper with ⟨Xp, hpaper⟩
  rcases hdata with ⟨Yd, hdata⟩
  refine ⟨max Xp Yd, ?_⟩
  intro Y hY X hXY hXE
  have hXpY : Xp ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hYdY : Yd ≤ Y := le_trans (Nat.le_max_right _ _) hY
  have hYX : Y ≤ X := (Finset.mem_Ico.mp hXY).1
  have hXpX : Xp ≤ X := hXpY.trans hYX
  have hp := hpaper X hXpX
  have hnonneg : 0 ≤ translatedEndpointReal eta X := by
    linarith [hp.1]
  have hmapX : translatedEndpointMap eta X ≤ X :=
    translatedEndpointMap_le_endpoint hp.2.2.2.2
  rcases hdata Y hYdY X hXY hXE with ⟨hscalar, hcard⟩
  rcases hscalar with ⟨hgapX, hwidth, hsquare⟩
  refine ⟨hgapX, hwidth, ?_, ?_, ?_, ?_⟩
  · dsimp [concreteTranslatedEndpointGap]
    omega
  · exact concreteTranslatedEndpoint_upper_le heta hnonneg hp.2.2.2.2
  · exact endpointPairSpace_sqrt_lt_half_of_scalar_square_bound hsquare
  · simpa [concreteTranslatedEndpointPrimePacket] using hcard

/-- Concrete simultaneous zero-defect transfer over all sufficiently large good
endpoints.  The theorem exposes exactly the remaining scalar/prime inputs and
then reuses the already formalized quotient and defect machinery. -/
theorem eventuallyZeroOutsideBadEndpoints_of_concreteTranslatedEndpoint
    {eta : ℝ} {K : ℕ → ℕ} {E : ℕ → Finset ℕ}
    (heta : 0 < eta)
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta)
    (hdata : EventuallyConcreteTranslatedEndpointData eta K E) :
    EventuallyZeroOutsideBadEndpoints K E := by
  exact eventuallyZeroOutsideBadEndpoints_of_shiftedRegularEndpointData
    (eventuallyShiftedRegularEndpointData_of_concreteTranslatedEndpoint
      heta hpaper hdata)

/-- Concrete weighted-density consequence for the actual `J_eta` packet.  All
post-prime-input bookkeeping is project-owned and machine-checkable; exceptional
set sparsity and prime richness remain explicit rather than being hidden as
axioms. -/
theorem weightedRelativeDensityZero_of_concreteTranslatedEndpoint
    {eta : ℝ} {K : ℕ → ℕ} {E : ℕ → Finset ℕ} {W : ℕ → ℕ}
    (heta : 0 < eta)
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta)
    (hdata : EventuallyConcreteTranslatedEndpointData eta K E)
    (hweight : EventuallyEndpointWeightBound K W)
    (hsmall : EventuallyNegligibleBadEndpointBurden K E W) :
    WeightedRelativeDensityZero K := by
  exact weightedRelativeDensityZero_of_shiftedRegularEndpointData
    (eventuallyShiftedRegularEndpointData_of_concreteTranslatedEndpoint
      heta hpaper hdata)
    hweight hsmall

end DivisorF
