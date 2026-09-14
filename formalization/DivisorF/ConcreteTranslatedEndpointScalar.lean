import DivisorF.ConcreteTranslatedEndpoint
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Scalar bounds for the concrete translated endpoint

Section 6 uses the actual gap

`H_eta(X) = X - nu_eta(X)`

with `nu_eta(X)=floor(X-3X^eta)`.  The previous concrete translated-endpoint
layer still asked for `RegularEndpointScalarBounds` on this gap as one packaged
hypothesis.  This module reduces that package to the two scalar inequalities
that are proved from `rho < eta < 1-rho` in the manuscript.

The floor contributes less than one unit.  Consequently

`H_eta(X) <= ceil(3 X^eta + 1)`.

Thus quotient placement follows from a single width comparison against this
explicit power radius, while cutoff inactivity is the same square comparison
already isolated in `RegularEndpointScalar`.  Prime-richness remains a separate
external-input interface.
-/

namespace DivisorF

/-- Explicit integer radius dominating the true translated-endpoint gap. -/
noncomputable def concreteTranslatedEndpointRadius (eta : ℝ) (X : ℕ) : ℕ :=
  ⌈3 * (X : ℝ) ^ eta + 1⌉₊

/-- The exact floor formula gives
`X - nu_eta(X) <= ceil(3 X^eta + 1)` whenever `g_eta(X)` is nonnegative. -/
theorem concreteTranslatedEndpointGap_le_radius
    {eta : ℝ} {X : ℕ}
    (_hnonneg : 0 ≤ translatedEndpointReal eta X) :
    concreteTranslatedEndpointGap eta X ≤
      concreteTranslatedEndpointRadius eta X := by
  have hpow : 0 ≤ (X : ℝ) ^ eta := Real.rpow_nonneg (by positivity) eta
  have hupper : translatedEndpointReal eta X ≤ (X : ℝ) := by
    dsimp [translatedEndpointReal]
    linarith
  have hmapX : translatedEndpointMap eta X ≤ X :=
    translatedEndpointMap_le_endpoint hupper
  have hfloorSucc :
      translatedEndpointReal eta X <
        ((translatedEndpointMap eta X : ℕ) : ℝ) + 1 := by
    simpa [translatedEndpointMap] using
      (Nat.lt_floor_add_one (translatedEndpointReal eta X))
  have hgapReal :
      ((concreteTranslatedEndpointGap eta X : ℕ) : ℝ) <
        3 * (X : ℝ) ^ eta + 1 := by
    dsimp [concreteTranslatedEndpointGap]
    rw [Nat.cast_sub hmapX]
    dsimp [translatedEndpointReal] at hfloorSucc
    linarith
  have hradiusReal :
      3 * (X : ℝ) ^ eta + 1 ≤
        ((concreteTranslatedEndpointRadius eta X : ℕ) : ℝ) := by
    exact Nat.le_ceil _
  have hcast :
      ((concreteTranslatedEndpointGap eta X : ℕ) : ℝ) ≤
        ((concreteTranslatedEndpointRadius eta X : ℕ) : ℝ) :=
    (le_of_lt hgapReal).trans hradiusReal
  exact_mod_cast hcast

/-- The same exact floor estimate locates the translated integer endpoint at
least `X-radius`.  This is the finite lower-location half of the manuscript's
`J_eta(X) ⊂ (X-O(X^eta),X)` statement. -/
theorem endpoint_sub_radius_le_translatedEndpointMap
    {eta : ℝ} {X : ℕ}
    (hnonneg : 0 ≤ translatedEndpointReal eta X) :
    X - concreteTranslatedEndpointRadius eta X ≤ translatedEndpointMap eta X := by
  have hpow : 0 ≤ (X : ℝ) ^ eta := Real.rpow_nonneg (by positivity) eta
  have hupper : translatedEndpointReal eta X ≤ (X : ℝ) := by
    dsimp [translatedEndpointReal]
    linarith
  have hmapX : translatedEndpointMap eta X ≤ X :=
    translatedEndpointMap_le_endpoint hupper
  have hgap := concreteTranslatedEndpointGap_le_radius
    (eta := eta) (X := X) hnonneg
  dsimp [concreteTranslatedEndpointGap] at hgap
  omega

/-- Combining the explicit radius lower location with the already proved upper
location of the actual `J_eta(X)` packet yields one concrete finite interval
containing every prime in that packet. -/
theorem concreteTranslatedEndpointPrimePacket_mem_interval
    {eta : ℝ} {X p : ℕ}
    (heta : 0 < eta)
    (hnonneg : 0 ≤ translatedEndpointReal eta X)
    (hp : p ∈ concreteTranslatedEndpointPrimePacket eta X) :
    X - concreteTranslatedEndpointRadius eta X < p ∧ p ≤ X := by
  have hpow : 0 ≤ (X : ℝ) ^ eta := Real.rpow_nonneg (by positivity) eta
  have hupper : translatedEndpointReal eta X ≤ (X : ℝ) := by
    dsimp [translatedEndpointReal]
    linarith
  have hlower := endpoint_sub_radius_le_translatedEndpointMap
    (eta := eta) (X := X) hnonneg
  have hpacketUpper := concreteTranslatedEndpoint_upper_le
    (eta := eta) (X := X) heta hnonneg hupper
  rcases mem_concreteTranslatedEndpointPrimePacket.mp hp with ⟨_, hleft, hright⟩
  constructor
  · exact lt_of_le_of_lt hlower hleft
  · exact hright.trans hpacketUpper

/-- The concrete scalar package follows from an explicit power-radius width
bound and the already isolated square cutoff bound. -/
theorem regularEndpointScalarBounds_of_concreteTranslatedEndpointRadius
    {eta : ℝ} {X K : ℕ}
    (hnonneg : 0 ≤ translatedEndpointReal eta X)
    (hwidth :
      (K + 1) * concreteTranslatedEndpointRadius eta X ≤ X + 1)
    (hsquare : K * (X + 1) ≤ (X / 2) * (X / 2)) :
    RegularEndpointScalarBounds X K (concreteTranslatedEndpointGap eta X) := by
  have hgap := concreteTranslatedEndpointGap_le_radius (eta := eta) (X := X) hnonneg
  refine ⟨Nat.sub_le _ _, ?_, hsquare⟩
  exact (Nat.mul_le_mul_left (K + 1) hgap).trans hwidth

/-- Eventual form of the two explicit scalar comparisons left after the true
gap is substituted. -/
def EventuallyConcreteTranslatedEndpointRadiusBounds
    (eta : ℝ) (K : ℕ → ℕ) : Prop :=
  ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    0 ≤ translatedEndpointReal eta X ∧
    (K X + 1) * concreteTranslatedEndpointRadius eta X ≤ X + 1 ∧
    K X * (X + 1) ≤ (X / 2) * (X / 2)

/-- The explicit radius comparisons discharge the concrete
`RegularEndpointScalarBounds` uniformly on the eventual tail. -/
theorem eventuallyRegularEndpointScalarBounds_of_concreteRadius
    {eta : ℝ} {K : ℕ → ℕ}
    (hscalar : EventuallyConcreteTranslatedEndpointRadiusBounds eta K) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      RegularEndpointScalarBounds X (K X)
        (concreteTranslatedEndpointGap eta X) := by
  rcases hscalar with ⟨X₀, hscalar⟩
  refine ⟨X₀, ?_⟩
  intro X hX
  rcases hscalar X hX with ⟨hnonneg, hwidth, hsquare⟩
  exact regularEndpointScalarBounds_of_concreteTranslatedEndpointRadius
    hnonneg hwidth hsquare

/-- Prime-richness of the actual translated packet, kept separate from the
project-owned endpoint arithmetic. -/
def EventuallyConcreteTranslatedEndpointPrimeRich
    (eta : ℝ) (K : ℕ → ℕ) (E : ℕ → Finset ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E Y →
      ∀ s ∈ Finset.Icc 2 (K X),
        2 * (s - 1) < (concreteTranslatedEndpointPrimePacket eta X).card

/-- Radius bounds plus prime-richness produce the exact concrete endpoint data
consumed by the downstream Section 6 zero-defect machinery. -/
theorem eventuallyConcreteTranslatedEndpointData_of_radiusBounds
    {eta : ℝ} {K : ℕ → ℕ} {E : ℕ → Finset ℕ}
    (hscalar : EventuallyConcreteTranslatedEndpointRadiusBounds eta K)
    (hprime : EventuallyConcreteTranslatedEndpointPrimeRich eta K E) :
    EventuallyConcreteTranslatedEndpointData eta K E := by
  rcases eventuallyRegularEndpointScalarBounds_of_concreteRadius hscalar with
    ⟨Xs, hscalar⟩
  rcases hprime with ⟨Yp, hprime⟩
  refine ⟨max Xs Yp, ?_⟩
  intro Y hY X hXY hXE
  have hXsY : Xs ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hYpY : Yp ≤ Y := le_trans (Nat.le_max_right _ _) hY
  have hYX : Y ≤ X := (Finset.mem_Ico.mp hXY).1
  refine ⟨hscalar X (hXsY.trans hYX), ?_⟩
  exact hprime Y hYpY X hXY hXE

/-- End-to-end Section 6 weighted-density transfer after replacing the abstract
true-gap scalar package by the explicit power-radius comparisons.  The
paper-shaped `g_eta` bounds and prime-richness remain visible hypotheses. -/
theorem weightedRelativeDensityZero_of_concreteTranslatedEndpoint_radiusBounds
    {eta : ℝ} {K : ℕ → ℕ} {E : ℕ → Finset ℕ} {W : ℕ → ℕ}
    (heta : 0 < eta)
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta)
    (hscalar : EventuallyConcreteTranslatedEndpointRadiusBounds eta K)
    (hprime : EventuallyConcreteTranslatedEndpointPrimeRich eta K E)
    (hweight : EventuallyEndpointWeightBound K W)
    (hsmall : EventuallyNegligibleBadEndpointBurden K E W) :
    WeightedRelativeDensityZero K := by
  exact weightedRelativeDensityZero_of_concreteTranslatedEndpoint
    heta hpaper
    (eventuallyConcreteTranslatedEndpointData_of_radiusBounds hscalar hprime)
    hweight hsmall

end DivisorF
