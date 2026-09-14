import DivisorF.ExceptionalEndpointMultiplicity
import DivisorF.WeightedRelativeDensity

set_option linter.style.header false

/-!
# Eventual regular-endpoint package for Section 6

The previous modules prove the finite arithmetic of a translated prime-rich
interval and the finite `o(Y)` pullback mechanism.  This file connects those
pieces to the existing weighted-density layer.

No external prime theorem is asserted.  The only analytic input is packaged as
an eventual family of shifted prime packets over nonexceptional endpoints.  All
quotient-interval placement, large-prime cutoff, multiplicity-to-defect, and
weighted exceptional-set counting are then project-owned Lean theorems.
-/

namespace DivisorF

/-- Eventual finite data produced by the manuscript's regular-endpoint
construction.  For every sufficiently large dyadic scale and every endpoint
outside `E Y`, there is one shifted prime-rich interval `(a X,a X+L X]` whose
location and cardinality work simultaneously for all types `2 ≤ s ≤ K X`.

The concrete Section 6 instantiation uses `a X = nu_eta(X)` and
`L X = floor (nu_eta(X)^eta)`. -/
def EventuallyShiftedRegularEndpointData
    (K H a L : ℕ → ℕ) (E : ℕ → Finset ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E Y →
      H X ≤ X ∧
      (K X + 1) * H X ≤ X + 1 ∧
      X - H X ≤ a X ∧
      a X + L X ≤ X ∧
      (∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X (K X) →
        Real.sqrt (N : ℝ) < (X / 2 : ℕ)) ∧
      (∀ s ∈ Finset.Icc 2 (K X),
        2 * (s - 1) < (shiftedPrimePacket (a X) (L X)).card)

/-- **Section 6 simultaneous regular-endpoint theorem, eventual form.**

Once the translated `J_eta` data are available outside the bad endpoints,
every admissible quotient pair over every sufficiently large good endpoint has
zero defect.  This is the project-owned implication between the analytic
regular-endpoint input and the graph-theoretic defect conclusion. -/
theorem eventuallyZeroOutsideBadEndpoints_of_shiftedRegularEndpointData
    {K H a L : ℕ → ℕ} {E : ℕ → Finset ℕ}
    (hreg : EventuallyShiftedRegularEndpointData K H a L E) :
    EventuallyZeroOutsideBadEndpoints K E := by
  rcases hreg with ⟨Y₀, hreg⟩
  refine ⟨Y₀, ?_⟩
  intro Y hY X hXY hXE s hs N hblock
  have hdata := hreg Y hY X hXY hXE
  have hpair : (N, s) ∈ endpointPairSpace X (K X) := by
    apply Finset.mem_biUnion.mpr
    exact ⟨s, hs, hblock⟩
  exact endpointPairSpace_zero_of_shifted_prime_packet_arithmetic
    (X := X) (K := K X) (H := H X) (a := a X) (L := L X)
    hdata.1
    hdata.2.1
    hdata.2.2.2.2.1
    hdata.2.2.1
    hdata.2.2.2.1
    hdata.2.2.2.2.2
    hpair

/-- Eventual endpoint-weight bound plus shifted regular-endpoint data gives the
finite weighted exceptional-set estimate uniformly on all sufficiently large
dyadic scales. -/
theorem eventuallyPositiveDefectWeightedPairs_card_le_bad_mul
    {K H a L : ℕ → ℕ} {E : ℕ → Finset ℕ} {W : ℕ → ℕ}
    (hreg : EventuallyShiftedRegularEndpointData K H a L E)
    (hweight : EventuallyEndpointWeightBound K W) :
    ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      (positiveDefectWeightedPairs Y K).card ≤ (E Y).card * W Y := by
  have hzero := eventuallyZeroOutsideBadEndpoints_of_shiftedRegularEndpointData hreg
  rcases hzero with ⟨Yzero, hzero⟩
  rcases hweight with ⟨Yweight, hweight⟩
  refine ⟨max Yzero Yweight, ?_⟩
  intro Y hY
  have hYzero : Yzero ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hYweight : Yweight ≤ Y := le_trans (Nat.le_max_right _ _) hY
  exact positiveDefectWeightedPairs_card_le_bad_card_mul
    (hzero Y hYzero) (hweight Y hYweight)

/-- **Section 6 density transfer from translated regular endpoints.**

The shifted regular-endpoint construction supplies zero defect off `E`; if the
weighted burden of `E` is negligible, the positive-defect pairs have relative
weighted density zero.  This theorem makes the trust boundary explicit:
prime-richness and exceptional-set sparsity are hypotheses, while every
subsequent transfer is machine-checked. -/
theorem weightedRelativeDensityZero_of_shiftedRegularEndpointData
    {K H a L : ℕ → ℕ} {E : ℕ → Finset ℕ} {W : ℕ → ℕ}
    (hreg : EventuallyShiftedRegularEndpointData K H a L E)
    (hweight : EventuallyEndpointWeightBound K W)
    (hsmall : EventuallyNegligibleBadEndpointBurden K E W) :
    WeightedRelativeDensityZero K := by
  exact weightedRelativeDensityZero_of_negligible_bad_endpoints
    (eventuallyZeroOutsideBadEndpoints_of_shiftedRegularEndpointData hreg)
    hweight hsmall

/-- Convenience composition for the manuscript's translated exceptional set.
If `Eint Y` is the sparse integer exceptional family and the irregular endpoint
family is its bounded-multiplicity pullback through `nu`, then the pullback is
dyadically sparse.  This theorem is deliberately separate from the weighted
burden estimate: the latter also needs the endpoint-weight and total-mass
bounds already formalized elsewhere. -/
theorem shiftedBadEndpoints_eventuallyDyadicallySparse
    {ν : ℕ → ℕ} {Eint : ℕ → Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M)
    (hint : EventuallyDyadicallySparse Eint)
    (hpull : EventuallyBoundedExceptionalPullback ν Eint M) :
    EventuallyDyadicallySparse
      (fun Y => pulledBackBadEndpoints Y ν (Eint Y)) :=
  eventuallyDyadicallySparse_pulledBack_of_boundedMultiplicity hM hint hpull

/-- Stronger convenience form matching the actual manuscript proof: it is
enough to bound each finite fibre of the translated map.  The counting factor
`M` is then derived, rather than assumed as an already-aggregated pullback
estimate. -/
theorem shiftedBadEndpoints_eventuallyDyadicallySparse_of_fibre_bound
    {ν : ℕ → ℕ} {Eint : ℕ → Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M)
    (hint : EventuallyDyadicallySparse Eint)
    (hfibre : EventuallyBoundedTranslatedEndpointFibres ν Eint M) :
    EventuallyDyadicallySparse
      (fun Y => pulledBackBadEndpoints Y ν (Eint Y)) :=
  eventuallyDyadicallySparse_pulledBack_of_fibre_bound hM hint hfibre

end DivisorF
