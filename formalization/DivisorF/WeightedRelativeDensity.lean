import DivisorF.WeightedPairDensity

set_option linter.style.header false

/-!
# Relative weighted density for Section 6

This module packages the project-original asymptotic logic behind Corollary 6.3
without formalizing the external almost-all prime theorem.  The natural
weighted pair space and the finite exceptional-endpoint estimate are already
formalized in `WeightedPairDensity`.

Rather than importing topological little-o machinery merely to express a ratio
of finite cardinalities, we use an equivalent reciprocal-integer formulation:
positive-defect pairs have relative density zero when, for every integer
`C >= 1`, their cardinality is eventually at most `1/C` of the whole weighted
pair space.  This form keeps all denominator-zero and coercion issues out of the
statement and is exactly what the manuscript's `o(Y) * O(Y^(2 rho))` argument
supplies after finite counting.

The external Gafni--Tao input is represented only through the hypothesis that
the weighted burden of exceptional endpoints is eventually negligible.
-/

namespace DivisorF

/-- Reciprocal-integer formulation of relative density zero in the natural
weighted quotient-pair space.  For every precision `1/C`, positive-defect
pairs eventually occupy at most that fraction of the whole space. -/
def WeightedRelativeDensityZero (K : ℕ → ℕ) : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    (positiveDefectWeightedPairs Y K).card * C ≤
      (weightedPairSpace Y K).card

/-- Eventually every admissible pair above an endpoint outside the designated
exceptional set has zero defect.  This is the discrete conclusion supplied by
the regular-endpoint transfer once the external prime input has produced the
good endpoints. -/
def EventuallyZeroOutsideBadEndpoints
    (K : ℕ → ℕ) (E : ℕ → Finset ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E Y →
      ∀ s ∈ Finset.Icc 2 (K X),
        ∀ N : ℕ, (N, s) ∈ quotientBlockPairs X s →
          paperTypeDefect N s = 0

/-- Eventual uniform bound on the natural total pair weight carried by one
endpoint in a dyadic block.  In the manuscript `W(Y)` is of order
`Y^(2 rho)`. -/
def EventuallyEndpointWeightBound
    (K : ℕ → ℕ) (W : ℕ → ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    ∀ X ∈ Finset.Ico Y (2 * Y),
      endpointPairWeight (K X) ≤ W Y

/-- The exceptional endpoints have negligible *weighted burden* relative to
the whole pair space.  This is the exact project-owned counting interface for
the manuscript's input `|E ∩ [Y,2Y)| = o(Y)` together with the endpoint-weight
and total-space estimates.

For every reciprocal precision `1/C`, the crude exceptional contribution
`|E(Y)| * W(Y)` is eventually at most `1/C` of the full weighted pair space. -/
def EventuallyNegligibleBadEndpointBurden
    (K : ℕ → ℕ) (E : ℕ → Finset ℕ) (W : ℕ → ℕ) : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    (E Y).card * W Y * C ≤ (weightedPairSpace Y K).card

/-- **Section 6 relative weighted-density transfer.**

If all sufficiently large admissible pairs above nonexceptional endpoints have
zero defect, endpoint weights admit a uniform dyadic bound, and the resulting
exceptional weighted burden is negligible, then positive-defect pairs have
relative density zero in the natural weighted pair space.

No prime-distribution theorem is asserted: Gafni--Tao (plus the manuscript's
integer discretisation) is needed only to discharge the three explicit input
interfaces above. -/
theorem weightedRelativeDensityZero_of_negligible_bad_endpoints
    {K : ℕ → ℕ} {E : ℕ → Finset ℕ} {W : ℕ → ℕ}
    (hzero : EventuallyZeroOutsideBadEndpoints K E)
    (hweight : EventuallyEndpointWeightBound K W)
    (hsmall : EventuallyNegligibleBadEndpointBurden K E W) :
    WeightedRelativeDensityZero K := by
  rcases hzero with ⟨Yzero, hzero⟩
  rcases hweight with ⟨Yweight, hweight⟩
  intro C hC
  rcases hsmall C hC with ⟨Ysmall, hsmall⟩
  refine ⟨max Yzero (max Yweight Ysmall), ?_⟩
  intro Y hY
  have hYzero : Yzero ≤ Y :=
    le_trans (Nat.le_max_left _ _) hY
  have hYweight : Yweight ≤ Y :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hY
  have hYsmall : Ysmall ≤ Y :=
    le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hY
  have hfinite :
      (positiveDefectWeightedPairs Y K).card ≤ (E Y).card * W Y :=
    positiveDefectWeightedPairs_card_le_bad_card_mul
      (hzero Y hYzero) (hweight Y hYweight)
  calc
    (positiveDefectWeightedPairs Y K).card * C
        ≤ ((E Y).card * W Y) * C := Nat.mul_le_mul_right C hfinite
    _ ≤ (weightedPairSpace Y K).card := hsmall Y hYsmall

/-- Finite one-scale form of the same relative-density mechanism.  It is often
convenient when an external argument has already produced a concrete bad set
and a concrete endpoint-weight bound at one dyadic scale. -/
theorem positiveDefectWeightedPairs_card_mul_le_total
    {Y W C : ℕ} {K : ℕ → ℕ} {E : Finset ℕ}
    (hzero :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ s ∈ Finset.Icc 2 (K X),
          ∀ N : ℕ, (N, s) ∈ quotientBlockPairs X s →
            paperTypeDefect N s = 0)
    (hweight :
      ∀ X ∈ Finset.Ico Y (2 * Y), endpointPairWeight (K X) ≤ W)
    (hsmall : E.card * W * C ≤ (weightedPairSpace Y K).card) :
    (positiveDefectWeightedPairs Y K).card * C ≤
      (weightedPairSpace Y K).card := by
  have hfinite :
      (positiveDefectWeightedPairs Y K).card ≤ E.card * W :=
    positiveDefectWeightedPairs_card_le_bad_card_mul hzero hweight
  exact le_trans (Nat.mul_le_mul_right C hfinite) hsmall

end DivisorF
