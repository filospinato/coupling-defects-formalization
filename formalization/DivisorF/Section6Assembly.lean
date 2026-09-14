import DivisorF.ExceptionalEndpointConcreteDiagonal
import DivisorF.RegularEndpointPrimeThreshold
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Section 6 end-to-end regular-endpoint assembly

The project-owned parts of Lemma 6.1 and Theorem 6.2 are developed in separate
modules: fixed-precision exceptional sets are diagonalised and pulled back
through the actual translated endpoint map, while a single prime-packet
cardinality bound is transferred simultaneously to every quotient type in the
power cutoff.

This module records the missing composition.  It deliberately keeps the two
analytic inputs visible:

* the fixed-precision exceptional-set bounds supplied after the real-variable
  theorem and standard local shift estimates;
* eventual dominance of the concrete translated prime packet over
  `2 * floor(X^rho)`, supplied by the integer prime-count asymptotic.

Everything between those inputs and the sparse zero-defect endpoint package is
project-owned bookkeeping from Section 6.
-/

namespace DivisorF

/-- The actual irregular endpoint family obtained by diagonalising the integer
exceptional sets and pulling them back through the manuscript map `nu_eta`. -/
noncomputable def section6TranslatedBadEndpoints
    (eta : ℝ) (E : ℕ → ℕ → Finset ℕ) (threshold : ℕ → ℕ) (Y : ℕ) : Finset ℕ :=
  pulledBackBadEndpoints Y (translatedEndpointMap eta)
    (diagonalExceptionalEndpoints E threshold Y)

/-- The project-owned regular-endpoint output needed before the weighted
counting step: the very same endpoint family is dyadically sparse and supports
zero defect for every quotient type in the canonical power cutoff. -/
def Section6RegularEndpointPackage
    (rho eta : ℝ) (E : ℕ → ℕ → Finset ℕ) (threshold : ℕ → ℕ) : Prop :=
  EventuallyDyadicallySparse (section6TranslatedBadEndpoints eta E threshold) ∧
    EventuallyZeroOutsideBadEndpoints (regularEndpointPowerCutoff rho)
      (section6TranslatedBadEndpoints eta E threshold)

/-- **Lemma 6.1 + Theorem 6.2, project-owned assembly.**

For `0 < rho < eta < 1-rho`, fixed-precision integer exceptional estimates
produce a dyadically sparse family of irregular translated endpoints.  If the
actual packet `J_eta(X)` eventually contains more than
`2 * floor(X^rho)` ordinary primes outside that same family, then every
quotient pair above a regular endpoint has zero defect throughout the full
power cutoff.

The conclusion uses one and the same exceptional family in both clauses; this
is the semantic link required by the manuscript before passing to the weighted
relative-density corollary. -/
theorem section6RegularEndpointPackage_of_fixedPrecision_and_packetDominates
    {rho eta : ℝ} {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hrho : 0 < rho) (hrhoEta : rho < eta) (hetaUpper : eta < 1 - rho)
    (hfixed : FixedPrecisionExceptionalBounds E threshold)
    (hprime : EventuallyConcretePrimePacketDominatesCutoff eta
      (regularEndpointPowerCutoff rho)
      (section6TranslatedBadEndpoints eta E threshold)) :
    Section6RegularEndpointPackage rho eta E threshold := by
  have heta : 0 < eta := lt_trans hrho hrhoEta
  have heta1 : eta < 1 := by linarith
  constructor
  · exact eventuallyDyadicallySparse_concreteTranslatedPullback_of_bounds
      heta heta1 hfixed
  · exact eventuallyZeroOutsideBadEndpoints_powerCutoff_of_packetDominates
      hrho hrhoEta hetaUpper
      (eventuallyTranslatedEndpointPaperBounds_concrete heta heta1)
      hprime

/-- Convenient projection of the assembly: the actual translated bad endpoint
family supplied by the discretisation stage is `o(Y)` on dyadic windows. -/
theorem section6TranslatedBadEndpoints_sparse_of_fixedPrecision
    {eta : ℝ} {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (heta : 0 < eta) (heta1 : eta < 1)
    (hfixed : FixedPrecisionExceptionalBounds E threshold) :
    EventuallyDyadicallySparse (section6TranslatedBadEndpoints eta E threshold) := by
  exact eventuallyDyadicallySparse_concreteTranslatedPullback_of_bounds
    heta heta1 hfixed

/-- Convenient projection of the same assembly: endpoint-level packet
dominance gives zero defect outside the *same* translated exceptional family. -/
theorem section6ZeroOutsideTranslatedBadEndpoints_of_packetDominates
    {rho eta : ℝ} {E : ℕ → ℕ → Finset ℕ} {threshold : ℕ → ℕ}
    (hrho : 0 < rho) (hrhoEta : rho < eta) (hetaUpper : eta < 1 - rho)
    (hprime : EventuallyConcretePrimePacketDominatesCutoff eta
      (regularEndpointPowerCutoff rho)
      (section6TranslatedBadEndpoints eta E threshold)) :
    EventuallyZeroOutsideBadEndpoints (regularEndpointPowerCutoff rho)
      (section6TranslatedBadEndpoints eta E threshold) := by
  have heta : 0 < eta := lt_trans hrho hrhoEta
  have heta1 : eta < 1 := by linarith
  exact eventuallyZeroOutsideBadEndpoints_powerCutoff_of_packetDominates
    hrho hrhoEta hetaUpper
    (eventuallyTranslatedEndpointPaperBounds_concrete heta heta1)
    hprime

end DivisorF
