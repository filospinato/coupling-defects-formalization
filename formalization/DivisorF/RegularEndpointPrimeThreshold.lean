import DivisorF.RegularEndpointCanonicalScalar

set_option linter.style.header false

/-!
# Prime-packet threshold transfer for Section 6

The analytic input in the manuscript gives an asymptotic count of ordinary
primes in the concrete translated interval `J_eta(X)`.  The project-owned step
used in Theorem 6.2 is simpler and finite: once that one packet contains more
than `2 K` primes, it simultaneously beats the zero-defect threshold
`2(s-1)` for every type `2 <= s <= K` over the same endpoint.

This module records exactly that implication and composes it with the existing
`nu_eta / J_eta` endpoint machinery.  It does not assert the prime asymptotic
itself.  Thus the external/support input is reduced to one endpoint-level
cardinality inequality, while the passage to every quotient type and then to
zero defect remains machine-checkable project-owned bookkeeping.
-/

namespace DivisorF

/-- One concrete translated packet beats the zero-defect multiplicity threshold
uniformly throughout a type cutoff once it contains more than twice the cutoff
itself. -/
theorem concreteTranslatedEndpointPrimePacket_zeroThreshold_of_card_gt_twice_cutoff
    {eta : ℝ} {X K : ℕ}
    (hcard : 2 * K < (concreteTranslatedEndpointPrimePacket eta X).card) :
    ∀ s ∈ Finset.Icc 2 K,
      2 * (s - 1) < (concreteTranslatedEndpointPrimePacket eta X).card := by
  intro s hs
  have hsK : s ≤ K := (Finset.mem_Icc.mp hs).2
  have hsk : 2 * (s - 1) ≤ 2 * K := by omega
  exact lt_of_le_of_lt hsk hcard

/-- Eventual endpoint-level prime-packing input in the exact form needed by the
project-owned Theorem 6.2 transfer.  It is deliberately weaker than recording
an asymptotic formula for the packet: an external integer-PNT input only needs
to imply this eventual inequality outside the exceptional endpoint family. -/
def EventuallyConcretePrimePacketDominatesCutoff
    (eta : ℝ) (K : ℕ → ℕ) (E : ℕ → Finset ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E Y →
      2 * K X < (concreteTranslatedEndpointPrimePacket eta X).card

/-- Eventual scalar geometry for the concrete translated endpoint, separated
from prime richness. -/
def EventuallyConcreteTranslatedScalarBounds
    (eta : ℝ) (K : ℕ → ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    ∀ X ∈ Finset.Ico Y (2 * Y),
      RegularEndpointScalarBounds X (K X) (concreteTranslatedEndpointGap eta X)

/-- Endpoint-level packet dominance implies the older per-type prime-richness
interface.  This is the finite multiplicity step in the proof of Theorem 6.2. -/
theorem eventuallyConcreteTranslatedEndpointPrimeRich_of_packetDominatesCutoff
    {eta : ℝ} {K : ℕ → ℕ} {E : ℕ → Finset ℕ}
    (hprime : EventuallyConcretePrimePacketDominatesCutoff eta K E) :
    EventuallyConcreteTranslatedEndpointPrimeRich eta K E := by
  rcases hprime with ⟨Y₀, hprime⟩
  refine ⟨Y₀, ?_⟩
  intro Y hY X hXY hXE
  exact concreteTranslatedEndpointPrimePacket_zeroThreshold_of_card_gt_twice_cutoff
    (hprime Y hY X hXY hXE)

/-- **Theorem 6.2 threshold assembly.**

Separate the two ingredients available at a large regular endpoint:

* project-owned scalar geometry for the actual `nu_eta / J_eta` construction;
* one endpoint-level prime-cardinality inequality supplied from the integer-PNT
  asymptotic.

They imply the older per-type package `EventuallyConcreteTranslatedEndpointData`.
The analytic side no longer has to state the zero-defect threshold separately
for every `s`: that simultaneous implication is proved here. -/
theorem eventuallyConcreteTranslatedEndpointData_of_primePacketDominatesCutoff
    {eta : ℝ} {K : ℕ → ℕ} {E : ℕ → Finset ℕ}
    (hscalar : EventuallyConcreteTranslatedScalarBounds eta K)
    (hprime : EventuallyConcretePrimePacketDominatesCutoff eta K E) :
    EventuallyConcreteTranslatedEndpointData eta K E := by
  rcases hscalar with ⟨Ys, hscalar⟩
  rcases hprime with ⟨Yp, hprime⟩
  refine ⟨max Ys Yp, ?_⟩
  intro Y hY X hXY hXE
  have hYs : Ys ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hYp : Yp ≤ Y := le_trans (Nat.le_max_right _ _) hY
  refine ⟨hscalar Y hYs X hXY, ?_⟩
  exact concreteTranslatedEndpointPrimePacket_zeroThreshold_of_card_gt_twice_cutoff
    (hprime Y hYp X hXY hXE)

/-- The canonical power cutoff `floor(X^rho)` automatically supplies the scalar
part of the preceding assembly from the manuscript inequalities
`0 < rho < eta < 1-rho`. -/
theorem eventuallyConcreteTranslatedScalarBounds_powerCutoff
    {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoEta : rho < eta) (hetaUpper : eta < 1 - rho) :
    EventuallyConcreteTranslatedScalarBounds eta
      (regularEndpointPowerCutoff rho) := by
  rcases eventuallyRegularEndpointScalarBounds_of_concreteRadius
      (eventuallyConcreteTranslatedEndpointRadiusBounds_powerCutoff
        hrho hrhoEta hetaUpper) with ⟨X₀, hscalar⟩
  refine ⟨X₀, ?_⟩
  intro Y hY X hXY
  have hYX : Y ≤ X := (Finset.mem_Ico.mp hXY).1
  exact hscalar X (hY.trans hYX)

/-- **Theorem 6.2, canonical power-cutoff transfer.**

For `0 < rho < eta < 1-rho`, every project-owned scalar condition of the actual
`nu_eta/J_eta` construction is automatic.  Thus the only endpoint-level
prime-distribution input still visible is that the actual packet contains more
than `2 floor(X^rho)` primes outside the exceptional family. -/
theorem eventuallyConcreteTranslatedEndpointData_powerCutoff_of_packetDominates
    {rho eta : ℝ} {E : ℕ → Finset ℕ}
    (hrho : 0 < rho) (hrhoEta : rho < eta) (hetaUpper : eta < 1 - rho)
    (hprime : EventuallyConcretePrimePacketDominatesCutoff eta
      (regularEndpointPowerCutoff rho) E) :
    EventuallyConcreteTranslatedEndpointData eta
      (regularEndpointPowerCutoff rho) E := by
  exact eventuallyConcreteTranslatedEndpointData_of_primePacketDominatesCutoff
    (eventuallyConcreteTranslatedScalarBounds_powerCutoff
      hrho hrhoEta hetaUpper)
    hprime

/-- **Section 6 regular-endpoint zero-defect theorem with the analytic boundary
reduced to one packet-cardinality inequality.** -/
theorem eventuallyZeroOutsideBadEndpoints_of_primePacketDominatesCutoff
    {eta : ℝ} {K : ℕ → ℕ} {E : ℕ → Finset ℕ}
    (heta : 0 < eta)
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta)
    (hscalar : EventuallyConcreteTranslatedScalarBounds eta K)
    (hprime : EventuallyConcretePrimePacketDominatesCutoff eta K E) :
    EventuallyZeroOutsideBadEndpoints K E := by
  exact eventuallyZeroOutsideBadEndpoints_of_concreteTranslatedEndpoint
    heta hpaper
    (eventuallyConcreteTranslatedEndpointData_of_primePacketDominatesCutoff
      hscalar hprime)

/-- Canonical power-cutoff zero-defect form of Theorem 6.2. -/
theorem eventuallyZeroOutsideBadEndpoints_powerCutoff_of_packetDominates
    {rho eta : ℝ} {E : ℕ → Finset ℕ}
    (hrho : 0 < rho) (hrhoEta : rho < eta) (hetaUpper : eta < 1 - rho)
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta)
    (hprime : EventuallyConcretePrimePacketDominatesCutoff eta
      (regularEndpointPowerCutoff rho) E) :
    EventuallyZeroOutsideBadEndpoints (regularEndpointPowerCutoff rho) E := by
  have heta : 0 < eta := lt_trans hrho hrhoEta
  exact eventuallyZeroOutsideBadEndpoints_of_concreteTranslatedEndpoint
    heta hpaper
    (eventuallyConcreteTranslatedEndpointData_powerCutoff_of_packetDominates
      hrho hrhoEta hetaUpper hprime)

/-- Weighted-density composition of the same threshold assembly.  Exceptional
set sparsity and endpoint-mass estimates stay separate, as in the manuscript. -/
theorem weightedRelativeDensityZero_of_primePacketDominatesCutoff
    {eta : ℝ} {K : ℕ → ℕ} {E : ℕ → Finset ℕ} {W : ℕ → ℕ}
    (heta : 0 < eta)
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta)
    (hscalar : EventuallyConcreteTranslatedScalarBounds eta K)
    (hprime : EventuallyConcretePrimePacketDominatesCutoff eta K E)
    (hweight : EventuallyEndpointWeightBound K W)
    (hsmall : EventuallyNegligibleBadEndpointBurden K E W) :
    WeightedRelativeDensityZero K := by
  exact weightedRelativeDensityZero_of_concreteTranslatedEndpoint
    heta hpaper
    (eventuallyConcreteTranslatedEndpointData_of_primePacketDominatesCutoff
      hscalar hprime)
    hweight hsmall

end DivisorF
