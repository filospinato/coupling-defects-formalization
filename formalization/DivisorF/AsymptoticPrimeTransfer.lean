import DivisorF.QuotientPrimeCounting
import DivisorF.PowerConeExponent

set_option linter.style.header false

/-!
# Eventual prime-input transfers for Section 5

This module packages the project-original logical part of the manuscript's
fixed-exponent and generic power-cone arguments without formalizing any
published short-interval theorem.

A range is represented by a predicate `R N s`.  An external analytic input may
prove that, eventually on `R`, the exact quotient interval has inactive
large-prime cutoff and contains more than `2(s-1)` ordinary primes.  The
results below convert precisely that input into eventual zero defect, and then
transport it to any eventually smaller range.

For the manuscript's Theorem 5.2, the concrete range is
`s <= (N/s)^rho`; for Corollary 5.3, the smaller range is `s <= N^gamma`.
The analytic theorem `SI(beta)` remains outside the formalization.  Both the
strict exponent choice `gamma < rho/(1+rho)` and the elementary real-power
range comparison are machine-checked here and in `PowerConeExponent`.
-/

namespace DivisorF

/-- Exact finite prime-richness condition needed by the project-original
zero-defect transfer on a range predicate. -/
def PrimeRichForZeroDefectOn (R : ℕ → ℕ → Prop) (N s : ℕ) : Prop :=
  2 ≤ s → R N s →
    LargePrimeCutoffInactive N s ∧
      2 * (s - 1) < (quotientIntervalPrimeValues N s).card

/-- Eventual form of the exact prime-richness input.  This is an interface for
an external short-interval theorem plus the manuscript's interval containment
calculation; no such theorem is asserted here. -/
def EventuallyPrimeRichForZeroDefectOn (R : ℕ → ℕ → Prop) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s : ℕ,
    PrimeRichForZeroDefectOn R N s

/-- Eventual zero defect on an arbitrary type range. -/
def EventuallyZeroDefectOn (R : ℕ → ℕ → Prop) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s : ℕ,
    2 ≤ s → R N s → paperTypeDefect N s = 0

/-- The finite Section 5 transfer at one `(N,s)`: exact quotient prime
richness implies zero common type defect. -/
theorem paperTypeDefect_eq_zero_of_prime_rich_range
    {R : ℕ → ℕ → Prop} {N s : ℕ}
    (hprime : PrimeRichForZeroDefectOn R N s)
    (hs : 2 ≤ s) (hR : R N s) :
    paperTypeDefect N s = 0 := by
  rcases hprime hs hR with ⟨hoff, hcount⟩
  exact paperTypeDefect_eq_zero_of_quotient_prime_count hs hoff hcount

/-- **Section 5 fixed-range transfer, eventual form.**

Once an external prime theorem supplies the exact prime-richness condition
throughout a range for every sufficiently large `N`, the project's same-type
boundary budget forces zero defect throughout that range for every sufficiently
large `N`. -/
theorem eventuallyZeroDefectOn_of_eventuallyPrimeRich
    {R : ℕ → ℕ → Prop}
    (hprime : EventuallyPrimeRichForZeroDefectOn R) :
    EventuallyZeroDefectOn R := by
  rcases hprime with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro N hN s hs hR
  exact paperTypeDefect_eq_zero_of_prime_rich_range (hN₀ N hN s) hs hR

/-- Predicate `S` is eventually contained in predicate `R`, uniformly in the
type variable. -/
def EventuallyRangeContained
    (S R : ℕ → ℕ → Prop) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s : ℕ, 2 ≤ s → S N s → R N s

/-- Eventual zero defect is monotone under eventual restriction of the type
range. -/
theorem EventuallyZeroDefectOn.mono
    {R S : ℕ → ℕ → Prop}
    (hzero : EventuallyZeroDefectOn R)
    (hsub : EventuallyRangeContained S R) :
    EventuallyZeroDefectOn S := by
  rcases hzero with ⟨N₁, hN₁⟩
  rcases hsub with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN s hs hS
  have hN1 : N₁ ≤ N := le_trans (Nat.le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (Nat.le_max_right _ _) hN
  exact hN₁ N hN1 s hs (hN₂ N hN2 s hs hS)

/-- **Section 5 generic-cone transfer interface.**

If the fixed-exponent quotient range is eventually prime-rich and a second
range is eventually contained in it, then zero defect holds eventually on the
second range. -/
theorem genericPowerConeTransfer_interface
    {quotientRange powerCone : ℕ → ℕ → Prop}
    (hprime : EventuallyPrimeRichForZeroDefectOn quotientRange)
    (hcone : EventuallyRangeContained powerCone quotientRange) :
    EventuallyZeroDefectOn powerCone := by
  exact (eventuallyZeroDefectOn_of_eventuallyPrimeRich hprime).mono hcone

/-- The manuscript's fixed-exponent quotient range
`s ≤ (N/s)^rho`, interpreted in `ℝ`. -/
def QuotientPowerRange (rho : ℝ) (N s : ℕ) : Prop :=
  (s : ℝ) ≤ ((N : ℝ) / (s : ℝ)) ^ rho

/-- The manuscript's power cone `s ≤ N^gamma`, interpreted in `ℝ`. -/
def NaturalPowerCone (gamma : ℝ) (N s : ℕ) : Prop :=
  (s : ℝ) ≤ (N : ℝ) ^ gamma

/-- **Concrete Section 5 cone containment.**

For positive exponents with `gamma < rho/(1+rho)`, the natural power cone is
eventually contained in the fixed-exponent quotient range.  In fact the
containment holds already for every `N ≥ 1` and every type `s ≥ 2`.
This discharges the elementary range-comparison obligation that was previously
left as an interface. -/
theorem naturalPowerCone_eventuallyContained_quotientPowerRange
    {gamma rho : ℝ}
    (hgamma : 0 < gamma)
    (hrho : 0 < rho)
    (hgammaRho : gamma < rho / (1 + rho)) :
    EventuallyRangeContained (NaturalPowerCone gamma) (QuotientPowerRange rho) := by
  refine ⟨1, ?_⟩
  intro N hN s hs hcone
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsreal : (1 : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) hs)
  exact le_div_rpow_of_le_rpow hNreal hsreal (le_of_lt hgamma) hrho hgammaRho hcone

/-- Prime-richness interface for the manuscript's fixed-exponent theorem.
For every admissible `rho`, the corresponding quotient range is eventually
prime-rich.  An `SI(beta)` theorem may discharge this interface externally;
no analytic input is asserted here. -/
def FixedExponentPrimeRichInput
    (beta : ℝ) (quotientRange : ℝ → ℕ → ℕ → Prop) : Prop :=
  ∀ rho : ℝ, 0 < rho → rho < 1 - beta →
    EventuallyPrimeRichForZeroDefectOn (quotientRange rho)

/-- Range-comparison interface retained for reusable abstract transfers. -/
def PowerConeRangeComparison
    (quotientRange powerCone : ℝ → ℕ → ℕ → Prop) : Prop :=
  ∀ gamma rho : ℝ, 0 < gamma → gamma < rho / (1 + rho) →
    EventuallyRangeContained (powerCone gamma) (quotientRange rho)

/-- **Section 5 strict exponent-window transfer, abstract range form.** -/
theorem eventuallyZeroDefectOn_powerCone_of_fixedExponentWindow
    {beta gamma : ℝ}
    {quotientRange powerCone : ℝ → ℕ → ℕ → Prop}
    (hbetaLower : (1 : ℝ) / 2 < beta)
    (hbetaUpper : beta < 1)
    (hgammaPos : 0 < gamma)
    (hgammaUpper : gamma < (1 - beta) / (2 - beta))
    (hprime : FixedExponentPrimeRichInput beta quotientRange)
    (hcompare : PowerConeRangeComparison quotientRange powerCone) :
    EventuallyZeroDefectOn (powerCone gamma) := by
  rcases exists_rho_for_power_cone hbetaLower hbetaUpper hgammaPos hgammaUpper with
    ⟨rho, hrhoPos, hrhoUpper, hgammaRho⟩
  exact genericPowerConeTransfer_interface
    (hprime rho hrhoPos hrhoUpper)
    (hcompare gamma rho hgammaPos hgammaRho)

/-- **Corollary 5.3, project-owned transfer with concrete ranges.**

Assume only the prime-richness consequence supplied externally for every
admissible fixed exponent `rho`.  Then every fixed
`0 < gamma < (1-beta)/(2-beta)` has eventual zero defect throughout the actual
manuscript cone `2 ≤ s ≤ N^gamma`.  The choice of `rho` and the conversion
`s ≤ N^gamma => s ≤ (N/s)^rho` are both proved internally; `SI(beta)` itself
remains outside the trust boundary. -/
theorem eventuallyZeroDefectOn_naturalPowerCone_of_fixedExponentPrimeRich
    {beta gamma : ℝ}
    (hbetaLower : (1 : ℝ) / 2 < beta)
    (hbetaUpper : beta < 1)
    (hgammaPos : 0 < gamma)
    (hgammaUpper : gamma < (1 - beta) / (2 - beta))
    (hprime : FixedExponentPrimeRichInput beta QuotientPowerRange) :
    EventuallyZeroDefectOn (NaturalPowerCone gamma) := by
  rcases exists_rho_for_power_cone hbetaLower hbetaUpper hgammaPos hgammaUpper with
    ⟨rho, hrhoPos, hrhoUpper, hgammaRho⟩
  exact genericPowerConeTransfer_interface
    (hprime rho hrhoPos hrhoUpper)
    (naturalPowerCone_eventuallyContained_quotientPowerRange
      hgammaPos hrhoPos hgammaRho)

end DivisorF
