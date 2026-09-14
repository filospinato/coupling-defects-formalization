import DivisorF.CubicDensityTransfer
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Natural-cone weighted density for Corollary 6.4

This module completes the finite project-owned packaging that turns the
endpoint sandwich of `CubicDensityTransfer` into the manuscript's natural
weighted pair space

`Y ≤ floor(N/s) < 2Y,  2 ≤ s ≤ N^gamma`.

The key point is to keep the counting cutoff at the canonical exponent
`delta = gamma/(1-gamma)`, rather than replacing it by the wider auxiliary
`rho`-cone.  The upper half of the exact sandwich gives
`s ≤ (X+1)^delta`, so on `Y ≤ X < 2Y` every natural-cone pair lies below one
finite dyadic cutoff `(2Y)^delta`.  This produces an exact finite model of
`D_gamma(Y)` and lets exceptional endpoints be counted with the correct
`delta`-scale weight.

The external Gafni--Tao / integer-discretisation input is still absent.  It is
needed only to discharge the explicit hypotheses that regular endpoints have
zero defect and that the exceptional endpoint set is sparse.  The remaining
`o(Y) * O(Y^(2 delta)) / Omega(Y^(1+2 delta))` bookkeeping is project-owned and
is formalized below as a purely finite eventual transfer.
-/

namespace DivisorF

noncomputable def cubicNaturalDyadicCutoff (gamma : ℝ) (Y : ℕ) : ℕ :=
  ⌈((2 * Y : ℕ) : ℝ) ^ cubicEndpointExponent gamma⌉₊

noncomputable def cubicNaturalPairSpace (Y : ℕ) (gamma : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (weightedPairSpace Y (fun _ => cubicNaturalDyadicCutoff gamma Y)).filter
    fun p => NaturalPowerCone gamma p.1 p.2

/-- Membership in the finite model is exactly the manuscript condition. -/
theorem mem_cubicNaturalPairSpace
    {Y N s : ℕ} {gamma : ℝ}
    (hY : 1 ≤ Y) (hgamma : 0 < gamma)
    (hgammaUpper : gamma < (1 : ℝ) / 3) :
    (N, s) ∈ cubicNaturalPairSpace Y gamma ↔
      Y ≤ N / s ∧ N / s < 2 * Y ∧ 2 ≤ s ∧ NaturalPowerCone gamma N s := by
  classical
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hweighted, hnatural⟩
    have hw := mem_weightedPairSpace.mp hweighted
    exact ⟨hw.1, hw.2.1, hw.2.2.1, hnatural⟩
  · rintro ⟨hlo, hhi, hs2, hnatural⟩
    let X := N / s
    have hX1 : 1 ≤ X := by
      dsimp [X]
      exact le_trans hY hlo
    have hspos : 0 < s := by omega
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast (le_trans (by decide : 1 ≤ 2) hs2)
    have hNposNat : 0 < N := by
      have hmul : s * X ≤ N := by
        dsimp [X]
        simpa [Nat.mul_comm] using Nat.div_mul_le_self N s
      have hprod : 0 < s * X := Nat.mul_pos hspos (Nat.zero_lt_of_lt hX1)
      omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
    have hupperNat : N ≤ s * (X + 1) := by
      have hlt : N / s < X + 1 := by simp [X]
      have hlt' : N < (X + 1) * s := (Nat.div_lt_iff_lt_mul hspos).1 hlt
      simpa [Nat.mul_comm] using hlt'.le
    have hupper : (N : ℝ) ≤ (s : ℝ) * ((X : ℝ) + 1) := by
      exact_mod_cast hupperNat
    have hpre :
        (s : ℝ) ≤ ((X : ℝ) + 1) ^ cubicEndpointExponent gamma :=
      natural_rpow_le_succ_endpoint_rpow (by positivity) hs1 hNpos hupper
        (cubicEndpointExponent_pos hgamma hgammaUpper)
        (gamma_eq_cubicEndpointExponent_div_one_add
          (lt_trans hgammaUpper (by norm_num)))
        hnatural
    have hXhi : X < 2 * Y := by
      simpa [X] using hhi
    have hXsucc : X + 1 ≤ 2 * Y := by
      omega
    have hXsuccReal : ((X + 1 : ℕ) : ℝ) ≤ ((2 * Y : ℕ) : ℝ) := by
      exact_mod_cast hXsucc
    have hdyadic :
        ((X + 1 : ℕ) : ℝ) ^ cubicEndpointExponent gamma ≤
          ((2 * Y : ℕ) : ℝ) ^ cubicEndpointExponent gamma :=
      Real.rpow_le_rpow (by positivity) hXsuccReal
        (le_of_lt (cubicEndpointExponent_pos hgamma hgammaUpper))
    have hsCutReal :
        (s : ℝ) ≤ (cubicNaturalDyadicCutoff gamma Y : ℝ) := by
      calc
        (s : ℝ) ≤ ((X + 1 : ℕ) : ℝ) ^ cubicEndpointExponent gamma := by
          simpa using hpre
        _ ≤ ((2 * Y : ℕ) : ℝ) ^ cubicEndpointExponent gamma := hdyadic
        _ ≤ (cubicNaturalDyadicCutoff gamma Y : ℝ) := by
          exact Nat.le_ceil _
    have hsCut : s ≤ cubicNaturalDyadicCutoff gamma Y := by
      exact_mod_cast hsCutReal
    apply Finset.mem_filter.mpr
    refine ⟨?_, hnatural⟩
    apply mem_weightedPairSpace.mpr
    simpa [X] using ⟨hlo, hhi, hs2, hsCut⟩

noncomputable def positiveDefectCubicNaturalPairs
    (Y : ℕ) (gamma : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (cubicNaturalPairSpace Y gamma).filter
    fun p => 0 < paperTypeDefect p.1 p.2

def EventuallyZeroOutsideBadEndpointsNatural
    (gamma : ℝ) (E : ℕ → Finset ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E Y →
      ∀ s N : ℕ, 2 ≤ s →
        (N, s) ∈ quotientBlockPairs X s →
        NaturalPowerCone gamma N s →
        paperTypeDefect N s = 0

/-- A numerical endpoint cutoff eventually contains every integral type in an
endpoint `rho`-cone.  For the manuscript one takes the floor of `X^rho`. -/
def EventuallyEndpointConeFitsCutoff
    (rho : ℝ) (K : ℕ → ℕ) : Prop :=
  ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    ∀ s : ℕ, EndpointPowerCone rho X s → s ≤ K X

/-- Connect the existing endpoint-cutoff zero-defect layer to the exact natural
cone using the cubic range containment. -/
theorem eventuallyZeroOutsideBadEndpointsNatural_of_endpoint_cutoff
    {gamma rho : ℝ} {K : ℕ → ℕ} {E : ℕ → Finset ℕ}
    (hzero : EventuallyZeroOutsideBadEndpoints K E)
    (hcontain : EventuallyNaturalConeContainedInEndpointCone gamma rho)
    (hfit : EventuallyEndpointConeFitsCutoff rho K) :
    EventuallyZeroOutsideBadEndpointsNatural gamma E := by
  rcases hzero with ⟨Yzero, hzero⟩
  rcases hcontain with ⟨Xcontain, hcontain⟩
  rcases hfit with ⟨Xfit, hfit⟩
  refine ⟨max Yzero (max Xcontain Xfit), ?_⟩
  intro Y hY X hXY hXE s N hs hblock hnatural
  have hYzero : Yzero ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hthreshold : max Xcontain Xfit ≤ Y :=
    le_trans (Nat.le_max_right _ _) hY
  have hYX : Y ≤ X := (Finset.mem_Ico.mp hXY).1
  have hXcontain : Xcontain ≤ X :=
    le_trans (le_trans (Nat.le_max_left _ _) hthreshold) hYX
  have hXfit : Xfit ≤ X :=
    le_trans (le_trans (Nat.le_max_right _ _) hthreshold) hYX
  have hcone : EndpointPowerCone rho X s :=
    hcontain X hXcontain s N hs hblock hnatural
  have hsK : s ≤ K X := hfit X hXfit s hcone
  exact hzero Y hYzero X hXY hXE s (Finset.mem_Icc.mpr ⟨hs, hsK⟩) N hblock

/-- Finite exceptional-endpoint bound in the exact natural pair space. -/
theorem positiveDefectCubicNaturalPairs_card_le_bad_card_mul
    {Y : ℕ} {gamma : ℝ} {E : Finset ℕ}
    (_hY : 1 ≤ Y) (_hgamma : 0 < gamma)
    (_hgammaUpper : gamma < (1 : ℝ) / 3)
    (hzero :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ s N : ℕ, 2 ≤ s →
          (N, s) ∈ quotientBlockPairs X s →
          NaturalPowerCone gamma N s →
          paperTypeDefect N s = 0) :
    (positiveDefectCubicNaturalPairs Y gamma).card ≤
      E.card * endpointPairWeight (cubicNaturalDyadicCutoff gamma Y) := by
  classical
  let K : ℕ → ℕ := fun _ => cubicNaturalDyadicCutoff gamma Y
  have hsubset :
      positiveDefectCubicNaturalPairs Y gamma ⊆ badEndpointPairSpace Y K E := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hnaturalSpace, hpdef⟩
    rcases Finset.mem_filter.mp hnaturalSpace with ⟨hweighted, hnatural⟩
    rcases Finset.mem_biUnion.mp hweighted with ⟨X, hXY, hpX⟩
    by_cases hXE : X ∈ E
    · exact Finset.mem_biUnion.mpr
        ⟨X, Finset.mem_filter.mpr ⟨hXY, hXE⟩, hpX⟩
    · rcases Finset.mem_biUnion.mp hpX with ⟨s, hsK, hblock⟩
      rcases p with ⟨N, t⟩
      have hts : t = s := (mem_quotientBlockPairs.mp hblock).1
      subst t
      have hs2 : 2 ≤ s := (Finset.mem_Icc.mp hsK).1
      have hz := hzero X hXY hXE s N hs2 hblock hnatural
      rw [hz] at hpdef
      omega
  calc
    (positiveDefectCubicNaturalPairs Y gamma).card
        ≤ (badEndpointPairSpace Y K E).card := Finset.card_le_card hsubset
    _ = ∑ X ∈ (Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E),
          endpointPairWeight (K X) := badEndpointPairSpace_card Y K E
    _ ≤ E.card * endpointPairWeight (cubicNaturalDyadicCutoff gamma Y) := by
      calc
        ∑ X ∈ (Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E),
              endpointPairWeight (K X)
            = ((Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E)).card *
                endpointPairWeight (cubicNaturalDyadicCutoff gamma Y) := by
                simp [K]
        _ ≤ E.card * endpointPairWeight (cubicNaturalDyadicCutoff gamma Y) := by
          exact Nat.mul_le_mul_right _
            (Finset.card_le_card (by
              intro X hX
              exact (Finset.mem_filter.mp hX).2))

def CubicNaturalRelativeDensityZero (gamma : ℝ) : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    (positiveDefectCubicNaturalPairs Y gamma).card * C ≤
      (cubicNaturalPairSpace Y gamma).card

def EventuallyNegligibleCubicNaturalBadBurden
    (gamma : ℝ) (E : ℕ → Finset ℕ) : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    (E Y).card * endpointPairWeight (cubicNaturalDyadicCutoff gamma Y) * C ≤
      (cubicNaturalPairSpace Y gamma).card

/-- Reciprocal-integer form of `|E(Y)| = o(Y)`.  This is the only place where
the external almost-all theorem enters the final counting transfer: the theorem
below does not care how the exceptional endpoint set was produced. -/
def EventuallySparseBadEndpoints (E : ℕ → Finset ℕ) : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    (E Y).card * C ≤ Y

/-- Eventual `O(W(Y))` upper bound for the total natural-cone pair weight carried
by one exceptional endpoint.  In the manuscript one instantiates `W(Y)` at the
`Y^(2 delta)` scale. -/
def EventuallyCubicNaturalEndpointWeightBound
    (gamma : ℝ) (W : ℕ → ℕ) (A : ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    endpointPairWeight (cubicNaturalDyadicCutoff gamma Y) ≤ A * W Y

/-- Eventual `Omega(Y W(Y))` lower bound for the exact natural-cone pair space.
At the canonical exponent this is the manuscript's
`Omega(Y^(1+2 delta))` lower mass. -/
def EventuallyCubicNaturalTotalWeightLower
    (gamma : ℝ) (W : ℕ → ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    Y * W Y ≤ (cubicNaturalPairSpace Y gamma).card

/-- Project-owned asymptotic multiplication step behind Corollary 6.4:

`|E(Y)| = o(Y)`, `endpointWeight = O(W(Y))`, and
`totalWeight = Omega(Y W(Y))` imply that the exceptional weighted burden is
negligible relative to the exact natural pair space.

All three hypotheses are stated in division-free eventual form, so this theorem
contains no external prime-distribution content. -/
theorem eventuallyNegligibleCubicNaturalBadBurden_of_sparse_bad_endpoints
    {gamma : ℝ} {E : ℕ → Finset ℕ} {W : ℕ → ℕ} {A : ℕ}
    (hA : 1 ≤ A)
    (hsparse : EventuallySparseBadEndpoints E)
    (hweight : EventuallyCubicNaturalEndpointWeightBound gamma W A)
    (htotal : EventuallyCubicNaturalTotalWeightLower gamma W) :
    EventuallyNegligibleCubicNaturalBadBurden gamma E := by
  intro C hC
  have hAC : 1 ≤ A * C := Nat.mul_pos (Nat.zero_lt_of_lt hA) (Nat.zero_lt_of_lt hC)
  rcases hsparse (A * C) hAC with ⟨Ysparse, hsparse⟩
  rcases hweight with ⟨Yweight, hweight⟩
  rcases htotal with ⟨Ytotal, htotal⟩
  refine ⟨max Ysparse (max Yweight Ytotal), ?_⟩
  intro Y hY
  have hYsparse : Ysparse ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hYweight : Yweight ≤ Y :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hY
  have hYtotal : Ytotal ≤ Y :=
    le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hY
  have hs : (E Y).card * (A * C) ≤ Y := hsparse Y hYsparse
  have hw := hweight Y hYweight
  have hendpoint :
      (E Y).card * endpointPairWeight (cubicNaturalDyadicCutoff gamma Y) * C ≤
        (E Y).card * (A * W Y) * C :=
    Nat.mul_le_mul_right C (Nat.mul_le_mul_left (E Y).card hw)
  have hscale :
      (E Y).card * (A * W Y) * C ≤ Y * W Y := by
    have := Nat.mul_le_mul_right (W Y) hs
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
  exact le_trans hendpoint (le_trans hscale (htotal Y hYtotal))

/-- **Corollary 6.4, project-owned density transfer.** -/
theorem cubicNaturalRelativeDensityZero_of_negligible_bad_endpoints
    {gamma : ℝ} {E : ℕ → Finset ℕ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hzero : EventuallyZeroOutsideBadEndpointsNatural gamma E)
    (hsmall : EventuallyNegligibleCubicNaturalBadBurden gamma E) :
    CubicNaturalRelativeDensityZero gamma := by
  rcases hzero with ⟨Yzero, hzero⟩
  intro C hC
  rcases hsmall C hC with ⟨Ysmall, hsmall⟩
  refine ⟨max 1 (max Yzero Ysmall), ?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hYzero : Yzero ≤ Y :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hY
  have hYsmall : Ysmall ≤ Y :=
    le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hY
  have hfinite := positiveDefectCubicNaturalPairs_card_le_bad_card_mul
    hY1 hgamma hgammaUpper (hzero Y hYzero)
  calc
    (positiveDefectCubicNaturalPairs Y gamma).card * C
        ≤ ((E Y).card * endpointPairWeight (cubicNaturalDyadicCutoff gamma Y)) * C :=
      Nat.mul_le_mul_right C hfinite
    _ ≤ (cubicNaturalPairSpace Y gamma).card := hsmall Y hYsmall

/-- Corollary 6.4 with the manuscript's three counting inputs separated:
sparse exceptional endpoints, one-endpoint weight control, and the lower mass of
the exact natural-cone pair space. -/
theorem cubicNaturalRelativeDensityZero_of_sparse_bad_endpoints
    {gamma : ℝ} {E : ℕ → Finset ℕ} {W : ℕ → ℕ} {A : ℕ}
    (hgamma : 0 < gamma) (hgammaUpper : gamma < (1 : ℝ) / 3)
    (hA : 1 ≤ A)
    (hzero : EventuallyZeroOutsideBadEndpointsNatural gamma E)
    (hsparse : EventuallySparseBadEndpoints E)
    (hweight : EventuallyCubicNaturalEndpointWeightBound gamma W A)
    (htotal : EventuallyCubicNaturalTotalWeightLower gamma W) :
    CubicNaturalRelativeDensityZero gamma := by
  apply cubicNaturalRelativeDensityZero_of_negligible_bad_endpoints
    hgamma hgammaUpper hzero
  exact eventuallyNegligibleCubicNaturalBadBurden_of_sparse_bad_endpoints
    hA hsparse hweight htotal

end DivisorF
