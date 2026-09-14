import DivisorF.TranslatedRegularEndpoint
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Scalar endpoint bounds for the Section 6 translated interval

The translated regular-endpoint transfer is simultaneous in all quotient types
`2 ≤ s ≤ K`, but one of its remaining hypotheses was still stated pair by pair:
`sqrt N < X/2` for every `(N,s)` in the endpoint cone.  The manuscript proves
this uniformly from the size of the cone.  This module isolates the exact finite
project-owned reduction: every pair above endpoint `X` satisfies
`N < K (X+1)`, so the single scalar inequality

`K (X+1) ≤ floor(X/2)^2`

forces the large-prime cutoff to be inactive throughout the cone.

Together with the already formalized width condition `(K+1)H ≤ X+1`, this
reduces all quotient geometry needed by the shifted packet to endpoint-level
scalar inequalities.  No prime-distribution input occurs here.
-/

namespace DivisorF

/-- Every pair in the endpoint cone has `N < K(X+1)`. -/
theorem endpointPairSpace_N_lt_cutoff_mul_endpointSucc
    {X K N s : ℕ}
    (hpair : (N, s) ∈ endpointPairSpace X K) :
    N < K * (X + 1) := by
  rcases Finset.mem_biUnion.mp hpair with ⟨t, htK, hblock⟩
  have hst : s = t := (mem_quotientBlockPairs.mp hblock).1
  subst t
  have hupper : N < s * (X + 1) := by
    simpa [Nat.mul_add] using (mem_quotientBlockPairs.mp hblock).2.2
  have hsK : s ≤ K := (Finset.mem_Icc.mp htK).2
  exact lt_of_lt_of_le hupper (Nat.mul_le_mul_right (X + 1) hsK)

/-- A single square bound on the endpoint cone implies the half-endpoint
square-root separation for every pair in that cone. -/
theorem endpointPairSpace_sqrt_lt_half_of_scalar_square_bound
    {X K : ℕ}
    (hsquare : K * (X + 1) ≤ (X / 2) * (X / 2)) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      Real.sqrt (N : ℝ) < (X / 2 : ℕ) := by
  intro N s hpair
  have hN : N < (X / 2) * (X / 2) :=
    lt_of_lt_of_le (endpointPairSpace_N_lt_cutoff_mul_endpointSucc hpair) hsquare
  have hNR : (N : ℝ) < ((X / 2 : ℕ) : ℝ) * ((X / 2 : ℕ) : ℝ) := by
    exact_mod_cast hN
  have hsqrtSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtNonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hhalfNonneg : 0 ≤ ((X / 2 : ℕ) : ℝ) := by positivity
  nlinarith [hsqrtSq]

/-- Endpoint-level package collecting exactly the finite scalar geometry used
by the translated-packet transfer. -/
def RegularEndpointScalarBounds (X K H : ℕ) : Prop :=
  H ≤ X ∧
  (K + 1) * H ≤ X + 1 ∧
  K * (X + 1) ≤ (X / 2) * (X / 2)

/-- Scalar bounds discharge both quotient placement and the large-prime cutoff
simultaneously throughout the endpoint cone. -/
theorem endpointPairSpace_zero_of_shifted_prime_packet_scalar
    {X K H a L : ℕ}
    (hscalar : RegularEndpointScalarBounds X K H)
    (hleft : X - H ≤ a)
    (hright : a + L ≤ X)
    (hcard :
      ∀ s ∈ Finset.Icc 2 K,
        2 * (s - 1) < (shiftedPrimePacket a L).card) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      paperTypeDefect N s = 0 := by
  rcases hscalar with ⟨hHX, hwidth, hsquare⟩
  exact endpointPairSpace_zero_of_shifted_prime_packet_arithmetic
    hHX hwidth
    (endpointPairSpace_sqrt_lt_half_of_scalar_square_bound hsquare)
    hleft hright hcard

/-- Binary counterpart of the scalar translated-endpoint package. -/
theorem endpointPairSpace_binary_of_shifted_prime_packet_scalar
    {X K H a L : ℕ}
    (hscalar : RegularEndpointScalarBounds X K H)
    (hleft : X - H ≤ a)
    (hright : a + L ≤ X)
    (hcard :
      ∀ s ∈ Finset.Icc 2 K,
        s - 1 < (shiftedPrimePacket a L).card) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      paperTypeDefect N s ≤ 1 := by
  rcases hscalar with ⟨hHX, hwidth, hsquare⟩
  exact endpointPairSpace_binary_of_shifted_prime_packet_arithmetic
    hHX hwidth
    (endpointPairSpace_sqrt_lt_half_of_scalar_square_bound hsquare)
    hleft hright hcard

/-- Weighted exceptional-endpoint estimate with all pairwise quotient geometry
reduced to endpoint-level scalar bounds.  This is the finite counting statement
used before the Section 6 `o(Y)` argument. -/
theorem positiveDefectWeightedPairs_card_le_bad_card_mul_of_shifted_packets_scalar
    {Y W : ℕ} {K H a L : ℕ → ℕ} {E : Finset ℕ}
    (hscalar :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        RegularEndpointScalarBounds X (K X) (H X))
    (hleft :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        X - H X ≤ a X)
    (hright :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        a X + L X ≤ X)
    (hcard :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ s ∈ Finset.Icc 2 (K X),
          2 * (s - 1) < (shiftedPrimePacket (a X) (L X)).card)
    (hweight :
      ∀ X ∈ Finset.Ico Y (2 * Y), endpointPairWeight (K X) ≤ W) :
    (positiveDefectWeightedPairs Y K).card ≤ E.card * W := by
  apply positiveDefectWeightedPairs_card_le_bad_card_mul
  · intro X hXY hXE s hs N hblock
    have hpair : (N, s) ∈ endpointPairSpace X (K X) := by
      apply Finset.mem_biUnion.mpr
      exact ⟨s, hs, hblock⟩
    exact endpointPairSpace_zero_of_shifted_prime_packet_scalar
      (X := X) (K := K X) (H := H X) (a := a X) (L := L X)
      (hscalar X hXY hXE)
      (hleft X hXY hXE)
      (hright X hXY hXE)
      (hcard X hXY hXE)
      hpair
  · exact hweight

end DivisorF
