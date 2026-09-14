import DivisorF.RegularEndpointTransfer
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Arithmetic of translated regular endpoints

Project-original finite arithmetic from Section 6.  The analytic almost-all
prime theorem is deliberately absent.  This file discharges the exact quotient
inequalities that turn one translated interval below an endpoint `X` into a
common prime packet for every quotient block carried by that endpoint.

The manuscript later obtains the numerical hypotheses here uniformly from
`2 ≤ s ≤ X^rho`, `rho < eta < 1-rho`, and sufficiently large `X`.  Keeping
that one-variable power comparison separate makes the external trust boundary
visible: Gafni--Tao supplies prime richness outside an exceptional set, while
the quotient arithmetic remains a theorem of `DivisorF`.
-/

namespace DivisorF

/-- Exact finite version of the lower-endpoint estimate used in Section 6.

If `(N,s)` belongs to the quotient block with endpoint `X`, then
`N < s(X+1)`.  Consequently a translated interval of height `H` sits above the
lower quotient endpoint as soon as `(s+1)H ≤ X+1`:

`floor(N/(s+1)) ≤ X-H`.

This is the discrete content behind the manuscript's asymptotic estimate
`floor(N/(s+1)) < X-5X^eta` once `H` is chosen on the `X^eta` scale. -/
theorem quotientLowerEndpoint_le_endpoint_sub_height
    {N s X H : ℕ}
    (hs : 1 ≤ s)
    (hblock : (N, s) ∈ quotientBlockPairs X s)
    (hHX : H ≤ X)
    (hwidth : (s + 1) * H ≤ X + 1) :
    N / (s + 1) ≤ X - H := by
  have hspos : 0 < s + 1 := by omega
  have hNupper : N < s * (X + 1) := by
    have h := (mem_quotientBlockPairs.mp hblock).2.2
    simpa [Nat.mul_add] using h
  have hsub : X - H + H = X := Nat.sub_add_cancel hHX
  have htarget : s * (X + 1) ≤ (X - H + 1) * (s + 1) := by
    nlinarith
  have hlt : N < (X - H + 1) * (s + 1) := lt_of_lt_of_le hNupper htarget
  have hdiv : N / (s + 1) < X - H + 1 :=
    (Nat.div_lt_iff_lt_mul hspos).2 (by
      simpa [Nat.mul_comm] using hlt)
  omega

/-- Uniform endpoint-space form of
`quotientLowerEndpoint_le_endpoint_sub_height`.  A single height `H` works for
all pairs with `2 ≤ s ≤ K` once `(K+1)H ≤ X+1`. -/
theorem endpointPairSpace_quotientLowerEndpoint_le_sub
    {X K H : ℕ}
    (hHX : H ≤ X)
    (hwidth : (K + 1) * H ≤ X + 1) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      N / (s + 1) ≤ X - H := by
  intro N s hpair
  rcases Finset.mem_biUnion.mp hpair with ⟨t, htK, hblock⟩
  have hst : s = t := (mem_quotientBlockPairs.mp hblock).1
  subst t
  have hsK : s ≤ K := (Finset.mem_Icc.mp htK).2
  have hs1 : 1 ≤ s := le_trans (by decide : 1 ≤ 2) (Finset.mem_Icc.mp htK).1
  have hmul : (s + 1) * H ≤ (K + 1) * H :=
    Nat.mul_le_mul_right H (Nat.succ_le_succ hsK)
  exact quotientLowerEndpoint_le_endpoint_sub_height
    hs1 hblock hHX (le_trans hmul hwidth)

/-- The exact quotient lower endpoint is always at least the half-endpoint
core for quotient types `s ≥ 2`.  This elementary bound is useful for
separating the large-prime cutoff from the translated-packet placement. -/
theorem endpoint_half_le_quotientLowerEndpoint
    {N s X : ℕ}
    (hs : 2 ≤ s)
    (hblock : (N, s) ∈ quotientBlockPairs X s) :
    X / 2 ≤ N / (s + 1) := by
  have hd : 0 < s + 1 := by omega
  apply (Nat.le_div_iff_mul_le hd).2
  have hhalf : 2 * (X / 2) ≤ X := by
    exact Nat.mul_div_le X 2
  have hsone : s + 1 ≤ 2 * s := by omega
  have h1 : (X / 2) * (s + 1) ≤ (X / 2) * (2 * s) :=
    Nat.mul_le_mul_left (X / 2) hsone
  have h2 : (X / 2) * (2 * s) ≤ X * s := by
    calc
      (X / 2) * (2 * s) = (2 * (X / 2)) * s := by ring
      _ ≤ X * s := Nat.mul_le_mul_right s hhalf
  have hNX : s * X ≤ N := (mem_quotientBlockPairs.mp hblock).2.1
  calc
    (X / 2) * (s + 1) ≤ X * s := le_trans h1 h2
    _ = s * X := by ring
    _ ≤ N := hNX

/-- A half-endpoint square-root separation is sufficient to make the complete
quotient interval large-prime.  This reduces cutoff inactivity to a single
endpoint estimate independent of the exact remainder `N-sX`. -/
theorem largePrimeCutoffInactive_of_sqrt_lt_endpoint_half
    {N s X : ℕ}
    (hs : 2 ≤ s)
    (hblock : (N, s) ∈ quotientBlockPairs X s)
    (hsqrt : Real.sqrt (N : ℝ) < (X / 2 : ℕ)) :
    LargePrimeCutoffInactive N s := by
  have hhalf := endpoint_half_le_quotientLowerEndpoint hs hblock
  have hhalfR : ((X / 2 : ℕ) : ℝ) ≤ ((N / (s + 1) : ℕ) : ℝ) := by
    exact_mod_cast hhalf
  exact lt_of_lt_of_le hsqrt hhalfR

/-- Uniform endpoint-space cutoff transfer.  Once every block in the endpoint
cone satisfies the same half-endpoint square-root separation, the cutoff
hypothesis required by `RegularEndpointTransfer` is discharged simultaneously. -/
theorem endpointPairSpace_cutoffInactive_of_sqrt_lt_half
    {X K : ℕ}
    (hsqrt :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        Real.sqrt (N : ℝ) < (X / 2 : ℕ)) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      LargePrimeCutoffInactive N s := by
  intro N s hpair
  rcases Finset.mem_biUnion.mp hpair with ⟨t, htK, hblock⟩
  have hst : s = t := (mem_quotientBlockPairs.mp hblock).1
  subst t
  exact largePrimeCutoffInactive_of_sqrt_lt_endpoint_half
    (Finset.mem_Icc.mp htK).1 hblock (hsqrt hpair)

/-- **Section 6 finite regular-endpoint package with arithmetic discharged.**

A translated packet `(X-H,X]` simultaneously forces zero defect throughout the
endpoint cone once three scalar conditions hold:

* `H ≤ X` and `(K+1)H ≤ X+1`, placing the packet above every lower quotient
  endpoint;
* the half-endpoint square-root separation, making the large-prime cutoff
  inactive in every block;
* enough primes in the packet to beat the same-type multiplicity threshold.

Thus the per-pair lower-endpoint and cutoff hypotheses of
`endpointPairSpace_zero_of_translated_prime_packet` are no longer interfaces.
The remaining asymptotic job is only to prove these scalar conditions from the
paper's exponent inequalities and prime-rich regular endpoint input. -/
theorem endpointPairSpace_zero_of_translated_prime_packet_arithmetic
    {X K H : ℕ}
    (hHX : H ≤ X)
    (hwidth : (K + 1) * H ≤ X + 1)
    (hsqrt :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        Real.sqrt (N : ℝ) < (X / 2 : ℕ))
    (hcard :
      ∀ s ∈ Finset.Icc 2 K,
        2 * (s - 1) < (translatedEndpointPrimePacket X H).card) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      paperTypeDefect N s = 0 := by
  exact endpointPairSpace_zero_of_translated_prime_packet
    (endpointPairSpace_quotientLowerEndpoint_le_sub hHX hwidth)
    (endpointPairSpace_cutoffInactive_of_sqrt_lt_half hsqrt)
    hcard

/-- Binary counterpart of the arithmetic-discharge package. -/
theorem endpointPairSpace_binary_of_translated_prime_packet_arithmetic
    {X K H : ℕ}
    (hHX : H ≤ X)
    (hwidth : (K + 1) * H ≤ X + 1)
    (hsqrt :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        Real.sqrt (N : ℝ) < (X / 2 : ℕ))
    (hcard :
      ∀ s ∈ Finset.Icc 2 K,
        s - 1 < (translatedEndpointPrimePacket X H).card) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      paperTypeDefect N s ≤ 1 := by
  exact endpointPairSpace_binary_of_translated_prime_packet
    (endpointPairSpace_quotientLowerEndpoint_le_sub hHX hwidth)
    (endpointPairSpace_cutoffInactive_of_sqrt_lt_half hsqrt)
    hcard

/-- **Section 6 exceptional-endpoint bound with quotient arithmetic
internalized.**  This is the weighted finite form used immediately before the
`o(Y)` density step.  Compared with the older translated-packet theorem, the
lower quotient endpoint and large-prime cutoff are no longer supplied pair by
pair: they follow from scalar endpoint estimates shared by the whole cone. -/
theorem positiveDefectWeightedPairs_card_le_bad_card_mul_of_translated_packets_arithmetic
    {Y W : ℕ} {K H : ℕ → ℕ} {E : Finset ℕ}
    (hHX :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E → H X ≤ X)
    (hwidth :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        (K X + 1) * H X ≤ X + 1)
    (hsqrt :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X (K X) →
          Real.sqrt (N : ℝ) < (X / 2 : ℕ))
    (hcard :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ s ∈ Finset.Icc 2 (K X),
          2 * (s - 1) < (translatedEndpointPrimePacket X (H X)).card)
    (hweight :
      ∀ X ∈ Finset.Ico Y (2 * Y), endpointPairWeight (K X) ≤ W) :
    (positiveDefectWeightedPairs Y K).card ≤ E.card * W := by
  apply positiveDefectWeightedPairs_card_le_bad_card_mul
  · intro X hXY hXE s hs N hblock
    have hpair : (N, s) ∈ endpointPairSpace X (K X) := by
      apply Finset.mem_biUnion.mpr
      exact ⟨s, hs, hblock⟩
    exact endpointPairSpace_zero_of_translated_prime_packet_arithmetic
      (X := X) (K := K X) (H := H X)
      (hHX X hXY hXE)
      (hwidth X hXY hXE)
      (hsqrt X hXY hXE)
      (hcard X hXY hXE)
      hpair
  · exact hweight

end DivisorF
