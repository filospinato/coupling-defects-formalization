import DivisorF.RegularEndpointArithmetic

set_option linter.style.header false

/-!
# Translated regular-endpoint packets

This file formalizes the project-owned finite part of the `nu_eta / J_eta`
construction in Section 6.  The external almost-all prime theorem is not
formalized here.  Instead, a prime-rich interval `J=(nu,nu+L]` supplied at a
regular integer endpoint is treated as explicit finite data.

The original contribution formalized below is the transfer from that translated
packet to all quotient types above the same endpoint: once `J` is known to lie
inside `(X-H,X]`, the quotient arithmetic from `RegularEndpointArithmetic`
places it in every exact type interval simultaneously, and the multiplicity
budget forces zero (or binary) defect.
-/

namespace DivisorF

/-- Ordinary primes in an auxiliary translated interval `(a,a+L]`.  In the
manuscript this is `J_eta(X)` with `a = nu_eta(X)` and
`L = floor (nu_eta(X)^eta)`. -/
def shiftedPrimePacket (a L : ℕ) : Finset ℕ :=
  (Finset.Ioc a (a + L)).filter Nat.Prime

@[simp]
theorem mem_shiftedPrimePacket {a L p : ℕ} :
    p ∈ shiftedPrimePacket a L ↔ Nat.Prime p ∧ a < p ∧ p ≤ a + L := by
  simp only [shiftedPrimePacket, Finset.mem_filter, Finset.mem_Ioc]
  aesop

/-- Finite form of the manuscript's location estimate
`J_eta(X) ⊂ (X-H,X]`. -/
theorem shiftedPrimePacket_subset_translatedEndpointPrimePacket
    {X H a L : ℕ}
    (hleft : X - H ≤ a)
    (hright : a + L ≤ X) :
    shiftedPrimePacket a L ⊆ translatedEndpointPrimePacket X H := by
  intro p hp
  have hpdata := mem_shiftedPrimePacket.mp hp
  apply mem_translatedEndpointPrimePacket.mpr
  exact ⟨hpdata.1, lt_of_le_of_lt hleft hpdata.2.1,
    le_trans hpdata.2.2 hright⟩

/-- A located auxiliary packet is contained in the exact quotient-prime
interval of every quotient block for which `(X-H,X]` is contained. -/
theorem shiftedPrimePacket_subset_quotientInterval
    {N s X H a L : ℕ}
    (hs : 1 ≤ s)
    (hblock : (N, s) ∈ quotientBlockPairs X s)
    (hlower : N / (s + 1) ≤ X - H)
    (hleft : X - H ≤ a)
    (hright : a + L ≤ X) :
    shiftedPrimePacket a L ⊆ quotientIntervalPrimeValues N s := by
  exact Finset.Subset.trans
    (shiftedPrimePacket_subset_translatedEndpointPrimePacket hleft hright)
    (translatedEndpointPrimePacket_subset_quotientInterval hs hblock hlower)

/-- **Section 6 `J_eta` regular-endpoint transfer, finite zero-defect form.**

One auxiliary prime-rich interval `(a,a+L]` controls every type
`2 ≤ s ≤ K` above endpoint `X`.  All per-pair quotient geometry is discharged
by the scalar hypotheses already isolated in `RegularEndpointArithmetic`.
Thus the only prime-distribution input remaining is the cardinality of the
single shifted packet. -/
theorem endpointPairSpace_zero_of_shifted_prime_packet_arithmetic
    {X K H a L : ℕ}
    (hHX : H ≤ X)
    (hwidth : (K + 1) * H ≤ X + 1)
    (hsqrt :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        Real.sqrt (N : ℝ) < (X / 2 : ℕ))
    (hleft : X - H ≤ a)
    (hright : a + L ≤ X)
    (hcard :
      ∀ s ∈ Finset.Icc 2 K,
        2 * (s - 1) < (shiftedPrimePacket a L).card) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      paperTypeDefect N s = 0 := by
  intro N s hpair
  rcases Finset.mem_biUnion.mp hpair with ⟨t, htK, hblock⟩
  have hst : s = t := (mem_quotientBlockPairs.mp hblock).1
  subst t
  have hsone : 1 ≤ s := by
    have hs2 := (Finset.mem_Icc.mp htK).1
    omega
  exact paperTypeDefect_eq_zero_of_prime_packet_subset
    (Finset.mem_Icc.mp htK).1
    (endpointPairSpace_cutoffInactive_of_sqrt_lt_half hsqrt hpair)
    (shiftedPrimePacket_subset_quotientInterval
      hsone hblock
      (endpointPairSpace_quotientLowerEndpoint_le_sub hHX hwidth hpair)
      hleft hright)
    (hcard s htK)

/-- Binary counterpart of the finite `J_eta` transfer. -/
theorem endpointPairSpace_binary_of_shifted_prime_packet_arithmetic
    {X K H a L : ℕ}
    (hHX : H ≤ X)
    (hwidth : (K + 1) * H ≤ X + 1)
    (hsqrt :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        Real.sqrt (N : ℝ) < (X / 2 : ℕ))
    (hleft : X - H ≤ a)
    (hright : a + L ≤ X)
    (hcard :
      ∀ s ∈ Finset.Icc 2 K,
        s - 1 < (shiftedPrimePacket a L).card) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      paperTypeDefect N s ≤ 1 := by
  intro N s hpair
  rcases Finset.mem_biUnion.mp hpair with ⟨t, htK, hblock⟩
  have hst : s = t := (mem_quotientBlockPairs.mp hblock).1
  subst t
  have hsone : 1 ≤ s := by
    have hs2 := (Finset.mem_Icc.mp htK).1
    omega
  exact paperTypeDefect_le_one_of_prime_packet_subset
    (Finset.mem_Icc.mp htK).1
    (endpointPairSpace_cutoffInactive_of_sqrt_lt_half hsqrt hpair)
    (shiftedPrimePacket_subset_quotientInterval
      hsone hblock
      (endpointPairSpace_quotientLowerEndpoint_le_sub hHX hwidth hpair)
      hleft hright)
    (hcard s htK)

/-- **Weighted exceptional-endpoint consequence of the translated `J_eta`
construction.**  Outside `E`, each endpoint has one shifted packet satisfying
the scalar location/arithmetic hypotheses.  Then all positive-defect weighted
pairs lie over `E`, giving the exact finite inequality used before the
`o(Y)` argument in Section 6. -/
theorem positiveDefectWeightedPairs_card_le_bad_card_mul_of_shifted_packets_arithmetic
    {Y W : ℕ} {K H a L : ℕ → ℕ} {E : Finset ℕ}
    (hHX :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E → H X ≤ X)
    (hwidth :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        (K X + 1) * H X ≤ X + 1)
    (hsqrt :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X (K X) →
          Real.sqrt (N : ℝ) < (X / 2 : ℕ))
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
    exact endpointPairSpace_zero_of_shifted_prime_packet_arithmetic
      (X := X) (K := K X) (H := H X) (a := a X) (L := L X)
      (hHX X hXY hXE)
      (hwidth X hXY hXE)
      (hsqrt X hXY hXE)
      (hleft X hXY hXE)
      (hright X hXY hXE)
      (hcard X hXY hXE)
      hpair
  · exact hweight

end DivisorF
