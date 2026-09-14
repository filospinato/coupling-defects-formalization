import DivisorF.QuotientPrimeCounting
import DivisorF.WeightedPairDensity

set_option linter.style.header false

namespace DivisorF

/-- Ordinary primes in the translated integer interval `(X-H, X]`. -/
def translatedEndpointPrimePacket (X H : ℕ) : Finset ℕ :=
  (Finset.Ioc (X - H) X).filter Nat.Prime

@[simp]
theorem mem_translatedEndpointPrimePacket
    {X H p : ℕ} :
    p ∈ translatedEndpointPrimePacket X H ↔
      Nat.Prime p ∧ X - H < p ∧ p ≤ X := by
  simp only [translatedEndpointPrimePacket, Finset.mem_filter, Finset.mem_Ioc]
  aesop

/-- A sufficiently large ordinary-prime subset of the exact quotient interval
forces zero defect once the large-prime cutoff is inactive. -/
theorem paperTypeDefect_eq_zero_of_prime_packet_subset
    {N s : ℕ} (hs : 2 ≤ s)
    (hoff : LargePrimeCutoffInactive N s)
    {P : Finset ℕ}
    (hP : P ⊆ quotientIntervalPrimeValues N s)
    (hcard : 2 * (s - 1) < P.card) :
    paperTypeDefect N s = 0 := by
  apply paperTypeDefect_eq_zero_of_quotient_prime_count hs hoff
  exact lt_of_lt_of_le hcard (Finset.card_le_card hP)

/-- Binary counterpart of `paperTypeDefect_eq_zero_of_prime_packet_subset`. -/
theorem paperTypeDefect_le_one_of_prime_packet_subset
    {N s : ℕ} (hs : 2 ≤ s)
    (hoff : LargePrimeCutoffInactive N s)
    {P : Finset ℕ}
    (hP : P ⊆ quotientIntervalPrimeValues N s)
    (hcard : s - 1 < P.card) :
    paperTypeDefect N s ≤ 1 := by
  apply paperTypeDefect_le_one_of_quotient_prime_count hs hoff
  exact lt_of_lt_of_le hcard (Finset.card_le_card hP)

/-- Finite translated-interval embedding used in Section 6. -/
theorem translatedEndpointPrimePacket_subset_quotientInterval
    {N s X H : ℕ}
    (hs : 1 ≤ s)
    (hblock : (N, s) ∈ quotientBlockPairs X s)
    (hlower : N / (s + 1) ≤ X - H) :
    translatedEndpointPrimePacket X H ⊆ quotientIntervalPrimeValues N s := by
  intro p hp
  have hpdata := mem_translatedEndpointPrimePacket.mp hp
  have hNlower : s * X ≤ N := (mem_quotientBlockPairs.mp hblock).2.1
  have hNupper : N < s * X + s := (mem_quotientBlockPairs.mp hblock).2.2
  have hdivLower : X ≤ N / s := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < s)).2
    simpa [Nat.mul_comm] using hNlower
  have hdivUpper : N / s < X + 1 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < s)).2
    rw [Nat.add_mul, one_mul, Nat.mul_comm X s]
    exact hNupper
  have hdiv : N / s = X := by omega
  apply mem_quotientIntervalPrimeValues.mpr
  refine ⟨hpdata.1, ?_, ?_⟩
  · exact lt_of_le_of_lt hlower hpdata.2.1
  · simpa [hdiv] using hpdata.2.2

/-- Simultaneous finite regular-endpoint transfer from one common packet. -/
theorem endpointPairSpace_zero_of_common_prime_packet
    {X K : ℕ} {P : Finset ℕ}
    (hpacket :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        P ⊆ quotientIntervalPrimeValues N s)
    (hoff :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        LargePrimeCutoffInactive N s)
    (hcard :
      ∀ s ∈ Finset.Icc 2 K, 2 * (s - 1) < P.card) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      paperTypeDefect N s = 0 := by
  intro N s hpair
  rcases Finset.mem_biUnion.mp hpair with ⟨t, htK, hblock⟩
  have hst : s = t := (mem_quotientBlockPairs.mp hblock).1
  subst t
  exact paperTypeDefect_eq_zero_of_prime_packet_subset
    (Finset.mem_Icc.mp htK).1 (hoff hpair) (hpacket hpair) (hcard s htK)

/-- Translated-packet specialization of the simultaneous zero-defect transfer. -/
theorem endpointPairSpace_zero_of_translated_prime_packet
    {X K H : ℕ}
    (hlower :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        N / (s + 1) ≤ X - H)
    (hoff :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        LargePrimeCutoffInactive N s)
    (hcard :
      ∀ s ∈ Finset.Icc 2 K,
        2 * (s - 1) < (translatedEndpointPrimePacket X H).card) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      paperTypeDefect N s = 0 := by
  apply endpointPairSpace_zero_of_common_prime_packet
    (P := translatedEndpointPrimePacket X H)
  · intro N s hpair
    rcases Finset.mem_biUnion.mp hpair with ⟨t, htK, hblock⟩
    have hst : s = t := (mem_quotientBlockPairs.mp hblock).1
    subst t
    exact translatedEndpointPrimePacket_subset_quotientInterval
      (le_trans (by decide : 1 ≤ 2) (Finset.mem_Icc.mp htK).1)
      hblock (hlower hpair)
  · exact hoff
  · exact hcard

/-- Binary version of the simultaneous common-packet transfer. -/
theorem endpointPairSpace_binary_of_common_prime_packet
    {X K : ℕ} {P : Finset ℕ}
    (hpacket :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        P ⊆ quotientIntervalPrimeValues N s)
    (hoff :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        LargePrimeCutoffInactive N s)
    (hcard :
      ∀ s ∈ Finset.Icc 2 K, s - 1 < P.card) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      paperTypeDefect N s ≤ 1 := by
  intro N s hpair
  rcases Finset.mem_biUnion.mp hpair with ⟨t, htK, hblock⟩
  have hst : s = t := (mem_quotientBlockPairs.mp hblock).1
  subst t
  exact paperTypeDefect_le_one_of_prime_packet_subset
    (Finset.mem_Icc.mp htK).1 (hoff hpair) (hpacket hpair) (hcard s htK)

/-- Binary translated-packet counterpart. -/
theorem endpointPairSpace_binary_of_translated_prime_packet
    {X K H : ℕ}
    (hlower :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        N / (s + 1) ≤ X - H)
    (hoff :
      ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
        LargePrimeCutoffInactive N s)
    (hcard :
      ∀ s ∈ Finset.Icc 2 K,
        s - 1 < (translatedEndpointPrimePacket X H).card) :
    ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X K →
      paperTypeDefect N s ≤ 1 := by
  apply endpointPairSpace_binary_of_common_prime_packet
    (P := translatedEndpointPrimePacket X H)
  · intro N s hpair
    rcases Finset.mem_biUnion.mp hpair with ⟨t, htK, hblock⟩
    have hst : s = t := (mem_quotientBlockPairs.mp hblock).1
    subst t
    exact translatedEndpointPrimePacket_subset_quotientInterval
      (le_trans (by decide : 1 ≤ 2) (Finset.mem_Icc.mp htK).1)
      hblock (hlower hpair)
  · exact hoff
  · exact hcard

/-- Weighted exceptional-endpoint bound from common packets. -/
theorem positiveDefectWeightedPairs_card_le_bad_card_mul_of_common_packets
    {Y W : ℕ} {K : ℕ → ℕ} {E : Finset ℕ}
    {P : ℕ → Finset ℕ}
    (hpacket :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X (K X) →
          P X ⊆ quotientIntervalPrimeValues N s)
    (hoff :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X (K X) →
          LargePrimeCutoffInactive N s)
    (hcard :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ s ∈ Finset.Icc 2 (K X), 2 * (s - 1) < (P X).card)
    (hweight :
      ∀ X ∈ Finset.Ico Y (2 * Y), endpointPairWeight (K X) ≤ W) :
    (positiveDefectWeightedPairs Y K).card ≤ E.card * W := by
  apply positiveDefectWeightedPairs_card_le_bad_card_mul
  · intro X hXY hXE s hs N hblock
    have hpair : (N, s) ∈ endpointPairSpace X (K X) := by
      apply Finset.mem_biUnion.mpr
      exact ⟨s, hs, hblock⟩
    exact endpointPairSpace_zero_of_common_prime_packet
      (P := P X)
      (hpacket X hXY hXE)
      (hoff X hXY hXE)
      (hcard X hXY hXE)
      hpair
  · exact hweight

/-- Weighted exceptional-endpoint bound specialized to translated packets. -/
theorem positiveDefectWeightedPairs_card_le_bad_card_mul_of_translated_packets
    {Y W : ℕ} {K H : ℕ → ℕ} {E : Finset ℕ}
    (hlower :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X (K X) →
          N / (s + 1) ≤ X - H X)
    (hoff :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ {N s : ℕ}, (N, s) ∈ endpointPairSpace X (K X) →
          LargePrimeCutoffInactive N s)
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
    exact endpointPairSpace_zero_of_translated_prime_packet
      (X := X) (K := K X) (H := H X)
      (hlower X hXY hXE)
      (hoff X hXY hXE)
      (hcard X hXY hXE)
      hpair
  · exact hweight

end DivisorF
