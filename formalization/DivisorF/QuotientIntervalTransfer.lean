import DivisorF.QuotientPairDiscretization

set_option linter.style.header false

/-!
# Quotient-interval prime-packing transfers

This is the project-original finite interface used by Sections 5 and 6.
Published prime-distribution theorems may provide many primes in the exact
quotient interval; the statements below convert only that finite input into
zero/binary coupling defect.
-/

namespace DivisorF

/-- A finite packet of large primes lying in the exact quotient interval is a
same-type packet. -/
theorem same_type_of_quotient_interval_packet
    {N s : ℕ} (hs : 0 < s)
    {P : Finset (LargePrime N)}
    (hP : ∀ q ∈ P, N / (s + 1) < q.val ∧ q.val ≤ N / s) :
    ∀ q ∈ P, q.quotientType = s := by
  intro q hq
  exact mem_typePrimes.mp
    ((mem_typePrimes_iff_quotient_interval hs).2 (hP q hq))

/-- A quotient-interval packet with more than `2(s-1)` large primes forces the
common quotient-type defect to vanish.  The existence/cardinality of the
packet is the only place where an external prime theorem may enter. -/
theorem typeDefect_eq_zero_of_quotient_interval_packet
    {N s : ℕ} (hs : 0 < s)
    {P : Finset (LargePrime N)}
    (hP : ∀ q ∈ P, N / (s + 1) < q.val ∧ q.val ≤ N / s)
    (hcard : 2 * (s - 1) < P.card) :
    ∃ hocc : TypeOccupied N s, typeDefect hocc = 0 := by
  exact typeDefect_eq_zero_of_same_type_packet
    (same_type_of_quotient_interval_packet hs hP) hcard

/-- Binary counterpart of
`typeDefect_eq_zero_of_quotient_interval_packet`. -/
theorem typeDefect_le_one_of_quotient_interval_packet
    {N s : ℕ} (hs : 0 < s)
    {P : Finset (LargePrime N)}
    (hP : ∀ q ∈ P, N / (s + 1) < q.val ∧ q.val ≤ N / s)
    (hcard : s - 1 < P.card) :
    ∃ hocc : TypeOccupied N s, typeDefect hocc ≤ 1 := by
  exact typeDefect_le_one_of_same_type_packet
    (same_type_of_quotient_interval_packet hs hP) hcard

/-- Pointwise zero-defect transfer for a target fibre of quotient type `s`
once an external input supplies a sufficiently large prime packet in the exact
quotient interval. -/
theorem fibreDefect_eq_zero_of_quotient_interval_packet
    {N s : ℕ} (hs : 0 < s)
    {q : LargePrime N} (hq : q.quotientType = s)
    {P : Finset (LargePrime N)}
    (hP : ∀ p ∈ P, N / (s + 1) < p.val ∧ p.val ≤ N / s)
    (hcard : 2 * (s - 1) < P.card) :
    fibreDefect q = 0 := by
  have hm : P.card ≤ typeMultiplicity N s :=
    card_le_typeMultiplicity_of_same_type P
      (same_type_of_quotient_interval_packet hs hP)
  exact fibreDefect_eq_zero_of_type_multiplicity_lower_bound
    hq hm hcard

/-- Pointwise binary transfer from a quotient-interval packet. -/
theorem fibreDefect_le_one_of_quotient_interval_packet
    {N s : ℕ} (hs : 0 < s)
    {q : LargePrime N} (hq : q.quotientType = s)
    {P : Finset (LargePrime N)}
    (hP : ∀ p ∈ P, N / (s + 1) < p.val ∧ p.val ≤ N / s)
    (hcard : s - 1 < P.card) :
    fibreDefect q ≤ 1 := by
  have hm : P.card ≤ typeMultiplicity N s :=
    card_le_typeMultiplicity_of_same_type P
      (same_type_of_quotient_interval_packet hs hP)
  exact fibreDefect_le_one_of_type_multiplicity_lower_bound
    hq hm hcard

/-- Exact Section 6 endpoint form: under `N=sX+u`, a packet known to lie in
`(floor(N/(s+1)), X]` is already a type-`s` packet because `X=floor(N/s)`;
therefore the usual multiplicity threshold transfers it to zero defect. -/
theorem zero_defect_transfer_from_decomposed_quotient_interval
    {N s X u : ℕ}
    (hs : 0 < s) (hu : u < s) (hN : N = s * X + u)
    {P : Finset (LargePrime N)}
    (hP : ∀ p ∈ P, N / (s + 1) < p.val ∧ p.val ≤ X)
    (hcard : 2 * (s - 1) < P.card) :
    ∃ hocc : TypeOccupied N s, typeDefect hocc = 0 := by
  have hNlt : N < (X + 1) * s := by
    rw [hN]
    nlinarith
  have hdivlt : N / s < X + 1 :=
    (Nat.div_lt_iff_lt_mul hs).2 hNlt
  have hXle : X ≤ N / s := by
    apply (Nat.le_div_iff_mul_le hs).2
    rw [hN]
    nlinarith
  have hXs : N / s = X := by omega
  apply typeDefect_eq_zero_of_quotient_interval_packet hs
  · intro p hp
    have hpI := hP p hp
    simpa [hXs] using hpI
  · exact hcard

end DivisorF
