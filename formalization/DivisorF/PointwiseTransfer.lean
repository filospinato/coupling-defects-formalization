import DivisorF.MultiplicityBarrier
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite pointwise transfers from prime packing to defect bounds

Project-original transfer layer underlying Section 5.  Published short-interval
or explicit prime-counting results are intentionally absent: they may supply a
finite collection of primes or a lower bound for `t_s(N)`, while the theorems
below perform only the paper's new conversion from that input to zero/binary
defect through the same-type boundary budget.
-/

namespace DivisorF

/-- Any finite packet consisting entirely of quotient-type `s` primes injects
into `Q_s(N)`, hence its cardinality is a lower bound for `t_s(N)`. -/
theorem card_le_typeMultiplicity_of_same_type
    {N s : ℕ} (P : Finset (LargePrime N))
    (hP : ∀ q ∈ P, q.quotientType = s) :
    P.card ≤ typeMultiplicity N s := by
  unfold typeMultiplicity
  apply Finset.card_le_card
  intro q hq
  exact mem_typePrimes.mpr (hP q hq)

/-- A nonempty same-type packet certifies that the quotient type is occupied. -/
theorem typeOccupied_of_same_type_packet
    {N s : ℕ} {P : Finset (LargePrime N)}
    (hP : ∀ q ∈ P, q.quotientType = s)
    (hne : P.Nonempty) :
    TypeOccupied N s := by
  rcases hne with ⟨q, hq⟩
  exact ⟨q, mem_typePrimes.mpr (hP q hq)⟩

/-- A lower bound for the same-type multiplicity exceeding the exact zero
threshold transfers immediately to zero common defect. -/
theorem typeDefect_eq_zero_of_multiplicity_lower_bound
    {N s m : ℕ} (hocc : TypeOccupied N s)
    (hm : m ≤ typeMultiplicity N s)
    (hthreshold : 2 * (s - 1) < m) :
    typeDefect hocc = 0 := by
  exact typeDefect_eq_zero_of_large_multiplicity hocc
    (lt_of_lt_of_le hthreshold hm)

/-- Binary analogue of `typeDefect_eq_zero_of_multiplicity_lower_bound`. -/
theorem typeDefect_le_one_of_multiplicity_lower_bound
    {N s m : ℕ} (hocc : TypeOccupied N s)
    (hm : m ≤ typeMultiplicity N s)
    (hthreshold : s - 1 < m) :
    typeDefect hocc ≤ 1 := by
  exact typeDefect_le_one_of_large_multiplicity hocc
    (lt_of_lt_of_le hthreshold hm)

/-- Pointwise Section 5 transfer for an already specified large-prime fibre.
The external input is only the numerical lower bound for its quotient-type
multiplicity. -/
theorem fibreDefect_eq_zero_of_type_multiplicity_lower_bound
    {N s m : ℕ} {q : LargePrime N}
    (hq : q.quotientType = s)
    (hm : m ≤ typeMultiplicity N s)
    (hthreshold : 2 * (s - 1) < m) :
    fibreDefect q = 0 := by
  have hqmem : q ∈ typePrimes N s := mem_typePrimes.mpr hq
  have hocc : TypeOccupied N s := ⟨q, hqmem⟩
  rw [fibreDefect_eq_typeDefect hocc hqmem]
  exact typeDefect_eq_zero_of_multiplicity_lower_bound hocc hm hthreshold

/-- Binary pointwise counterpart of
`fibreDefect_eq_zero_of_type_multiplicity_lower_bound`. -/
theorem fibreDefect_le_one_of_type_multiplicity_lower_bound
    {N s m : ℕ} {q : LargePrime N}
    (hq : q.quotientType = s)
    (hm : m ≤ typeMultiplicity N s)
    (hthreshold : s - 1 < m) :
    fibreDefect q ≤ 1 := by
  have hqmem : q ∈ typePrimes N s := mem_typePrimes.mpr hq
  have hocc : TypeOccupied N s := ⟨q, hqmem⟩
  rw [fibreDefect_eq_typeDefect hocc hqmem]
  exact typeDefect_le_one_of_multiplicity_lower_bound hocc hm hthreshold

/-- Finite prime-packing form of the Section 5 zero-defect transfer.
A packet with more than `2(s-1)` same-type large primes forces `d_s(N)=0`.
No theorem asserting existence of such a packet is assumed here. -/
theorem typeDefect_eq_zero_of_same_type_packet
    {N s : ℕ} {P : Finset (LargePrime N)}
    (hP : ∀ q ∈ P, q.quotientType = s)
    (hcard : 2 * (s - 1) < P.card) :
    ∃ hocc : TypeOccupied N s, typeDefect hocc = 0 := by
  have hcardpos : 0 < P.card :=
    lt_of_le_of_lt (Nat.zero_le _) hcard
  have hocc : TypeOccupied N s :=
    typeOccupied_of_same_type_packet hP (Finset.card_pos.mp hcardpos)
  have hm : P.card ≤ typeMultiplicity N s :=
    card_le_typeMultiplicity_of_same_type P hP
  exact ⟨hocc,
    typeDefect_eq_zero_of_multiplicity_lower_bound hocc hm hcard⟩

/-- Finite prime-packing form of the binary-defect transfer.
A packet with more than `s-1` same-type large primes forces `d_s(N)≤1`. -/
theorem typeDefect_le_one_of_same_type_packet
    {N s : ℕ} {P : Finset (LargePrime N)}
    (hP : ∀ q ∈ P, q.quotientType = s)
    (hcard : s - 1 < P.card) :
    ∃ hocc : TypeOccupied N s, typeDefect hocc ≤ 1 := by
  have hcardpos : 0 < P.card :=
    lt_of_le_of_lt (Nat.zero_le _) hcard
  have hocc : TypeOccupied N s :=
    typeOccupied_of_same_type_packet hP (Finset.card_pos.mp hcardpos)
  have hm : P.card ≤ typeMultiplicity N s :=
    card_le_typeMultiplicity_of_same_type P hP
  exact ⟨hocc,
    typeDefect_le_one_of_multiplicity_lower_bound hocc hm hcard⟩

/-- A convenient Section 5 interface: an external prime-distribution result may
supply the lower bound `m ≤ t_s(N)`; once `m > 2(s-1)`, the project-original
conclusion is zero defect. -/
theorem pointwise_zero_defect_transfer
    {N s m : ℕ}
    (hmult : m ≤ typeMultiplicity N s)
    (hthreshold : 2 * (s - 1) < m) :
    ∃ hocc : TypeOccupied N s, typeDefect hocc = 0 := by
  have hpos : 0 < typeMultiplicity N s := by
    exact lt_of_lt_of_le
      (lt_of_le_of_lt (Nat.zero_le _) hthreshold)
      hmult
  have hnonempty : (typePrimes N s).Nonempty := by
    apply Finset.card_pos.mp
    simpa [typeMultiplicity] using hpos
  have hocc : TypeOccupied N s := by
    exact hnonempty
  exact ⟨hocc,
    typeDefect_eq_zero_of_multiplicity_lower_bound hocc hmult hthreshold⟩

/-- Binary counterpart of `pointwise_zero_defect_transfer`. -/
theorem pointwise_binary_defect_transfer
    {N s m : ℕ}
    (hmult : m ≤ typeMultiplicity N s)
    (hthreshold : s - 1 < m) :
    ∃ hocc : TypeOccupied N s, typeDefect hocc ≤ 1 := by
  have hpos : 0 < typeMultiplicity N s := by
    exact lt_of_lt_of_le
      (lt_of_le_of_lt (Nat.zero_le _) hthreshold)
      hmult
  have hnonempty : (typePrimes N s).Nonempty := by
    apply Finset.card_pos.mp
    simpa [typeMultiplicity] using hpos
  have hocc : TypeOccupied N s := by
    exact hnonempty
  exact ⟨hocc,
    typeDefect_le_one_of_multiplicity_lower_bound hocc hmult hthreshold⟩

end DivisorF
