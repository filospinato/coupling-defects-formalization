import DivisorF.QuotientIntervalTransfer
import DivisorF.MultiplicityCorollaries
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weighted quotient-pair density transfer

Project-original finite counting layer from Section 6.  The external almost-all
prime theorem is deliberately absent.  We parameterise the upper type cutoff by
an arbitrary function `K(X)`; the manuscript later takes `K(X)=⌊X^ρ⌋` (or the
corresponding cubic-cone cutoff).

For fixed endpoint `X` and type `s`, the `s` integers with quotient `X` are
exactly `sX, ..., sX+s-1`.  These blocks are disjoint both across types and
across endpoints.  Consequently the natural pair-space weight over endpoint
`X` is exactly `∑_{2≤s≤K(X)} s`.  The final theorem transfers any statement
that positive defect is confined to a finite set of bad endpoints into the
corresponding weighted counting bound.
-/

namespace DivisorF

open scoped BigOperators

/-- Pairs `(N,s)` in the exact quotient block with endpoint `X` and fixed type
`s`: `N=sX,...,sX+s-1`. -/
def quotientBlockPairs (X s : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico (s * X) (s * X + s)).image fun N => (N, s)

@[simp]
theorem mem_quotientBlockPairs
    {X s N t : ℕ} :
    (N, t) ∈ quotientBlockPairs X s ↔
      t = s ∧ s * X ≤ N ∧ N < s * X + s := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨M, hM, hpair⟩
    have hN : M = N := congrArg Prod.fst hpair
    have ht : s = t := congrArg Prod.snd hpair
    subst M
    exact ⟨ht.symm, (Finset.mem_Ico.mp hM).1, (Finset.mem_Ico.mp hM).2⟩
  · rintro ⟨rfl, hlo, hhi⟩
    apply Finset.mem_image.mpr
    exact ⟨N, Finset.mem_Ico.mpr ⟨hlo, hhi⟩, rfl⟩

/-- Every quotient block contains exactly `s` weighted pairs. -/
theorem quotientBlockPairs_card (X s : ℕ) :
    (quotientBlockPairs X s).card = s := by
  unfold quotientBlockPairs
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact congrArg Prod.fst h

/-- The block parametrisation really has quotient endpoint `X`. -/
theorem quotient_eq_of_mem_quotientBlockPairs
    {X s N : ℕ} (hs : 0 < s)
    (h : (N, s) ∈ quotientBlockPairs X s) :
    N / s = X := by
  have hb := (mem_quotientBlockPairs.mp h).2
  have hlo : s * X ≤ N := hb.1
  have hhi : N < s * (X + 1) := by
    simpa [Nat.mul_add] using hb.2
  have hle : X ≤ N / s :=
    (Nat.le_div_iff_mul_le hs).2 (by simpa [Nat.mul_comm] using hlo)
  have hlt : N / s < X + 1 :=
    (Nat.div_lt_iff_lt_mul hs).2 (by simpa [Nat.mul_comm] using hhi)
  omega

/-- All weighted pairs over one endpoint, with types `2≤s≤K`. -/
def endpointPairSpace (X K : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 2 K).biUnion fun s => quotientBlockPairs X s

/-- Distinct types give disjoint quotient blocks because the second coordinate
records the type. -/
theorem quotientBlockPairs_disjoint_of_ne
    {X s t : ℕ} (hst : s ≠ t) :
    Disjoint (quotientBlockPairs X s) (quotientBlockPairs X t) := by
  refine Finset.disjoint_left.2 ?_
  intro p hs ht
  rcases p with ⟨N, u⟩
  have hus : u = s := (mem_quotientBlockPairs.mp hs).1
  have hut : u = t := (mem_quotientBlockPairs.mp ht).1
  exact hst (hus.symm.trans hut)

/-- Exact natural weight over a fixed endpoint. -/
def endpointPairWeight (K : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 2 K, s

/-- The number of pairs above one endpoint is exactly the natural weight
`∑_{2≤s≤K} s`. -/
theorem endpointPairSpace_card (X K : ℕ) :
    (endpointPairSpace X K).card = endpointPairWeight K := by
  unfold endpointPairSpace endpointPairWeight
  calc
    ((Finset.Icc 2 K).biUnion fun s => quotientBlockPairs X s).card
        = ∑ s ∈ Finset.Icc 2 K, (quotientBlockPairs X s).card := by
            apply Finset.card_biUnion
            intro s _ t _ hst
            exact quotientBlockPairs_disjoint_of_ne hst
    _ = ∑ s ∈ Finset.Icc 2 K, s := by
          apply Finset.sum_congr rfl
          intro s _
          exact quotientBlockPairs_card X s

/-- Endpoint pair spaces for distinct endpoints are disjoint. -/
theorem endpointPairSpace_disjoint_of_ne
    {X Z KX KZ : ℕ} (hXZ : X ≠ Z) :
    Disjoint (endpointPairSpace X KX) (endpointPairSpace Z KZ) := by
  refine Finset.disjoint_left.2 ?_
  intro p hpX hpZ
  rcases Finset.mem_biUnion.mp hpX with ⟨s, hsK, hps⟩
  rcases Finset.mem_biUnion.mp hpZ with ⟨t, htK, hpt⟩
  rcases p with ⟨N, u⟩
  have hus : u = s := (mem_quotientBlockPairs.mp hps).1
  have hut : u = t := (mem_quotientBlockPairs.mp hpt).1
  have hst : s = t := hus.symm.trans hut
  subst t
  have hspos : 0 < s := by
    have := (Finset.mem_Icc.mp hsK).1
    omega
  have hNX : N / s = X := by
    have hps' : (N, s) ∈ quotientBlockPairs X s := by
      simpa [hus] using hps
    exact quotient_eq_of_mem_quotientBlockPairs hspos hps'
  have hNZ : N / s = Z := by
    have hpt' : (N, s) ∈ quotientBlockPairs Z s := by
      simpa [hus] using hpt
    exact quotient_eq_of_mem_quotientBlockPairs hspos hpt'
  exact hXZ (hNX.symm.trans hNZ)

/-- Weighted quotient-pair space over endpoints `Y≤X<2Y`, with a variable
upper type cutoff `K(X)`. -/
def weightedPairSpace (Y : ℕ) (K : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico Y (2 * Y)).biUnion fun X => endpointPairSpace X (K X)

/-- The parametrised weighted space is exactly the manuscript-style condition
on `(N,s)`: the quotient endpoint lies in `[Y,2Y)` and the type lies between
`2` and the cutoff attached to that endpoint. -/
theorem mem_weightedPairSpace
    {Y N s : ℕ} {K : ℕ → ℕ} :
    (N, s) ∈ weightedPairSpace Y K ↔
      Y ≤ N / s ∧ N / s < 2 * Y ∧ 2 ≤ s ∧ s ≤ K (N / s) := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨X, hXY, hpX⟩
    rcases Finset.mem_biUnion.mp hpX with ⟨t, htK, hblock⟩
    have hst : s = t := (mem_quotientBlockPairs.mp hblock).1
    subst t
    have hspos : 0 < s := by
      have := (Finset.mem_Icc.mp htK).1
      omega
    have hquot : N / s = X :=
      quotient_eq_of_mem_quotientBlockPairs hspos hblock
    have hXY' := Finset.mem_Ico.mp hXY
    have hsK := Finset.mem_Icc.mp htK
    simpa [hquot] using ⟨hXY'.1, hXY'.2, hsK.1, hsK.2⟩
  · rintro ⟨hY, h2Y, hs2, hsK⟩
    have hspos : 0 < s := by omega
    let X := N / s
    have hlo : s * X ≤ N := by
      simpa [X, Nat.mul_comm] using Nat.div_mul_le_self N s
    have hhi : N < s * X + s := by
      have h := (Nat.div_lt_iff_lt_mul hspos).1 (Nat.lt_succ_self (N / s))
      simpa [X, Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using h
    have hblock : (N, s) ∈ quotientBlockPairs X s :=
      mem_quotientBlockPairs.mpr ⟨rfl, hlo, hhi⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨X, Finset.mem_Ico.mpr ?_, ?_⟩
    · simpa [X] using ⟨hY, h2Y⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨s, Finset.mem_Icc.mpr ?_, hblock⟩
      simpa [X] using ⟨hs2, hsK⟩

/-- Exact cardinality identity for the weighted pair space.  This is the finite
form of the manuscript's double sum `∑_X ∑_s s`. -/
theorem weightedPairSpace_card
    (Y : ℕ) (K : ℕ → ℕ) :
    (weightedPairSpace Y K).card =
      ∑ X ∈ Finset.Ico Y (2 * Y), endpointPairWeight (K X) := by
  unfold weightedPairSpace
  calc
    ((Finset.Ico Y (2 * Y)).biUnion fun X => endpointPairSpace X (K X)).card
        = ∑ X ∈ Finset.Ico Y (2 * Y),
            (endpointPairSpace X (K X)).card := by
              apply Finset.card_biUnion
              intro X _ Z _ hXZ
              exact endpointPairSpace_disjoint_of_ne hXZ
    _ = ∑ X ∈ Finset.Ico Y (2 * Y), endpointPairWeight (K X) := by
          apply Finset.sum_congr rfl
          intro X _
          exact endpointPairSpace_card X (K X)

/-- Positive-defect pairs inside a weighted quotient-pair space.  The total
paper convention `paperTypeDefect=0` for empty quotient classes makes this
well-defined without choosing representatives. -/
noncomputable def positiveDefectWeightedPairs
    (Y : ℕ) (K : ℕ → ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (weightedPairSpace Y K).filter fun p => 0 < paperTypeDefect p.1 p.2

/-- Pairs lying above a designated finite set of bad endpoints. -/
def badEndpointPairSpace
    (Y : ℕ) (K : ℕ → ℕ) (E : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico Y (2 * Y)).filter fun X => X ∈ E).biUnion
    fun X => endpointPairSpace X (K X)

/-- Exact cardinality of the weighted pairs above the bad endpoints. -/
theorem badEndpointPairSpace_card
    (Y : ℕ) (K : ℕ → ℕ) (E : Finset ℕ) :
    (badEndpointPairSpace Y K E).card =
      ∑ X ∈ (Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E),
        endpointPairWeight (K X) := by
  unfold badEndpointPairSpace
  calc
    (((Finset.Ico Y (2 * Y)).filter fun X => X ∈ E).biUnion
        fun X => endpointPairSpace X (K X)).card
        = ∑ X ∈ (Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E),
            (endpointPairSpace X (K X)).card := by
              apply Finset.card_biUnion
              intro X _ Z _ hXZ
              exact endpointPairSpace_disjoint_of_ne hXZ
    _ = ∑ X ∈ (Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E),
          endpointPairWeight (K X) := by
          apply Finset.sum_congr rfl
          intro X _
          exact endpointPairSpace_card X (K X)

/-- **Section 6 weighted-density transfer, finite form.**

Suppose every admissible pair over every endpoint outside `E` has zero defect.
Then every positive-defect weighted pair lies over `E`, hence its cardinality
is bounded by the exact total endpoint weight of `E`.

The external almost-all theorem is used later only to show that `E` is sparse;
it is not part of this theorem. -/
theorem positiveDefectWeightedPairs_card_le_bad_weight
    {Y : ℕ} {K : ℕ → ℕ} {E : Finset ℕ}
    (hzero :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ s ∈ Finset.Icc 2 (K X),
          ∀ N : ℕ, (N, s) ∈ quotientBlockPairs X s →
            paperTypeDefect N s = 0) :
    (positiveDefectWeightedPairs Y K).card ≤
      ∑ X ∈ (Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E),
        endpointPairWeight (K X) := by
  classical
  have hsubset :
      positiveDefectWeightedPairs Y K ⊆ badEndpointPairSpace Y K E := by
    intro p hp
    have hpall : p ∈ weightedPairSpace Y K :=
      (Finset.mem_filter.mp hp).1
    have hpdef : 0 < paperTypeDefect p.1 p.2 :=
      (Finset.mem_filter.mp hp).2
    rcases Finset.mem_biUnion.mp hpall with ⟨X, hXY, hpX⟩
    by_cases hXE : X ∈ E
    · apply Finset.mem_biUnion.mpr
      refine ⟨X, Finset.mem_filter.mpr ⟨hXY, hXE⟩, hpX⟩
    · rcases Finset.mem_biUnion.mp hpX with ⟨s, hsK, hps⟩
      rcases p with ⟨N, t⟩
      have hts : t = s := (mem_quotientBlockPairs.mp hps).1
      subst t
      have hz := hzero X hXY hXE s hsK N hps
      rw [hz] at hpdef
      omega
  calc
    (positiveDefectWeightedPairs Y K).card
        ≤ (badEndpointPairSpace Y K E).card := Finset.card_le_card hsubset
    _ = ∑ X ∈ (Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E),
          endpointPairWeight (K X) := badEndpointPairSpace_card Y K E

/-- Coarser but useful weighted exceptional-endpoint bound: if every endpoint
carries at most weight `W`, then the positive-defect pair count is at most
`|E∩[Y,2Y)| * W`, and hence at most `|E|*W`. -/
theorem positiveDefectWeightedPairs_card_le_bad_card_mul
    {Y W : ℕ} {K : ℕ → ℕ} {E : Finset ℕ}
    (hzero :
      ∀ X ∈ Finset.Ico Y (2 * Y), X ∉ E →
        ∀ s ∈ Finset.Icc 2 (K X),
          ∀ N : ℕ, (N, s) ∈ quotientBlockPairs X s →
            paperTypeDefect N s = 0)
    (hweight : ∀ X ∈ Finset.Ico Y (2 * Y), endpointPairWeight (K X) ≤ W) :
    (positiveDefectWeightedPairs Y K).card ≤ E.card * W := by
  have hbad := positiveDefectWeightedPairs_card_le_bad_weight hzero
  calc
    (positiveDefectWeightedPairs Y K).card
        ≤ ∑ X ∈ (Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E),
            endpointPairWeight (K X) := hbad
    _ ≤ ∑ _X ∈ (Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E), W := by
          apply Finset.sum_le_sum
          intro X hX
          exact hweight X (Finset.mem_filter.mp hX).1
    _ = ((Finset.Ico Y (2 * Y)).filter (fun X => X ∈ E)).card * W := by
          simp
    _ ≤ E.card * W := by
          apply Nat.mul_le_mul_right W
          apply Finset.card_le_card
          intro X hX
          exact (Finset.mem_filter.mp hX).2

end DivisorF
