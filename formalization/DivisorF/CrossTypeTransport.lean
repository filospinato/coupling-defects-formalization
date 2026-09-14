import DivisorF.VertexSensitivity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Theorem 5.2: cross-type transport

Let `sqrt N < q < p <= N` be primes of quotient types `s = ⌊N/q⌋` and
`t = ⌊N/p⌋`.  The manuscript compares the two fibre complements directly:
after deleting the `s - t` tail vertices

```text
T_q(t) = {(t+1)q, ..., sq}
```

from `R_{N,p}`, the map fixing everything outside both fibres and sending
`aq` to `ap` for `1 <= a <= t` is an induced-graph isomorphism onto
`R_{N,q}`.  Vertex sensitivity (`DivisorF.VertexSensitivity`) then bounds
`|P(R_{N,q}) - P(R_{N,p})|` by `s - t`, and the defect definition turns that
into

```text
|(D_N(q) - F(s)) - (D_N(p) - F(t))| <= s - t,
```

whence `|D_N(q) - D_N(p)| <= 2(s - t)` because `F` is `1`-Lipschitz.

The isomorphism is the mathematical content, and it is built here rather than
assumed.  It is the cross-type analogue of `swapFibreVertex`, which handles the
*equal*-type case in `DivisorF.Fibre`; the difference is that here the two
fibres have different sizes, so the larger one has to be truncated first.
-/

namespace DivisorF

open SimpleGraph

variable {N : ℕ}

/-! ### The quotient types are ordered -/

/-- A larger large prime has a smaller quotient type. -/
theorem quotientType_le_of_val_le {q p : LargePrime N} (h : q.val ≤ p.val) :
    p.quotientType ≤ q.quotientType :=
  Nat.div_le_div_left h q.pos

/-- The quotient type is smaller than the prime: `s < q`. -/
theorem quotientType_lt_val (q : LargePrime N) : q.quotientType < q.val := by
  apply (Nat.div_lt_iff_lt_mul q.pos).2
  exact q.large

/-! ### The cross-type vertex map -/

/-- The manuscript's transport map.  A fibre vertex `aq` with `a <= t` is sent
to `ap`; every other vertex is fixed. -/
noncomputable def crossTypeVertex (q p : LargePrime N) (v : HVertex N) :
    HVertex N := by
  classical
  by_cases hv : InFibre q v ∧ fibreCoefficient q v ≤ p.quotientType
  · exact HVertex.ofValue
      (fibre_value_bounds p (fibreCoefficient_pos q hv.1) hv.2).1
      (fibre_value_bounds p (fibreCoefficient_pos q hv.1) hv.2).2
  · exact v

@[simp]
theorem crossTypeVertex_value_of_mem (q p : LargePrime N) {v : HVertex N}
    (hq : InFibre q v) (hle : fibreCoefficient q v ≤ p.quotientType) :
    (crossTypeVertex q p v).value = fibreCoefficient q v * p.val := by
  simp [crossTypeVertex, hq, hle]

theorem crossTypeVertex_of_not_mem (q p : LargePrime N) {v : HVertex N}
    (h : ¬ (InFibre q v ∧ fibreCoefficient q v ≤ p.quotientType)) :
    crossTypeVertex q p v = v := by
  simp [crossTypeVertex, h]

theorem crossTypeVertex_mem_target (q p : LargePrime N) {v : HVertex N}
    (hq : InFibre q v) (hle : fibreCoefficient q v ≤ p.quotientType) :
    InFibre p (crossTypeVertex q p v) := by
  rw [InFibre, crossTypeVertex_value_of_mem q p hq hle]
  exact ⟨fibreCoefficient q v, by simp [Nat.mul_comm]⟩

theorem crossTypeVertex_coefficient (q p : LargePrime N) {v : HVertex N}
    (hq : InFibre q v) (hle : fibreCoefficient q v ≤ p.quotientType) :
    fibreCoefficient p (crossTypeVertex q p v) = fibreCoefficient q v := by
  unfold fibreCoefficient
  rw [crossTypeVertex_value_of_mem q p hq hle]
  exact Nat.mul_div_cancel _ p.pos

theorem crossTypeVertex_not_mem_source (q p : LargePrime N)
    (hqp : q.val ≠ p.val) {v : HVertex N}
    (hq : InFibre q v) (hle : fibreCoefficient q v ≤ p.quotientType) :
    ¬ InFibre q (crossTypeVertex q p v) := by
  rw [InFibre, crossTypeVertex_value_of_mem q p hq hle]
  intro hdvd
  rcases q.prime.dvd_mul.mp hdvd with hcoeff | hprime
  · exact (Nat.not_dvd_of_pos_of_lt (fibreCoefficient_pos q hq)
      (fibreCoefficient_lt_largePrime q q hq)) hcoeff
  · rcases (Nat.dvd_prime p.prime).mp hprime with hq_one | hq_eq
    · exact q.ne_one hq_one
    · exact hqp hq_eq

/-! ### The truncated complement -/

/-- Vertices of `R_{N,p}` surviving the deletion of the `q`-tail `T_q(t)`,
`t = ⌊N/p⌋`. -/
def TruncKeep (q p : LargePrime N) (w : {v : HVertex N // ¬ InFibre p v}) : Prop :=
  ¬ (InFibre q w.1 ∧ p.quotientType < fibreCoefficient q w.1)

instance (q p : LargePrime N) : DecidablePred (TruncKeep q p) := by
  intro w
  unfold TruncKeep
  infer_instance

/-- On the truncated complement, every fibre coefficient is admissible. -/
theorem coefficient_le_of_truncKeep {q p : LargePrime N}
    {w : {v : HVertex N // ¬ InFibre p v}} (hw : TruncKeep q p w)
    (hq : InFibre q w.1) :
    fibreCoefficient q w.1 ≤ p.quotientType :=
  Nat.le_of_not_lt fun hlt => hw ⟨hq, hlt⟩

/-- A deleted vertex is exactly a `q`-fibre vertex of the tail. -/
theorem not_truncKeep_iff {q p : LargePrime N}
    {w : {v : HVertex N // ¬ InFibre p v}} :
    ¬ TruncKeep q p w ↔
      InFibre q w.1 ∧ p.quotientType < fibreCoefficient q w.1 :=
  not_not

/-- The transport map lands in `R_{N,q}`. -/
theorem crossTypeVertex_not_inFibre_source {q p : LargePrime N}
    (hqp : q.val ≠ p.val) {w : {v : HVertex N // ¬ InFibre p v}}
    (hw : TruncKeep q p w) :
    ¬ InFibre q (crossTypeVertex q p w.1) := by
  by_cases hq : InFibre q w.1
  · exact crossTypeVertex_not_mem_source q p hqp hq (coefficient_le_of_truncKeep hw hq)
  · rw [crossTypeVertex_of_not_mem q p (fun h => hq h.1)]
    exact hq

/-- The transport map, as a function between the two subtypes. -/
noncomputable def truncToComplement (q p : LargePrime N) (hqp : q.val ≠ p.val)
    (w : {w : {v : HVertex N // ¬ InFibre p v} // TruncKeep q p w}) :
    {v : HVertex N // ¬ InFibre q v} :=
  ⟨crossTypeVertex q p w.1.1, crossTypeVertex_not_inFibre_source hqp w.2⟩

/-! ### Injectivity and surjectivity -/

theorem truncToComplement_injective (q p : LargePrime N) (hqp : q.val ≠ p.val) :
    Function.Injective (truncToComplement q p hqp) := by
  intro w₁ w₂ hw
  have hval : (crossTypeVertex q p w₁.1.1).value = (crossTypeVertex q p w₂.1.1).value := by
    rw [show crossTypeVertex q p w₁.1.1 = crossTypeVertex q p w₂.1.1 from
      congrArg Subtype.val hw]
  apply Subtype.ext
  apply Subtype.ext
  apply HVertex.ext_value
  by_cases h₁ : InFibre q w₁.1.1 <;> by_cases h₂ : InFibre q w₂.1.1
  · have hle₁ := coefficient_le_of_truncKeep w₁.2 h₁
    have hle₂ := coefficient_le_of_truncKeep w₂.2 h₂
    rw [crossTypeVertex_value_of_mem q p h₁ hle₁,
      crossTypeVertex_value_of_mem q p h₂ hle₂] at hval
    have hcoeff : fibreCoefficient q w₁.1.1 = fibreCoefficient q w₂.1.1 :=
      Nat.eq_of_mul_eq_mul_right p.pos hval
    rw [value_eq_prime_mul_coefficient q h₁, value_eq_prime_mul_coefficient q h₂,
      hcoeff]
  · exact absurd (by
      rw [crossTypeVertex_of_not_mem q p (fun h => h₂ h.1)] at hval
      have hmem := crossTypeVertex_mem_target q p h₁ (coefficient_le_of_truncKeep w₁.2 h₁)
      rw [InFibre] at hmem
      rw [hval] at hmem
      exact hmem) w₂.1.2
  · exact absurd (by
      rw [crossTypeVertex_of_not_mem q p (fun h => h₁ h.1)] at hval
      have hmem := crossTypeVertex_mem_target q p h₂ (coefficient_le_of_truncKeep w₂.2 h₂)
      rw [InFibre] at hmem
      rw [← hval] at hmem
      exact hmem) w₁.1.2
  · rw [crossTypeVertex_of_not_mem q p (fun h => h₁ h.1),
      crossTypeVertex_of_not_mem q p (fun h => h₂ h.1)] at hval
    exact hval

theorem truncToComplement_surjective (q p : LargePrime N) (hqp : q.val ≠ p.val)
    (hle : p.quotientType ≤ q.quotientType) :
    Function.Surjective (truncToComplement q p hqp) := by
  intro y
  by_cases hy : InFibre p y.1
  · -- `y = bp` with `1 ≤ b ≤ t`; its preimage is `bq`.
    set b := fibreCoefficient p y.1 with hb
    have hb_pos : 0 < b := fibreCoefficient_pos p hy
    have hb_le : b ≤ p.quotientType := fibreCoefficient_le_quotientType p hy
    have hb_le_q : b ≤ q.quotientType := le_trans hb_le hle
    have hbounds := fibre_value_bounds q hb_pos hb_le_q
    set v : HVertex N := HVertex.ofValue hbounds.1 hbounds.2 with hv
    have hvval : v.value = b * q.val := by simp [hv]
    have hvq : InFibre q v := by
      rw [InFibre, hvval]
      exact ⟨b, by simp [Nat.mul_comm]⟩
    have hvcoeff : fibreCoefficient q v = b := by
      unfold fibreCoefficient
      rw [hvval]
      exact Nat.mul_div_cancel _ q.pos
    have hvp : ¬ InFibre p v := by
      rw [InFibre, hvval]
      intro hdvd
      rcases p.prime.dvd_mul.mp hdvd with hcoeff | hprime
      · exact (Nat.not_dvd_of_pos_of_lt hb_pos
          (lt_of_le_of_lt hb_le (quotientType_lt_val p))) hcoeff
      · rcases (Nat.dvd_prime q.prime).mp hprime with hp_one | hp_eq
        · exact p.ne_one hp_one
        · exact hqp hp_eq.symm
    have hkeep : TruncKeep q p ⟨v, hvp⟩ := by
      rintro ⟨-, hgt⟩
      simp only [hvcoeff] at hgt
      omega
    refine ⟨⟨⟨v, hvp⟩, hkeep⟩, ?_⟩
    apply Subtype.ext
    apply HVertex.ext_value
    change (crossTypeVertex q p v).value = y.1.value
    rw [crossTypeVertex_value_of_mem q p hvq (by simpa [hvcoeff] using hb_le),
      hvcoeff, Nat.mul_comm, hb]
    exact (value_eq_prime_mul_coefficient p hy).symm
  · -- `y` lies outside both fibres and is its own preimage.
    have hkeep : TruncKeep q p ⟨y.1, hy⟩ := fun hcon => y.2 hcon.1
    refine ⟨⟨⟨y.1, hy⟩, hkeep⟩, ?_⟩
    apply Subtype.ext
    change crossTypeVertex q p y.1 = y.1
    exact crossTypeVertex_of_not_mem q p (fun h => y.2 h.1)

/-! ### Adjacency -/

theorem truncToComplement_adj_iff (q p : LargePrime N) (_hqp : q.val ≠ p.val)
    (w₁ w₂ : {w : {v : HVertex N // ¬ InFibre p v} // TruncKeep q p w}) :
    (reducedDivisorGraph N).Adj
        (crossTypeVertex q p w₁.1.1) (crossTypeVertex q p w₂.1.1) ↔
      (reducedDivisorGraph N).Adj w₁.1.1 w₂.1.1 := by
  by_cases h₁ : InFibre q w₁.1.1 <;> by_cases h₂ : InFibre q w₂.1.1
  · have hle₁ := coefficient_le_of_truncKeep w₁.2 h₁
    have hle₂ := coefficient_le_of_truncKeep w₂.2 h₂
    rw [same_fibre_adj_iff p (crossTypeVertex_mem_target q p h₁ hle₁)
      (crossTypeVertex_mem_target q p h₂ hle₂),
      same_fibre_adj_iff q h₁ h₂,
      crossTypeVertex_coefficient q p h₁ hle₁,
      crossTypeVertex_coefficient q p h₂ hle₂]
  · have hle₁ := coefficient_le_of_truncKeep w₁.2 h₁
    rw [crossTypeVertex_of_not_mem q p (fun h => h₂ h.1)]
    have hout :=
      outside_adj_fibre_iff p (crossTypeVertex_mem_target q p h₁ hle₁) w₂.1.2
    rw [crossTypeVertex_coefficient q p h₁ hle₁] at hout
    constructor
    · intro hadj
      exact ((outside_adj_fibre_iff q h₁ h₂).2 (hout.1 hadj.symm)).symm
    · intro hadj
      exact (hout.2 ((outside_adj_fibre_iff q h₁ h₂).1 hadj.symm)).symm
  · have hle₂ := coefficient_le_of_truncKeep w₂.2 h₂
    rw [crossTypeVertex_of_not_mem q p (fun h => h₁ h.1)]
    rw [outside_adj_fibre_iff p (crossTypeVertex_mem_target q p h₂ hle₂) w₁.1.2,
      outside_adj_fibre_iff q h₂ h₁,
      crossTypeVertex_coefficient q p h₂ hle₂]
  · rw [crossTypeVertex_of_not_mem q p (fun h => h₁ h.1),
      crossTypeVertex_of_not_mem q p (fun h => h₂ h.1)]

/-! ### The isomorphism -/

/-- **The manuscript's induced-graph isomorphism `R_{N,p} - T_q(t) ≅ R_{N,q}`.**

It fixes every vertex outside both fibres and sends `aq` to `ap` for
`1 <= a <= t`. -/
noncomputable def truncatedComplementIso (q p : LargePrime N) (hqp : q.val ≠ p.val)
    (hle : p.quotientType ≤ q.quotientType) :
    (fibreComplement p).induce {w | TruncKeep q p w} ≃g fibreComplement q where
  toEquiv :=
    Equiv.ofBijective (truncToComplement q p hqp)
      ⟨truncToComplement_injective q p hqp,
        truncToComplement_surjective q p hqp hle⟩
  map_rel_iff' := by
    intro w₁ w₂
    exact truncToComplement_adj_iff q p hqp w₁ w₂

/-! ### Counting the deleted tail -/

/-- The deletion removes at most `s - t` vertices: they are the tail
`{aq : t < a ≤ s}`. -/
theorem card_truncDeleted_le (q p : LargePrime N) :
    Fintype.card {w : {v : HVertex N // ¬ InFibre p v} // ¬ TruncKeep q p w}
      ≤ q.quotientType - p.quotientType := by
  classical
  rw [Fintype.card_subtype]
  rw [← Nat.card_Ioc p.quotientType q.quotientType]
  apply Finset.card_le_card_of_injOn (fun w => fibreCoefficient q w.1)
  · intro w hw
    simp only [Finset.coe_filter,
      Set.mem_setOf_eq, Finset.mem_univ, true_and] at hw
    obtain ⟨hq, hgt⟩ := not_truncKeep_iff.mp hw
    exact Finset.mem_Ioc.mpr ⟨hgt, fibreCoefficient_le_quotientType q hq⟩
  · intro w₁ hw₁ w₂ hw₂ hcoeff
    simp only [Finset.coe_filter,
      Set.mem_setOf_eq, Finset.mem_univ, true_and] at hw₁ hw₂
    have hq₁ : InFibre q w₁.1 := (not_truncKeep_iff.mp hw₁).1
    have hq₂ : InFibre q w₂.1 := (not_truncKeep_iff.mp hw₂).1
    have hcoeff' : fibreCoefficient q w₁.1 = fibreCoefficient q w₂.1 := hcoeff
    apply Subtype.ext
    apply HVertex.ext_value
    rw [value_eq_prime_mul_coefficient q hq₁, value_eq_prime_mul_coefficient q hq₂,
      hcoeff']

/-! ### Theorem 5.2 -/

/-- The complement path numbers of two large-prime fibres differ by at most
`s - t`.  This is the manuscript's Theorem 5.2, Step 1. -/
theorem abs_complement_pathPartitionNumber_sub_le (q p : LargePrime N)
    (hqp : q.val ≠ p.val) (hle : p.quotientType ≤ q.quotientType) :
    |(pathPartitionNumber (fibreComplement q) : ℤ)
        - pathPartitionNumber (fibreComplement p)|
      ≤ (q.quotientType : ℤ) - p.quotientType := by
  classical
  have hsens :=
    vertexSensitivity_pathPartitionNumber (fibreComplement p) (TruncKeep q p)
  have hiso : pathPartitionNumber
      ((fibreComplement p).induce {w | TruncKeep q p w})
      = pathPartitionNumber (fibreComplement q) :=
    pathPartitionNumber_iso (truncatedComplementIso q p hqp hle)
  have hcard := card_truncDeleted_le q p
  have hcardZ : (Fintype.card {w : {v : HVertex N // ¬ InFibre p v} // ¬ TruncKeep q p w} : ℤ)
      ≤ (q.quotientType : ℤ) - p.quotientType := by
    have : ((q.quotientType - p.quotientType : ℕ) : ℤ)
        = (q.quotientType : ℤ) - p.quotientType := by omega
    omega
  rw [hiso] at hsens
  rw [abs_le] at hsens ⊢
  omega

/-- **Theorem 5.2 (cross-type transport).**

For large primes `q < p` of quotient types `s ≥ t`,

```text
|(D_N(q) - F(s)) - (D_N(p) - F(t))| ≤ s - t.
```
-/
theorem crossTypeTransport (q p : LargePrime N) (hqp : q.val < p.val) :
    p.quotientType ≤ q.quotientType ∧
      |(fibreDefect q - (divisorPathPartitionNumber q.quotientType : ℤ))
          - (fibreDefect p - (divisorPathPartitionNumber p.quotientType : ℤ))|
        ≤ (q.quotientType : ℤ) - p.quotientType := by
  have hle : p.quotientType ≤ q.quotientType :=
    quotientType_le_of_val_le (le_of_lt hqp)
  refine ⟨hle, ?_⟩
  have hq := fibreDefect_eq_pathPartitionForm q
  have hp := fibreDefect_eq_pathPartitionForm p
  have hcomp :=
    abs_complement_pathPartitionNumber_sub_le q p (Nat.ne_of_lt hqp) hle
  rw [hq, hp]
  rw [abs_le] at hcomp ⊢
  omega

/-- **Theorem 5.2, second display.**

```text
|D_N(q) - D_N(p)| ≤ 2(s - t).
```

The extra factor of two is the `1`-Lipschitz property of `F`. -/
theorem crossTypeDefectLipschitz (q p : LargePrime N) (hqp : q.val < p.val) :
    |fibreDefect q - fibreDefect p|
      ≤ 2 * ((q.quotientType : ℤ) - p.quotientType) := by
  obtain ⟨hle, htransport⟩ := crossTypeTransport q p hqp
  have hF := abs_divisorPathPartitionNumber_sub_le hle
  rw [abs_le] at hF htransport ⊢
  omega

end DivisorF
