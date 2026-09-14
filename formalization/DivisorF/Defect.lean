import DivisorF.Fibre
import DivisorF.LinearForest
import DivisorF.Crossing
import DivisorF.Split

set_option linter.style.header false

/-!
# Fibre defect

The defect is defined in `ℤ`, rather than with truncated natural subtraction.
Consequently, the later nonnegativity theorem will certify a genuine
inequality instead of making it true by representation.
-/

namespace DivisorF

/-- The graph induced by the complement of the complete fibre `B_q(N)`. -/
def fibreComplement {N : ℕ} (q : LargePrime N) :
    SimpleGraph {v : HVertex N // ¬InFibre q v} :=
  (reducedDivisorGraph N).induce {v | ¬InFibre q v}

/-- The same-type fibre swap restricts to an isomorphism of fibre complements. -/
noncomputable def sameTypeComplementIso {N : ℕ} (q r : LargePrime N)
    (htype : q.quotientType = r.quotientType) (hqr : q.val ≠ r.val) :
    fibreComplement q ≃g fibreComplement r :=
  (sameTypeFibreIso q r htype hqr).induce
    (swapFibreVertex_complement_bijOn q r htype hqr)

/--
`D_N(q) = λ(H_N) - λ(R_{N,q}) - λ(G_s)`, represented in `ℤ` so that no
subtraction is silently truncated.
-/
noncomputable def fibreDefect {N : ℕ} (q : LargePrime N) : ℤ := by
  classical
  exact (linearForestNumber (reducedDivisorGraph N) : ℤ)
    - linearForestNumber (fibreComplement q)
    - linearForestNumber (divisorGraph q.quotientType)

/--
The quotient-type contribution to the defect may be read either on the fibre
itself or on `G_s`.
-/
theorem linearForestNumber_quotientType {N : ℕ} (q : LargePrime N) :
    linearForestNumber (divisorGraph q.quotientType) = linearForestNumber (fibreGraph q) :=
  (linearForestNumber_iso (fibreIso q)).symm

/--
**Lemma 2.4 of the paper.**  `D_N(q) ≥ 0`.

A maximum linear forest of `R_{N,q}` and a maximum linear forest of `B_q(N)`
have disjoint vertex sets, so their disjoint union is a spanning linear forest
of `H_N`.  Hence `λ(H_N) ≥ λ(R_{N,q}) + λ(G_s)`.

The inequality is genuine: `fibreDefect` lives in `ℤ`, so nothing here is true
by truncation.
-/
theorem fibreDefect_nonneg {N : ℕ} (q : LargePrime N) : 0 ≤ fibreDefect q := by
  classical
  have hsplit :
      linearForestNumber (fibreGraph q) + linearForestNumber (fibreComplement q)
        ≤ linearForestNumber (reducedDivisorGraph N) :=
    linearForestNumber_induce_add_induce_le (reducedDivisorGraph N) (InFibre q)
  unfold fibreDefect
  rw [linearForestNumber_quotientType q]
  omega

/-- `m_L(q)`, the number of selected fibre crossings of `L`. -/
noncomputable def crossingCount {N : ℕ} (q : LargePrime N)
    (L : SimpleGraph (HVertex N)) : ℕ :=
  crossingCard L (InFibre q)

/-- `i_L(q)`, the fibre restriction loss, in `ℤ`. -/
noncomputable def fibreRestrictionLoss {N : ℕ} (q : LargePrime N)
    (L : SimpleGraph (HVertex N)) : ℤ :=
  (linearForestNumber (divisorGraph q.quotientType) : ℤ)
    - edgeCard (L.induce {v | InFibre q v})

/-- `r_L(q)`, the complement restriction loss, in `ℤ`. -/
noncomputable def complementRestrictionLoss {N : ℕ} (q : LargePrime N)
    (L : SimpleGraph (HVertex N)) : ℤ :=
  (linearForestNumber (fibreComplement q) : ℤ)
    - edgeCard (L.induce {v | ¬ InFibre q v})

theorem fibreRestrictionLoss_nonneg {N : ℕ} (q : LargePrime N)
    {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    0 ≤ fibreRestrictionLoss q L := by
  have h : edgeCard (L.induce {v | InFibre q v}) ≤ linearForestNumber (fibreGraph q) :=
    edgeCard_induce_le_linearForestNumber hL (InFibre q)
  unfold fibreRestrictionLoss
  rw [linearForestNumber_quotientType q]
  omega

theorem complementRestrictionLoss_nonneg {N : ℕ} (q : LargePrime N)
    {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    0 ≤ complementRestrictionLoss q L := by
  have h : edgeCard (L.induce {v | ¬ InFibre q v}) ≤ linearForestNumber (fibreComplement q) :=
    edgeCard_induce_le_linearForestNumber hL (fun v ↦ ¬ InFibre q v)
  unfold complementRestrictionLoss
  omega

/--
**Lemma 3.4 of the paper (exact defect decomposition).**  For every maximum
spanning linear forest `L` of `H_N`,

```text
D_N(q) = m_L(q) - i_L(q) - r_L(q).
```

The proof is the exact three-way edge partition of `L`: fibre-internal edges,
complement-internal edges and crossings, with nothing counted twice.
-/
theorem fibreDefect_eq_crossing_sub_losses {N : ℕ} (q : LargePrime N)
    {L : SimpleGraph (HVertex N)}
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N)) :
    fibreDefect q
      = (crossingCount q L : ℤ) - fibreRestrictionLoss q L
        - complementRestrictionLoss q L := by
  have hpart := edgeCard_eq_internal_add_internal_add_crossing L (InFibre q)
  rw [← edgeCard_induce_setOf L (InFibre q),
    ← edgeCard_induce_setOf L (fun v ↦ ¬ InFibre q v)] at hpart
  unfold fibreDefect crossingCount fibreRestrictionLoss complementRestrictionLoss
  rw [linearForestNumber_quotientType q] at *
  omega

/--
**Lemma 2.9 of the paper (constructive lower bound).**

For an *arbitrary* spanning linear forest `L` of `H_N` — not necessarily a
maximum one —

```text
D_N(q) ≥ m_L(q) - i_L(q) - e_L(q).
```

This is the manuscript's `D_N(q) ≥ r - a - b`: writing `M = L[R_{N,q}]`,
`qJ = L[B_q(N)]` and `X` for the crossings of `L`, the losses `a` and `b` are
exactly `e_L(q)` and `i_L(q)`, and `r = m_L(q)`.  Assembling `M ∪ qJ ∪ X` is
not needed in this direction: any spanning linear forest of `H_N` already
decomposes that way, and the compatibility hypothesis of the manuscript is what
makes `L` a linear forest in the first place.
-/
theorem fibreDefect_ge_crossing_sub_losses {N : ℕ} (q : LargePrime N)
    {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    (crossingCount q L : ℤ) - fibreRestrictionLoss q L
        - complementRestrictionLoss q L
      ≤ fibreDefect q := by
  have hpart := edgeCard_eq_internal_add_internal_add_crossing L (InFibre q)
  rw [← edgeCard_induce_setOf L (InFibre q),
    ← edgeCard_induce_setOf L (fun v ↦ ¬ InFibre q v)] at hpart
  have hmax : edgeCard L ≤ linearForestNumber (reducedDivisorGraph N) :=
    edgeCard_le_linearForestNumber hL
  unfold fibreDefect crossingCount fibreRestrictionLoss complementRestrictionLoss
  rw [linearForestNumber_quotientType q] at *
  omega

/-- Consequence (3.8): the defect never exceeds the crossing count of any
maximum forest. -/
theorem fibreDefect_le_crossingCount {N : ℕ} (q : LargePrime N)
    {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N)) :
    fibreDefect q ≤ (crossingCount q L : ℤ) := by
  have h1 := fibreRestrictionLoss_nonneg q hL
  have h2 := complementRestrictionLoss_nonneg q hL
  rw [fibreDefect_eq_crossing_sub_losses q hmax]
  omega

/-- Fibres with the same quotient type have the same defect. -/
theorem sameType_fibreDefect {N : ℕ} (q r : LargePrime N)
    (htype : q.quotientType = r.quotientType) :
    fibreDefect q = fibreDefect r := by
  classical
  by_cases hqr : q.val = r.val
  · have hqeq : q = r := by
      cases q
      cases r
      simp_all
    subst r
    rfl
  · unfold fibreDefect
    rw [linearForestNumber_iso (sameTypeComplementIso q r htype hqr)]
    rw [htype]

end DivisorF
