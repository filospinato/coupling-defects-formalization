import DivisorF.ManuscriptCompletion

set_option linter.style.header false

/-!
# Axiom audit for the September-manuscript completion layer

These checkpoints supplement `DivisorF.Audit`.  They isolate the small
paper-facing completion layer so that its semantic bridges remain easy to audit.

The accepted criterion is the same as the central audit: no `sorryAx`, no
project-specific axiom, and no dependency beyond `propext`, `Classical.choice`
and `Quot.sound`.

The transport-ramp declaration corresponds to equation (5.3) of the current
10 September manuscript.  `primeWindowBound_real` is the exact paper-facing
real-window wrapper for Corollary 5.3.  The support-level injectivity lemma is
not separately checkpointed; it is a transitive dependency of
`card_truncDeleted_eq`.
-/

#print axioms DivisorF.card_truncDeleted_eq
#print axioms DivisorF.transportPenalty_bounds
#print axioms DivisorF.fibreDefect_sub_transportPenalty_le
#print axioms DivisorF.transportRampTerm_le_fibreDefect
#print axioms DivisorF.transportRampSum_le
#print axioms DivisorF.primeWindowBound_real
