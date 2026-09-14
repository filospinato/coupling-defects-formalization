import DivisorF.Section6Assembly
import DivisorF.ExceptionalEndpointIntegerDiscretisation

set_option linter.style.header false

/-! Supplemental axiom audit for the newest Section 6 surface.

These declarations are kept separate while the candidate API is still in
Develop.  They are imported by the library build so the exact declarations and
their transitive axiom sets are checked before the final central `Audit.lean`
consolidation.
-/

#print axioms DivisorF.integerDiscretisationCore_of_manuscript
#print axioms DivisorF.concreteTranslatedEndpointPrimePacket_zeroThreshold_of_card_gt_twice_cutoff
#print axioms DivisorF.eventuallyConcreteTranslatedEndpointData_powerCutoff_of_packetDominates
#print axioms DivisorF.eventuallyZeroOutsideBadEndpoints_powerCutoff_of_packetDominates
#print axioms DivisorF.section6TranslatedBadEndpoints_sparse_of_fixedPrecision
#print axioms DivisorF.section6ZeroOutsideTranslatedBadEndpoints_of_packetDominates
#print axioms DivisorF.section6RegularEndpointPackage_of_fixedPrecision_and_packetDominates
