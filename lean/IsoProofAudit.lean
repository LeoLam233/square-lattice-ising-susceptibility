import IsoProof

/-! Independent terminal readback entry. All statements below are elaborated
from the imported actual source, rather than copied summaries. Structure and
alias definitions expose physical premises, domains, jets and germ meanings.
The final command walks actual transitive proof-body dependencies. -/
set_option pp.proofs false
set_option pp.universes true
set_option maxHeartbeats 0

#print IsoProof.Phase
#print IsoProof.Sign
#print IsoProof.signValue
#print IsoProof.signAngle
#print IsoProof.particleOrder
#print IsoProof.energy
#print IsoProof.seriesCoordinate
#print IsoProof.physicalDomain
#print IsoProof.realTemperatureDomain
#print IsoProof.energyDomain
#print IsoProof.angleRoot
#print IsoProof.anglePoint
#print IsoProof.pairProduct
#print IsingBulk.Tail.canceledPairProduct
#print IsoProof.siteCoefficient
#print IsoProof.constrainedAngles
#print IsoProof.particleDensity
#print IsoProof.particleCoefficient
#print IsoProof.fullEnergySum
#print IsoProof.energyTail
#print IsoProof.normalization
#print IsoProof.reducedSusceptibility
#print IsoProof.physicalSusceptibility
#print IsingBulk.Final.inverseTemperatureBranch
#print IsoProof.rawNormalizedSeries
#print IsoProof.normalizedSeries
#print IsoProof.normalizedSeriesDomain

#print IsoProof.LatticeSite
#print IsoProof.spontaneousSquare
#print IsoProof.connectedCorrelation
#print IsoProof.PublishedSiteInput
#print IsoProof.publishedCosineSiteCoefficient
#print IsoProof.exteriorTemperature
#print IsoProof.realReducedSum
#print IsoProof.realInverseTemperature
#print IsoProof.realPhysicalSum
#print IsoProof.HasEnergyFieldResponse
#print IsoProof.PublishedEnergyResponse
#print IsoProof.LocalExtension
#print IsoProof.NaturalBoundary
#print IsoProof.PhysicalExteriorExtension

#print IsoProof.GermEqAt
#print IsoProof.complexJet
#print IsoProof.UpperJetTrace
#print IsoProof.DifferentialPolynomial
#print IsoProof.jetEvaluation
#print IsoProof.evaluateDifferentialPolynomial
#print IsoProof.PolynomialDifferentialRelationAt
#print IsoProof.RationalDifferentialPolynomial
#print IsoProof.evaluateRationalDifferentialPolynomial
#print IsoProof.RationalDifferentialRelationAt
#print IsoProof.DifferentiallyTranscendentalAt
#print IsoProof.rational_relation_iff_polynomial_relation
#print IsoProof.RegularEnergyJetInterval
#print IsoProof.SmoothSingularBoundaryChart
#print IsoProof.SharpBoundaryApproach

#print IsoProof.reduced_analyticOn
#print IsoProof.reduced_high_value_zero
#print IsoProof.reduced_naturalBoundary_from_sharp
#print IsoProof.physical_high_analyticOn
#print IsoProof.physical_high_naturalBoundary_from_sharp
#print IsoProof.physical_low_all_branches_naturalBoundary_from_sharp
#print IsoProof.realReducedSum_eq_reducedSusceptibility
#print IsoProof.connectedCorrelation_norm_summable
#print IsoProof.realReducedSum_origin_add_offOrigin
#print IsoProof.spin_reversal_sum_eq
#print IsoProof.physical_real_identification
#print IsoProof.energyFieldResponse_identification
#print IsoProof.high_normalization_real
#print IsoProof.low_normalization_real
#print IsoProof.spontaneousSquare_low_real_positive
#print IsoProof.paper_reduced
#print IsoProof.paper_physical
#print IsoProof.paper_normalized
#print IsoProof.regularEnergyJetInterval
#print IsoProof.reduced_differentiallyTranscendental
#print IsoProof.physical_differentiallyTranscendental
#print IsoProof.normalizedSeries_analyticAt_zero
#print IsoProof.normalizedSeries_differentiallyTranscendental

#print IsoProof.common_phase_gain
#print IsoProof.complex_pairProduct_three_quarters
#print IsoProof.siteCoefficient_lattice_jet_bound
#print IsoProof.siteCoefficient_compact_jets_bound
#print IsoProof.common_phase_gain_locally_uniform
#print IsoProof.latticeShell_card
#print IsoProof.signed_energyTail_continuous_jets_on_compact_interval
#print IsoProof.prime_particleCoefficient_analytic_extension
#print IsoProof.finite_particleCoefficient_extensions_in_interval
#print IsoProof.high_prime_sharp_full_sum
#print IsoProof.low_prime_sharp_full_sum
#print IsoProof.exists_minimal_relation_nonzero_separant
#print IsoProof.differential_transcendentalAt_of_boundary_charts

#print axioms IsoProof.reduced_analyticOn
#print axioms IsoProof.reduced_high_value_zero
#print axioms IsoProof.reduced_naturalBoundary_from_sharp
#print axioms IsoProof.physical_high_analyticOn
#print axioms IsoProof.physical_high_naturalBoundary_from_sharp
#print axioms IsoProof.physical_low_all_branches_naturalBoundary_from_sharp
#print axioms IsoProof.realReducedSum_eq_reducedSusceptibility
#print axioms IsoProof.energyFieldResponse_identification
#print axioms IsoProof.rational_relation_iff_polynomial_relation
#print axioms IsoProof.paper_reduced
#print axioms IsoProof.paper_physical
#print axioms IsoProof.paper_normalized
#print axioms IsoProof.regularEnergyJetInterval
#print axioms IsoProof.reduced_differentiallyTranscendental
#print axioms IsoProof.physical_differentiallyTranscendental
#print axioms IsoProof.normalizedSeries_analyticAt_zero
#print axioms IsoProof.normalizedSeries_differentiallyTranscendental
#print axioms IsoProof.common_phase_gain
#print axioms IsoProof.siteCoefficient_lattice_jet_bound
#print axioms IsoProof.signed_energyTail_continuous_jets_on_compact_interval
#print axioms IsoProof.prime_particleCoefficient_analytic_extension
#print axioms IsoProof.high_prime_sharp_full_sum
#print axioms IsoProof.low_prime_sharp_full_sum

#audit_proof_closure [
 IsoProof.paper_reduced,
 IsoProof.paper_physical,
 IsoProof.paper_normalized,
 IsoProof.reduced_analyticOn,
 IsoProof.reduced_high_value_zero,
 IsoProof.reduced_naturalBoundary_from_sharp,
 IsoProof.physical_high_analyticOn,
 IsoProof.physical_high_naturalBoundary_from_sharp,
 IsoProof.physical_low_all_branches_naturalBoundary_from_sharp,
 IsoProof.realReducedSum_eq_reducedSusceptibility,
 IsoProof.energyFieldResponse_identification,
 IsoProof.rational_relation_iff_polynomial_relation,
 IsoProof.reduced_differentiallyTranscendental,
 IsoProof.physical_differentiallyTranscendental,
 IsoProof.normalizedSeries_analyticAt_zero,
 IsoProof.normalizedSeries_differentiallyTranscendental,
 IsoProof.signed_energyTail_continuous_jets_on_compact_interval,
 IsoProof.prime_particleCoefficient_analytic_extension]
