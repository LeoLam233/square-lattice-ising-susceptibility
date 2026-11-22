import IsoProof.EnergyJetRegularity
import IsoProof.SusceptibilityDifferential
import IsoProof.TailSigned
import IsoProof.ResonanceNaturalBoundary

/-! Terminal differential transcendence statements for the literal functions
of the signed five-page manuscript. No contour, tail estimate, singularity,
noncancellation, extension, or differential-algebraic hypothesis is supplied
by the caller. Physical correlation inputs occur only in the separately
stated physical identification theorems. -/
namespace IsoProof
noncomputable section

/-- The reduced susceptibility germ is differentially transcendental over
C(s) at every point of the entire positive real interval in either phase. -/
theorem reduced_differentiallyTranscendental (ν : Phase) {s : ℝ}
    (hs : s ∈ realTemperatureDomain ν) :
    DifferentiallyTranscendentalAt (reducedSusceptibility ν) (s : ℂ) :=
  reduced_differentiallyTranscendental_of_energyJetIntervals ν
    (fun n _ => regularEnergyJetInterval ν n) hs

/-- The energy-field physical susceptibility includes beta=arsinh(s)/(2J).
It is differentially transcendental over C(s) throughout each real phase. -/
theorem physical_differentiallyTranscendental (ν : Phase) {J s : ℝ}
    (hJ : 0 < J) (hs : s ∈ realTemperatureDomain ν) :
    DifferentiallyTranscendentalAt (physicalSusceptibility ν J) (s : ℂ) :=
  physical_differentiallyTranscendental_of_energyJetIntervals ν
    (fun n _ => regularEnergyJetInterval ν n) hJ hs

/-- Both literal normalized odd/even w-series, with their actual removable
value at w=0, are differentially transcendental over C(w) at the origin. -/
theorem normalizedSeries_differentiallyTranscendental (ν : Phase) :
    DifferentiallyTranscendentalAt (normalizedSeries ν) 0 :=
  normalized_differentiallyTranscendental_of_energyJetIntervals ν
    (fun n _ => regularEnergyJetInterval ν n)

/-- The complete reduced-susceptibility assertions of manuscript §1. -/
theorem paper_reduced (ν : Phase) :
    AnalyticOnNhd ℂ (reducedSusceptibility ν) (physicalDomain ν) ∧
    NaturalBoundary (physicalDomain ν) (reducedSusceptibility ν) ∧
    ∀ s : ℝ, s ∈ realTemperatureDomain ν →
      DifferentiallyTranscendentalAt (reducedSusceptibility ν) (s : ℂ) :=
  ⟨reduced_analyticOn ν, reduced_naturalBoundary_from_sharp ν,
    fun _ hs => reduced_differentiallyTranscendental ν hs⟩

/-- Physical normalization and every genuine continued exterior beta sheet.
The low-temperature sheet predicate is printed in IsoProofAudit. -/
theorem paper_physical {J : ℝ} (hJ : 0 < J) :
    AnalyticOnNhd ℂ (physicalSusceptibility .high J) (physicalDomain .high) ∧
    NaturalBoundary (physicalDomain .high) (physicalSusceptibility .high J) ∧
    (∀ z : ℂ, ‖z‖ = 1 →
      ¬ PhysicalExteriorExtension J (reducedSusceptibility .low) z) ∧
    ∀ ν : Phase, ∀ s : ℝ, s ∈ realTemperatureDomain ν →
      DifferentiallyTranscendentalAt (physicalSusceptibility ν J) (s : ℂ) :=
  ⟨physical_high_analyticOn hJ, physical_high_naturalBoundary_from_sharp hJ,
    physical_low_all_branches_naturalBoundary_from_sharp hJ,
    fun ν _ hs => physical_differentiallyTranscendental ν hJ hs⟩

/-- The two series germs in the literal normalization w=1/(2E). -/
theorem paper_normalized (ν : Phase) :
    AnalyticAt ℂ (normalizedSeries ν) 0 ∧
    DifferentiallyTranscendentalAt (normalizedSeries ν) 0 :=
  ⟨normalizedSeries_analyticAt_zero ν, normalizedSeries_differentiallyTranscendental ν⟩

end
end IsoProof
