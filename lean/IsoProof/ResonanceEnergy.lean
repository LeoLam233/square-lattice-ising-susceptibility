import IsoProof.ResonanceCoordinate
import IsoProof.IntegralsReflection
import IsingBulk.Preferred22.NormalConvergence

/-! Analyticity of the literal E-coordinate infinite sums, produced from
the proved coefficient/sum identities and the actual analytic energy map. -/
namespace IsoProof
noncomputable section
open Complex Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

private theorem exterior_noncritical {s : ℂ} (hs : 1<‖s‖) :
    s≠0 ∧ s≠1 ∧ s≠ -1 := by
  constructor
  · intro h
    norm_num [h] at hs
  constructor
  · intro h
    norm_num [h] at hs
  · intro h
    norm_num [h] at hs

/-- Both signed high-temperature complete E-sums are analytic at every energy
of an exterior point.  The identity used is the termwise literal one. -/
theorem fullEnergySum_high_analyticAt_energy (σ : Sign) {s : ℂ} (hs : 1<‖s‖) :
    AnalyticAt ℂ (fullEnergySum .high σ) (energy s) := by
  obtain ⟨hs0,hs1,hsm1⟩ := exterior_noncritical hs
  apply analyticAt_energyFunction_of_composition hs0 hs1 hsm1
  cases σ with
  | positive =>
      apply (IsingBulk.HT22.Physical.signedOddSeries_analyticAt false hs).congr
      exact Filter.Eventually.of_forall (fun u=>(fullEnergySum_high_positive_signed_energy u).symm)
  | negative =>
      apply (IsingBulk.HT22.Physical.signedOddSeries_analyticAt true hs).congr
      exact Filter.Eventually.of_forall (fun u=>(fullEnergySum_high_negative_signed_energy u).symm)

/-- The literal low-temperature positive-even E-sum is analytic at every
energy of an exterior point.  Its exact even determinant normalization and
constrained angular integration have already been identified in IntegralsParity. -/
theorem fullEnergySum_low_analyticAt_energy {s : ℂ} (hs : 1<‖s‖) :
    AnalyticAt ℂ (fullEnergySum .low .positive) (energy s) := by
  obtain ⟨hs0,hs1,hsm1⟩ := exterior_noncritical hs
  apply analyticAt_energyFunction_of_composition hs0 hs1 hsm1
  apply (IsingBulk.Preferred22.evenSeries_analyticAt hs).congr
  have hnear : ∀ᶠ u in 𝓝 s,1<‖u‖ := (isOpen_lt continuous_const continuous_norm).mem_nhds hs
  filter_upwards [hnear] with u hu
  exact (fullEnergySum_low_energy hu).symm

end
end IsoProof
