import IsoProof.IntegralsBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Exact one-particle normalization in both signed channels. -/
namespace IsoProof
noncomputable section
open scoped BigOperators
open IsingBulk.First IsingBulk.Tail

/-- The exterior temperature map lands in the complete energy slit domain.
This uses the explicit physical-root domain theorem at a test angle, not a
choice of a complex inverse of the Joukowski map. -/
theorem energy_mem_domain_of_exterior {s : ℂ} (hs : 1 < ‖s‖) :
    energy s ∈ energyDomain := by
  by_contra h
  have hbad : (energy s).im = 0 ∧ |(energy s).re| ≤ 2 := by
    simpa only [energyDomain, Set.mem_ofPred_eq, not_or, not_ne_iff, not_lt] using h
  have hlo : -1 ≤ (energy s).re/2 := by linarith [(abs_le.mp hbad.2).1]
  have hhi : (energy s).re/2 ≤ 1 := by linarith [(abs_le.mp hbad.2).2]
  have hcos := Real.cos_arccos hlo hhi
  have hw := IsingBulk.Preferred22.angularW_off_segment hs
    (Real.arccos ((energy s).re/2))
  rcases hw with hw | hw
  · apply hw
    simpa only [IsingBulk.Preferred22.angularW, IsingBulk.Preferred22.temperatureTrace,
      Complex.sub_im, Complex.ofReal_im, sub_zero, energy] using hbad.1
  · have hw' : 1 < |(energy s).re/2| := by
      change 1 < |(energy s).re - Real.cos (Real.arccos ((energy s).re/2))| at hw
      rw [hcos, sub_half] at hw
      exact hw
    exact (not_lt_of_ge (abs_le.mpr ⟨hlo,hhi⟩)) hw'

theorem energy_mem_domain_of_interior {s : ℂ} (hs0 : s ≠ 0) (hs : ‖s‖ < 1) :
    energy s ∈ energyDomain := by
  rw [← energy_inv s]
  apply energy_mem_domain_of_exterior
  rw [norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hs0)).mpr hs

/-- A concrete exterior inverse of E=s+s⁻¹. -/
def exteriorEnergyInverse (E : ℂ) : ℂ :=
  (IsingBulk.Preferred22.physicalRoot (E/2))⁻¹

theorem exteriorEnergyInverse_spec {E : ℂ} (hE : E ∈ energyDomain) :
    1 < ‖exteriorEnergyInverse E‖ ∧ energy (exteriorEnergyInverse E) = E := by
  have hw : IsingBulk.Preferred22.OffRealSegment (E/2) := by
    rcases hE with hE | hE
    · left
      simpa using div_ne_zero hE (by norm_num : (2 : ℝ) ≠ 0)
    · right
      have hre : (E/2).re = E.re/2 := by simp
      rw [hre, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)
  constructor
  · rw [exteriorEnergyInverse, norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr (IsingBulk.Preferred22.physicalRoot_ne_zero _))).mpr
      (IsingBulk.Preferred22.physicalRoot_inside hw)
  · unfold energy exteriorEnergyInverse
    rw [inv_inv, add_comm, IsingBulk.Preferred22.physicalRoot_trace]
    ring

private theorem one_particle_positive_algebra (E u : ℂ)
    (hu : u ≠ 0) (hm : 1-u ≠ 0) (hp : 1+u ≠ 0)
    (hE : E-2 ≠ 0) (ht : u+u⁻¹ = 2*(E-1)) :
    ((1+u)/(1-u)) * (((u⁻¹-u)/2)⁻¹) = (E-2)⁻¹ := by
  have ht' : u^2+1 = 2*(E-1)*u := by
    have h := congrArg (fun z : ℂ => z*u) ht
    rw [add_mul, inv_mul_cancel₀ hu] at h
    simpa only [pow_two] using h
  have hd : u⁻¹-u ≠ 0 := by
    intro h
    have hx : u^2=1 := by
      have h' := congrArg (fun z : ℂ => z*u) h
      rw [sub_mul, inv_mul_cancel₀ hu, zero_mul] at h'
      linear_combination -h'
    have hz : (1-u)*(1+u)=0 := by linear_combination -hx
    exact (mul_ne_zero hm hp) hz
  have h12 : 1-u^2 ≠ 0 := by
    convert mul_ne_zero hm hp using 1
    ring
  have hone : 2*u*(E-2) = (1-u)^2 := by linear_combination -ht'
  field_simp [hu, hm, hp, hE, h12]
  linear_combination (1+u)*hone

theorem particleCoefficient_one_positive {E : ℂ} (hE : E ∈ energyDomain) :
    particleCoefficient .positive 1 E = (E-2)⁻¹ := by
  let u := angleRoot E 0
  have hu : u ≠ 0 := angleRoot_ne_zero E 0
  have hn : ‖u‖ < 1 := angleRoot_inside hE 0
  have hm : 1-u ≠ 0 := by
    intro h
    have he : u=1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hn
    exact lt_irrefl _ hn
  have hp : 1+u ≠ 0 := by
    intro h
    have he : u= -1 := by linear_combination h
    rw [he, norm_neg, norm_one] at hn
    exact lt_irrefl _ hn
  have he : E-2 ≠ 0 := by
    intro h
    have hE' : E=2 := sub_eq_zero.mp h
    subst E
    norm_num [energyDomain] at hE
  have ht : u+u⁻¹ = 2*(E-1) := by
    simpa only [u, Real.cos_zero, Complex.ofReal_one] using angleRoot_trace E 0
  have hscalar := one_particle_positive_algebra E u hu hm hp he ht
  simpa [particleCoefficient, particleDensity, constrainedAngles, signAngle,
    signValue, pairProduct, canceledPairProduct,
    IsingBulk.HT22.Physical.oneBody, multiAngleIntegral, Fin.snoc_zero, Fin.eq_zero, u] using hscalar

/-- The normalized first term has its stated rational form under the s map. -/
theorem one_particle_coordinate (s : ℂ) (hs : s ≠ 0) (_hs1 : s ≠ 1) :
    (energy s-2)⁻¹ = s/(1-s)^2 := by
  have hden : energy s-2 = (1-s)^2/s := by
    unfold energy
    field_simp [hs]
    ring
  rw [hden, inv_div]

end
end IsoProof
