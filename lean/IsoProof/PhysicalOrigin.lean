import IsoProof.IntegralsOneParticle
import IsoProof.IntegralsOriginBound
import IsingBulk.HT22.Physical.GermBridge

/-! The high-temperature value at zero is proved from the explicit first
particle and the full higher-particle tail. The value 1 in the new definition
is therefore the actual analytic removable value. -/
namespace IsoProof
noncomputable section
open Filter Set IsingBulk.First IsingBulk.Tail IsingBulk.HT.Final
open scoped Topology BigOperators

def scaledHighTail (s : ℂ) : ℂ :=
  ∑' n : ℕ, s⁻¹ * IsingBulk.HT22.Physical.coefficient (2*n+3) s⁻¹

theorem scaledHighTail_tendsto_zero :
    Tendsto scaledHighTail (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  have hb : Tendsto (fun s : ℂ => (∑' n : ℕ, originTailMajorant n)*‖s‖^2)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa using (((continuous_norm.pow 2).const_mul
      (∑' n : ℕ, originTailMajorant n)).tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hb
  have hsmall : ∀ᶠ s : ℂ in 𝓝[≠] (0 : ℂ), ‖s‖ < 1/16 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_norm continuous_const).mem_nhds
      (by norm_num : ‖(0 : ℂ)‖ < (1/16 : ℝ)))
  filter_upwards [self_mem_nhdsWithin, hsmall] with s hs0 hs
  exact scaled_odd_tail_bound hs0 hs

/-- Split the complete high-temperature angular sum. The first term is
separated only after absolute summability has been proved. -/
theorem high_scaled_series_split {s : ℂ} (hs0 : s ≠ 0) (hs : ‖s‖ < 1) :
    s⁻¹ * fullEnergySum .high .positive (energy s) =
      ((1-s)^2)⁻¹ + scaledHighTail s := by
  have hi : 1 < ‖s⁻¹‖ := by
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hs0)).mpr hs
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hsum : Summable (fun n : ℕ => IsingBulk.HT22.Physical.coefficient (2*n+1) s⁻¹) := by
    simpa only [iteratedDeriv_zero] using
      (IsingBulk.HT22.Physical.oddCoefficient_derivative_norm_summable 0 hi).of_norm
  rw [← energy_inv s, fullEnergySum_high_energy]
  unfold IsingBulk.HT22.Physical.oddSeries
  rw [hsum.tsum_eq_zero_add, mul_add, ← tsum_mul_left]
  have hone : IsingBulk.HT22.Physical.coefficient 1 s⁻¹ = s/(1-s)^2 := by
    rw [← particleCoefficient_positive_energy, energy_inv,
      particleCoefficient_one_positive (energy_mem_domain_of_interior hs0 hs)]
    exact one_particle_coordinate s hs0 hs1
  simp only [Nat.mul_zero, zero_add, hone]
  have hf : s⁻¹*(s/(1-s)^2) = ((1-s)^2)⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  rw [hf]
  congr 1

theorem high_scaled_series_tendsto_one :
    Tendsto (fun s => s⁻¹*fullEnergySum .high .positive (energy s))
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  have hfirst : Tendsto (fun s : ℂ => ((1-s)^2)⁻¹)
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have hcont : ContinuousAt (fun s : ℂ => ((1-s)^2)⁻¹) 0 := by
      exact ((continuousAt_const.sub continuousAt_id).pow 2).inv₀ (by norm_num)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hnew := hfirst.add scaledHighTail_tendsto_zero
  simp only [add_zero] at hnew
  apply hnew.congr'
  have hsmall : ∀ᶠ s : ℂ in 𝓝[≠] (0 : ℂ), ‖s‖ < 1 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_norm continuous_const).mem_nhds
      (by norm_num : ‖(0 : ℂ)‖ < (1 : ℝ)))
  filter_upwards [self_mem_nhdsWithin, hsmall] with s hs0 hs
  exact (high_scaled_series_split hs0 hs).symm

theorem rawHigh_eq_puncturedInteriorBulk (s : ℂ) :
    normalization .high s * fullEnergySum .high .positive (energy s) =
      IsingBulk.HT22.Physical.puncturedInteriorBulk s := by
  rw [← energy_inv s, fullEnergySum_high_energy]
  rfl

theorem puncturedInteriorBulk_tendsto_one :
    Tendsto IsingBulk.HT22.Physical.puncturedInteriorBulk
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  have hf : Tendsto interiorFourthFactor (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h := (interiorFourthFactor_analyticAt (s := 0) (by norm_num)).continuousAt.tendsto
    simpa [interiorFourthFactor] using h.mono_left nhdsWithin_le_nhds
  have hprod := hf.mul high_scaled_series_tendsto_one
  simp only [mul_one] at hprod
  apply hprod.congr'
  apply Filter.Eventually.of_forall
  intro s
  rw [← rawHigh_eq_puncturedInteriorBulk]
  simp only [interiorFourthFactor, normalization, div_eq_mul_inv, mul_assoc]
  rfl

theorem existing_interior_value_one : interiorFullBulk 0 = 1 :=
  tendsto_nhds_unique IsingBulk.HT22.Physical.puncturedInteriorBulk_tendsto_zero
    puncturedInteriorBulk_tendsto_one

theorem reduced_high_eq_existing {s : ℂ} (hs : s ∈ physicalDomain .high) :
    reducedSusceptibility .high s = interiorFullBulk s := by
  by_cases hs0 : s=0
  · subst s
    simp only [reducedSusceptibility, and_self, ite_true]
    exact existing_interior_value_one.symm
  · simp only [reducedSusceptibility, hs0, and_false, ite_false]
    rw [rawHigh_eq_puncturedInteriorBulk]
    exact IsingBulk.HT22.Physical.puncturedInteriorBulk_eq_existing hs0 hs

/-- Full-disk analyticity of the paper's literal high-temperature function,
including the now verified origin normalization. -/
theorem reduced_high_analyticOn :
    AnalyticOnNhd ℂ (reducedSusceptibility .high) (physicalDomain .high) := by
  intro s hs
  apply (interiorFullBulk_analyticOn s hs).congr
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hs] with z hz
  exact (reduced_high_eq_existing hz).symm

theorem reduced_high_value_zero : reducedSusceptibility .high 0 = 1 := by
  simp [reducedSusceptibility]

end
end IsoProof
