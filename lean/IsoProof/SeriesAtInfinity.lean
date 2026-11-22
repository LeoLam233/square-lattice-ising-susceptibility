import IsoProof.ResonanceEnergy
import IsoProof.IntegralsOriginBound
import IsingBulk.Preferred22.NormalConvergence

/-! Actual bounds near E=infinity.  They provide the removable w=0 germ of
the normalized series; no convergence or value at infinity is supplied as
an input. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open scoped Topology BigOperators
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem energyDomain_of_norm_gt_two {E : ℂ} (hE : 2 < ‖E‖) : E ∈ energyDomain := by
  by_cases hi : E.im=0
  · exact Or.inr ((Complex.abs_re_eq_norm.mpr hi).symm ▸ hE)
  · exact Or.inl hi

theorem fullEnergySum_positive_analyticOn (ν : Phase) :
    AnalyticOnNhd ℂ (fullEnergySum ν .positive) energyDomain := by
  intro E hE
  obtain ⟨hs,he⟩ := exteriorEnergyInverse_spec hE
  rw [← he]
  cases ν with
  | high => exact fullEnergySum_high_analyticAt_energy .positive hs
  | low => exact fullEnergySum_low_analyticAt_energy hs

/-- On a fixed far exterior, every genuine small transfer root has a
uniform contraction margin.  The estimate comes directly from its trace. -/
theorem angleRoot_norm_le_half_of_far {E : ℂ} (hE : 4 < ‖E‖) (q : ℝ) :
    ‖angleRoot E q‖ ≤ (1/2 : ℝ) := by
  have hD := energyDomain_of_norm_gt_two (by linarith : 2 < ‖E‖)
  have hu := angleRoot_inside hD q
  by_contra hbad
  have hhalf : (1/2 : ℝ) < ‖angleRoot E q‖ := lt_of_not_ge hbad
  have hinv : ‖(angleRoot E q)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1/2) hhalf.le
    norm_num at h ⊢
    exact h
  have htrace : ‖2*(E-(Real.cos q : ℂ))‖ ≤ 3 := by
    rw [← angleRoot_trace]
    exact (norm_add_le _ _).trans (by linarith)
  have hW : ‖E-(Real.cos q : ℂ)‖ ≤ 3/2 := by
    norm_num only [norm_mul, norm_ofNat] at htrace
    linarith
  have hc : ‖(Real.cos q : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one q
  have he : ‖E‖ ≤ ‖E-(Real.cos q : ℂ)‖+‖(Real.cos q : ℂ)‖ :=
    norm_le_norm_sub_add E (Real.cos q : ℂ)
  linarith

def farEvenEnvelope (n : ℕ) : ℝ :=
  IsingBulk.Preferred22.resolventEnvelope (1/2) *
    (Real.exp 1*(IsingBulk.Preferred22.kernelEnvelope (1/2))^2 /
      Real.sqrt (2*(n+1) : ℕ))^(2*(n+1))

theorem farEvenEnvelope_summable : Summable farEvenEnvelope :=
  IsingBulk.Preferred22.even_numerical_envelope_summable _ _

theorem fullEnergySum_low_far_bound {E : ℂ} (hE : 4 < ‖E‖) :
    ‖fullEnergySum .low .positive E‖ ≤ ∑' n : ℕ, farEvenEnvelope n := by
  obtain ⟨hs,he⟩ := exteriorEnergyInverse_spec
    (energyDomain_of_norm_gt_two (by linarith : 2 < ‖E‖))
  let s := exteriorEnergyInverse E
  have hroot : ∀ q : ℝ,
      ‖IsingBulk.Preferred22.physicalRoot (IsingBulk.Preferred22.angularW s q)‖ ≤ 1/2 := by
    intro q
    change ‖angleRoot (energy s) q‖ ≤ 1/2
    rw [show energy s=E from he]
    exact angleRoot_norm_le_half_of_far hE q
  have hterm (n : ℕ) : ‖IsingBulk.Preferred22.coefficient (2*(n+1)) s‖ ≤ farEvenEnvelope n :=
    IsingBulk.Preferred22.coefficient_norm_bound (by omega)
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1) hroot
  have hsum := IsingBulk.Preferred22.even_coefficients_absolutely_summable hs
  rw [← he, fullEnergySum_low_energy hs]
  exact (norm_tsum_le_tsum_norm hsum).trans
    (Summable.tsum_le_tsum hterm hsum farEvenEnvelope_summable)

theorem exteriorEnergyInverse_large {E : ℂ} (hE : 17 < ‖E‖) :
    16 < ‖exteriorEnergyInverse E‖ := by
  obtain ⟨hs,he⟩ := exteriorEnergyInverse_spec
    (energyDomain_of_norm_gt_two (by linarith : 2 < ‖E‖))
  have hinv : ‖(exteriorEnergyInverse E)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hs.le
  have hsum := norm_add_le (exteriorEnergyInverse E) (exteriorEnergyInverse E)⁻¹
  change ‖energy (exteriorEnergyInverse E)‖ ≤ _ at hsum
  rw [he] at hsum
  linarith

theorem fullEnergySum_high_far_bound {E : ℂ} (hE : 17 < ‖E‖) :
    ‖fullEnergySum .high .positive E‖ ≤ IsingBulk.HT.Final.originMajorant := by
  obtain ⟨hs,he⟩ := exteriorEnergyInverse_spec
    (energyDomain_of_norm_gt_two (by linarith : 2 < ‖E‖))
  have hbound := IsingBulk.HT.Final.exteriorOddSeries_scaled_bound
    (exteriorEnergyInverse_large hE)
  rw [norm_mul] at hbound
  rw [← he, fullEnergySum_high_energy,
    IsingBulk.HT22.Physical.oddSeries_eq_existing_exterior hs]
  exact (le_mul_of_one_le_left (norm_nonneg _) hs.le).trans hbound

theorem fullEnergySum_far_bounded (ν : Phase) :
    ∃ M : ℝ, ∀ E : ℂ, 17 < ‖E‖ → ‖fullEnergySum ν .positive E‖ ≤ M := by
  cases ν with
  | high => exact ⟨_,fun _ h => fullEnergySum_high_far_bound h⟩
  | low => exact ⟨_,fun _ h => fullEnergySum_low_far_bound (by linarith)⟩

end
end IsoProof
