import IsoProof.BoundaryCoordinates
import IsoProof.PhysicalFactors

/-! The actual physical factors on the closed energy collars.  Interior
points use the physical-domain branches; real boundary points use the same
continued root, with explicit nonaxis unit-circle geometry. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem temperatureChart_low_real {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    temperatureChart .low (x : ℂ) =
      Complex.exp ((Real.arccos (x/2) : ℂ)*Complex.I) := by
  unfold temperatureChart
  rw [show (x : ℂ)/2 = ((x/2 : ℝ) : ℂ) by push_cast; rfl,
    continuedTransferRoot_real_interior (by linarith : -1 < x/2) (by linarith : x/2 < 1),
    ← Complex.exp_neg]
  ring

theorem temperatureChart_high_real {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    temperatureChart .high (x : ℂ) =
      Complex.exp ((-Real.arccos (x/2) : ℂ)*Complex.I) := by
  unfold temperatureChart
  rw [show (x : ℂ)/2 = ((x/2 : ℝ) : ℂ) by push_cast; rfl,
    continuedTransferRoot_real_interior (by linarith : -1 < x/2) (by linarith : x/2 < 1)]
  ring

theorem temperatureChart_real_geometry (ν : Phase) {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    ‖temperatureChart ν (x : ℂ)‖=1 ∧
      (temperatureChart ν (x : ℂ))^4 ≠ 1 ∧ 0 < (temperatureChart ν (x : ℂ)).re := by
  have hθ0 : 0 < Real.arccos (x/2) := Real.arccos_pos.mpr (by linarith)
  have hθπ : Real.arccos (x/2) < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have hlowre : 0 < (temperatureChart .low (x : ℂ)).re := temperatureChart_re_pos .low hx
  have hlowim : 0 < (temperatureChart .low (x : ℂ)).im := by
    rw [temperatureChart_low_real hx hx2]
    simpa only [Complex.exp_ofReal_mul_I, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
      mul_zero, add_zero, zero_add] using Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hfourlow := IsingBulk.Preferred22.first_quadrant_pow_four_ne_one hlowre hlowim
  refine ⟨?_,?_,temperatureChart_re_pos ν hx⟩
  · cases ν with
    | high =>
        rw [temperatureChart_high_real hx hx2]
        simpa only [← Complex.ofReal_neg] using
          Complex.norm_exp_ofReal_mul_I (-Real.arccos (x/2))
    | low =>
        rw [temperatureChart_low_real hx hx2]
        exact Complex.norm_exp_ofReal_mul_I _
  · cases ν with
    | low => exact hfourlow
    | high =>
        intro hfour
        apply hfourlow
        change ((temperatureChart .high (x : ℂ))⁻¹)^4=1
        rw [inv_pow,hfour,inv_one]

theorem normalization_analyticAt_positiveDomain (ν : Phase) {s : ℂ}
    (hs : s ∈ positiveTemperatureDomain ν) : AnalyticAt ℂ (normalization ν) s := by
  cases ν with
  | high =>
      exact (IsingBulk.HT.Final.interiorFourthFactor_analyticAt hs.1).div
        analyticAt_id (positiveTemperatureDomain_ne_zero hs)
  | low => exact normalization_low_analyticAt hs.1

theorem normalization_analyticAt_temperatureChart (ν : Phase) {E : ℂ}
    (hE0 : 0 < E.re) (hE2 : E.re < 2) (hEi : 0 ≤ E.im) :
    AnalyticAt ℂ (normalization ν) (temperatureChart ν E) := by
  rcases lt_or_eq_of_le hEi with hpos | heq
  · exact normalization_analyticAt_positiveDomain ν
      (temperatureChart_mapsTo_positiveDomain ν hE0 hpos)
  · have hreal : E = (E.re : ℂ) := by apply Complex.ext <;> simp [← heq]
    rw [hreal]
    have hgeo := temperatureChart_real_geometry ν hE0 hE2
    exact (normalization_regular_at_unit_nonaxis ν hgeo.1 hgeo.2.1).1

theorem normalization_analyticOn_chart_closedCollar (ν : Phase) {a b R : ℝ}
    (ha : 0 < a) (hb : b < 2) :
    AnalyticOnNhd ℂ (normalization ν) (temperatureChart ν '' closedUpperCollar a b R) := by
  rintro s ⟨E,hE,rfl⟩
  exact normalization_analyticAt_temperatureChart ν (ha.trans hE.1.1.1)
    (hE.1.1.2.trans hb) hE.2

theorem physicalPrefactor_analyticOn_chart_closedCollar (ν : Phase) {J : ℝ}
    (hJ : 0 < J) {a b R : ℝ} (ha : 0 < a) (hb : b < 2) :
    AnalyticOnNhd ℂ (physicalPrefactor ν J) (temperatureChart ν '' closedUpperCollar a b R) := by
  rintro s ⟨E,hE,rfl⟩
  exact (IsingBulk.Final.inverseTemperatureBranch_regular
    (temperatureChart_re_pos ν (ha.trans hE.1.1.1)) hJ).1.mul
    (normalization_analyticAt_temperatureChart ν (ha.trans hE.1.1.1)
      (hE.1.1.2.trans hb) hE.2)

theorem energy_analyticOn_chart_closedCollar (ν : Phase) {a b R : ℝ} :
    AnalyticOnNhd ℂ energy (temperatureChart ν '' closedUpperCollar a b R) := by
  rintro s ⟨E,_hE,rfl⟩
  exact energy_analyticAt (temperatureChart_ne_zero ν E)

theorem reduced_eq_energy_product_of_ne_zero (ν : Phase) {s : ℂ} (hs : s ≠ 0) :
    reducedSusceptibility ν s = fullEnergySum ν .positive (energy s)*normalization ν s := by
  simp only [reducedSusceptibility,hs,and_false,ite_false]
  ring

theorem physical_eq_energy_product_of_ne_zero (ν : Phase) (J : ℝ) {s : ℂ} (hs : s ≠ 0) :
    physicalSusceptibility ν J s = fullEnergySum ν .positive (energy s)*physicalPrefactor ν J s := by
  rw [physicalSusceptibility,reduced_eq_energy_product_of_ne_zero ν hs]
  unfold physicalPrefactor
  ring

theorem reduced_energy_product_germ (ν : Phase) {E : ℂ} :
    reducedSusceptibility ν =ᶠ[𝓝 (temperatureChart ν E)]
      (fullEnergySum ν .positive ∘ energy)*normalization ν := by
  filter_upwards [eventually_ne_nhds (temperatureChart_ne_zero ν E)] with s hs
  exact reduced_eq_energy_product_of_ne_zero ν hs

theorem physical_energy_product_germ (ν : Phase) (J : ℝ) {E : ℂ} :
    physicalSusceptibility ν J =ᶠ[𝓝 (temperatureChart ν E)]
      (fullEnergySum ν .positive ∘ energy)*physicalPrefactor ν J := by
  filter_upwards [eventually_ne_nhds (temperatureChart_ne_zero ν E)] with s hs
  exact physical_eq_energy_product_of_ne_zero ν J hs

end
end IsoProof
