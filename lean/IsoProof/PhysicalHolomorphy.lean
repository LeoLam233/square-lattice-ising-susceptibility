import IsoProof.PhysicalOrigin
import IsoProof.IntegralsParity
import IsingBulk.Preferred22.NormalConvergence

/-! Both literal susceptibility functions are holomorphic on their complete
physical temperature domains. The high-temperature origin was proved in
PhysicalOrigin; the low-temperature fourth root stays on its prescribed
principal sheet since its radicand has positive real part. -/
namespace IsoProof
noncomputable section
open Filter Set
open scoped Topology

theorem normalization_low_eq_magnetization (s : ℂ) :
    normalization .low s = IsingBulk.Preferred22.magnetizationSquared s := by
  simp only [normalization, IsingBulk.Preferred22.magnetizationSquared, inv_pow]
  rfl

theorem low_fourth_root_argument_re_pos {s : ℂ} (hs : 1 < ‖s‖) :
    0 < (1-(s^4)⁻¹).re := by
  have hp : 1 < ‖s‖^4 := by
    have hs2 : 1 < ‖s‖^2 := by nlinarith [norm_nonneg s]
    nlinarith [sq_nonneg (‖s‖^2-1)]
  have hn : ‖(s^4)⁻¹‖ < 1 := by
    rw [norm_inv, norm_pow]
    exact inv_lt_one_of_one_lt₀ hp
  have hr := (Complex.re_le_norm ((s^4)⁻¹)).trans_lt hn
  simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hr

theorem normalization_low_analyticAt {s : ℂ} (hs : 1 < ‖s‖) :
    AnalyticAt ℂ (normalization .low) s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have ha : AnalyticAt ℂ (fun t : ℂ => 1-(t^4)⁻¹) s :=
    analyticAt_const.sub ((analyticAt_id.pow 4).inv (pow_ne_zero 4 hs0))
  have hp : (1-(s^4)⁻¹) ∈ Complex.slitPlane :=
    Or.inl (low_fourth_root_argument_re_pos hs)
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [ha.eventually_analyticAt,
    ha.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hp)] with t ht htp
  change DifferentiableAt ℂ (fun x : ℂ => (1-(x⁻¹)^4)^(1/4 : ℂ)) t
  simp_rw [inv_pow]
  exact ht.differentiableAt.cpow_const htp

theorem normalization_low_ne_zero {s : ℂ} (hs : 1 < ‖s‖) :
    normalization .low s ≠ 0 := by
  rw [normalization_low_eq_magnetization]
  apply Complex.cpow_ne_zero_iff.mpr
  left
  intro he
  have h := low_fourth_root_argument_re_pos hs
  rw [he] at h
  norm_num at h

/-- Actual full-series bridge, retaining the physical low-temperature
normalization, rather than merely identifying the unnormalized series. -/
theorem reduced_low_eq_existing {s : ℂ} (hs : 1 < ‖s‖) :
    reducedSusceptibility .low s = IsingBulk.Preferred22.bulkFunction s := by
  simp only [reducedSusceptibility, reduceCtorEq, false_and, ite_false]
  rw [fullEnergySum_low_energy hs, normalization_low_eq_magnetization]
  rfl

theorem reduced_low_analyticOn :
    AnalyticOnNhd ℂ (reducedSusceptibility .low) (physicalDomain .low) := by
  intro s hs
  have ha : AnalyticAt ℂ (fun t => normalization .low t * IsingBulk.Preferred22.evenSeries t) s :=
    (normalization_low_analyticAt hs).mul (IsingBulk.Preferred22.evenSeries_analyticAt hs)
  apply ha.congr
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hs] with t ht
  simp only [reducedSusceptibility, reduceCtorEq, false_and, ite_false,
    fullEnergySum_low_energy ht]

theorem reduced_analyticOn (ν : Phase) :
    AnalyticOnNhd ℂ (reducedSusceptibility ν) (physicalDomain ν) := by
  cases ν
  · exact reduced_high_analyticOn
  · exact reduced_low_analyticOn

end
end IsoProof
