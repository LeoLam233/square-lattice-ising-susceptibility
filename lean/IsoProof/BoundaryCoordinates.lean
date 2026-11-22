import IsoProof.ContourPhysical
import IsoProof.PhysicalBoundary
import IsoProof.ResonanceCoordinate
import IsoProof.JetTrace
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected

/-! Actual one-sided energy charts used by the separant argument.  The
rotated-cut root extends analytically through 0<E<2; on the open upper half
plane it is proved to equal the physical disk root. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def positiveTemperatureDomain (ν : Phase) : Set ℂ :=
  physicalDomain ν ∩ {s : ℂ | 0 < s.re}

theorem positiveTemperatureDomain_isOpen (ν : Phase) : IsOpen (positiveTemperatureDomain ν) := by
  cases ν
  · exact (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  · exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_const Complex.continuous_re)

theorem positiveTemperatureDomain_ne_zero {ν : Phase} {s : ℂ}
    (hs : s ∈ positiveTemperatureDomain ν) : s ≠ 0 := by
  intro hz
  have h : 0 < s.re := hs.2
  simp only [hz,Complex.zero_re,lt_self_iff_false] at h

theorem positiveHalfDisk_convex : Convex ℝ (positiveTemperatureDomain .high) := by
  simpa only [positiveTemperatureDomain, physicalDomain, Metric.ball, dist_zero_right]
    using (convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_gt 0)

theorem inverse_image_positiveHalfDisk :
    (fun s : ℂ => s⁻¹) '' positiveTemperatureDomain .high = positiveTemperatureDomain .low := by
  ext s
  constructor
  · rintro ⟨u,hu,rfl⟩
    have hu0 := positiveTemperatureDomain_ne_zero hu
    refine ⟨?_,?_⟩
    · change 1 < ‖u⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr hu.1
    · change 0 < (u⁻¹).re
      rw [Complex.inv_re]
      exact div_pos hu.2 (Complex.normSq_pos.mpr hu0)
  · intro hs
    have hs0 := positiveTemperatureDomain_ne_zero hs
    refine ⟨s⁻¹, ⟨?_,?_⟩,inv_inv s⟩
    · change ‖s⁻¹‖ < 1
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hs.1
    · change 0 < (s⁻¹).re
      rw [Complex.inv_re]
      exact div_pos hs.2 (Complex.normSq_pos.mpr hs0)

theorem positiveTemperatureDomain_isPreconnected (ν : Phase) :
    IsPreconnected (positiveTemperatureDomain ν) := by
  cases ν with
  | high => exact positiveHalfDisk_convex.isPreconnected
  | low =>
      rw [← inverse_image_positiveHalfDisk]
      apply positiveHalfDisk_convex.isPreconnected.image
      intro s hs
      have han : AnalyticAt ℂ (fun z : ℂ => z⁻¹) s :=
        analyticAt_id.inv (positiveTemperatureDomain_ne_zero hs)
      exact han.continuousAt.continuousWithinAt

theorem realTemperature_mem_positiveDomain (ν : Phase) {s : ℝ}
    (hs : s ∈ realTemperatureDomain ν) : (s : ℂ) ∈ positiveTemperatureDomain ν := by
  have hp : 0 < s := by cases ν with
    | high => exact hs.1
    | low => exact lt_trans zero_lt_one hs
  refine ⟨?_,by simpa using hp⟩
  cases ν with
  | high =>
      change ‖(s : ℂ)‖ < 1
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp] using hs.2
  | low =>
      change 1 < ‖(s : ℂ)‖
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp] using (show 1 < s from hs)

def temperatureChart (ν : Phase) (E : ℂ) : ℂ :=
  match ν with
  | .high => continuedTransferRoot (E/2)
  | .low => (continuedTransferRoot (E/2))⁻¹

theorem temperatureChart_ne_zero (ν : Phase) (E : ℂ) : temperatureChart ν E ≠ 0 := by
  cases ν with
  | high => exact continuedTransferRoot_ne_zero _
  | low => exact inv_ne_zero (continuedTransferRoot_ne_zero _)

theorem energy_temperatureChart (ν : Phase) (E : ℂ) : energy (temperatureChart ν E)=E := by
  have h := continuedTransferRoot_trace (E/2)
  cases ν <;> simp only [temperatureChart,energy,inv_inv] <;> linear_combination h

theorem temperatureChart_injective (ν : Phase) : Function.Injective (temperatureChart ν) := by
  intro E F h
  simpa only [energy_temperatureChart] using congrArg energy h

theorem half_energy_mem_contourRootDomain {E : ℂ} (hE0 : 0 < E.re) (hE2 : E.re < 2) :
    E/2 ∈ contourRootDomain := by
  constructor
  · right
    have h : 0 < (-Complex.I*(E/2-1)).im := by
      simp only [Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
        Complex.sub_re,Complex.one_re,neg_zero,zero_mul,zero_add]
      simp only [Complex.div_ofNat_re]
      linarith
    exact h.ne'
  · left
    simp only [Complex.add_re,Complex.div_ofNat_re,Complex.one_re]
    linarith

theorem temperatureChart_analyticAt (ν : Phase) {E : ℂ}
    (hE0 : 0 < E.re) (hE2 : E.re < 2) : AnalyticAt ℂ (temperatureChart ν) E := by
  have hh : AnalyticAt ℂ (fun z : ℂ => z/2) E := analyticAt_id.div_const
  have hr := (continuedTransferRoot_analyticAt
    (half_energy_mem_contourRootDomain hE0 hE2)).comp (f := fun z : ℂ => z/2) hh
  cases ν with
  | high => exact hr
  | low => exact hr.inv (continuedTransferRoot_ne_zero _)

theorem temperatureChart_deriv_ne_zero (ν : Phase) {E : ℂ}
    (hE0 : 0 < E.re) (hE2 : E.re < 2) : deriv (temperatureChart ν) E ≠ 0 := by
  have hcomp := (energy_hasDerivAt (temperatureChart_ne_zero ν E)).comp E
    (temperatureChart_analyticAt ν hE0 hE2).differentiableAt.hasDerivAt
  have hid : HasDerivAt (fun z : ℂ => z)
      ((1-((temperatureChart ν E)^2)⁻¹)*deriv (temperatureChart ν) E) E := by
    simpa only [Function.comp_def,energy_temperatureChart] using! hcomp
  have he := hid.unique (hasDerivAt_id E)
  intro hz
  rw [hz,mul_zero] at he
  exact zero_ne_one he

theorem temperatureChart_low_eq_exterior {E : ℂ} (hE : 0 < E.im) :
    temperatureChart .low E = exteriorEnergyInverse E := by
  unfold temperatureChart exteriorEnergyInverse
  rw [continuedTransferRoot_eq_physicalRoot (by simpa using half_pos hE)]

theorem temperatureChart_high_eq_exterior_inv {E : ℂ} (hE : 0 < E.im) :
    temperatureChart .high E = (exteriorEnergyInverse E)⁻¹ := by
  unfold temperatureChart exteriorEnergyInverse
  rw [inv_inv, continuedTransferRoot_eq_physicalRoot (by simpa using half_pos hE)]

theorem temperatureChart_re_pos (ν : Phase) {E : ℂ} (hE : 0 < E.re) :
    0 < (temperatureChart ν E).re := by
  have htrace := congrArg Complex.re (energy_temperatureChart ν E)
  simp only [energy,Complex.add_re,Complex.inv_re] at htrace
  by_contra hbad
  have hr : (temperatureChart ν E).re ≤ 0 := le_of_not_gt hbad
  have hdiv : (temperatureChart ν E).re / Complex.normSq (temperatureChart ν E) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hr (Complex.normSq_nonneg _)
  linarith

theorem temperatureChart_mapsTo_positiveDomain (ν : Phase) {E : ℂ}
    (hEre : 0 < E.re) (hEim : 0 < E.im) :
    temperatureChart ν E ∈ positiveTemperatureDomain ν := by
  refine ⟨?_,temperatureChart_re_pos ν hEre⟩
  have hroot := continuedTransferRoot_upper_norm
    (show 0 < (E/2).im by simpa using half_pos hEim)
  cases ν with
  | high => exact hroot
  | low =>
      change 1 < ‖(continuedTransferRoot (E/2))⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr (continuedTransferRoot_ne_zero _))).mpr hroot

theorem temperatureChart_analyticOn_closedCollar (ν : Phase) {a b R : ℝ}
    (ha : 0 < a) (hb : b < 2) :
    AnalyticOnNhd ℂ (temperatureChart ν) (closedUpperCollar a b R) := by
  intro E hE
  exact temperatureChart_analyticAt ν (ha.trans hE.1.1.1) (hE.1.1.2.trans hb)

theorem temperatureChart_mapsTo_collar (ν : Phase) {a b R : ℝ} (ha : 0 < a) :
    MapsTo (temperatureChart ν) (upperCollar a b R) (positiveTemperatureDomain ν) :=
  fun _ hE => temperatureChart_mapsTo_positiveDomain ν (ha.trans hE.1.1.1) hE.2

theorem reduced_positiveDomain_analyticOn (ν : Phase) :
    AnalyticOnNhd ℂ (reducedSusceptibility ν) (positiveTemperatureDomain ν) :=
  (reduced_analyticOn ν).mono inter_subset_left

theorem physical_positiveDomain_analyticOn (ν : Phase) {J : ℝ} (hJ : 0 < J) :
    AnalyticOnNhd ℂ (physicalSusceptibility ν J) (positiveTemperatureDomain ν) := by
  intro s hs
  exact (IsingBulk.Final.inverseTemperatureBranch_regular hs.2 hJ).1.mul
    (reduced_analyticOn ν s hs.1)

end
end IsoProof
