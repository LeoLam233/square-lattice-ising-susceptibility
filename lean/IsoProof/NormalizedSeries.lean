import IsoProof.SeriesAtInfinity
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.RemovableSingularity

/-! The normalized series in w=1/(2E), including their actual removable germ
at w=0.  The punctured formula is exactly F_nu(1/(2w)); the value at zero is
the unique analytic continuation produced from the proved infinity bound. -/
namespace IsoProof
noncomputable section
open Complex Filter Set Metric Function
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem seriesCoordinate_involutive : Function.Involutive seriesCoordinate := by
  intro z
  simp only [seriesCoordinate, mul_inv_rev, inv_inv]
  ring

theorem seriesCoordinate_ne_zero {z : ℂ} (hz : z ≠ 0) : seriesCoordinate z ≠ 0 :=
  inv_ne_zero (mul_ne_zero (by norm_num) hz)

theorem seriesCoordinate_analyticAt {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ seriesCoordinate z :=
  (analyticAt_const.mul analyticAt_id).inv (mul_ne_zero (by norm_num) hz)

theorem seriesCoordinate_hasDerivAt {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt seriesCoordinate (-(2 : ℂ)/(2*z)^2) z := by
  simpa only [mul_one,seriesCoordinate] using!
    ((hasDerivAt_id z).const_mul (2 : ℂ)).inv (mul_ne_zero (by norm_num) hz)

theorem seriesCoordinate_deriv_ne_zero {z : ℂ} (hz : z ≠ 0) :
    deriv seriesCoordinate z ≠ 0 := by
  rw [(seriesCoordinate_hasDerivAt hz).deriv]
  exact div_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero (by norm_num) hz))

/-- The plane with the two outer real rays removed, including w=0. -/
def normalizedSeriesDomain : Set ℂ := {w : ℂ | w.im ≠ 0 ∨ |w.re| < 1/4}

theorem normalizedSeriesDomain_isOpen : IsOpen normalizedSeriesDomain :=
  (isOpen_ne_fun Complex.continuous_im continuous_const).union
    (isOpen_lt Complex.continuous_re.abs continuous_const)

theorem zero_mem_normalizedSeriesDomain : (0 : ℂ) ∈ normalizedSeriesDomain := by
  right
  norm_num

theorem normalizedSeriesDomain_starConvex :
    StarConvex ℝ (0 : ℂ) normalizedSeriesDomain := by
  apply starConvex_zero_iff.mpr
  intro z hz t ht ht1
  by_cases ht0 : t=0
  · simpa only [ht0,zero_smul] using zero_mem_normalizedSeriesDomain
  rcases hz with hi | hr
  · left
    simpa only [Complex.smul_im,smul_eq_mul] using mul_ne_zero ht0 hi
  · right
    rw [Complex.smul_re,smul_eq_mul,abs_mul,abs_of_nonneg ht]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht1).trans_lt hr

theorem normalizedSeriesDomain_isPreconnected : IsPreconnected normalizedSeriesDomain :=
  (normalizedSeriesDomain_starConvex.isPathConnected zero_mem_normalizedSeriesDomain).isConnected.isPreconnected

theorem seriesCoordinate_mem_energyDomain {w : ℂ} (hw0 : w ≠ 0)
    (hw : w ∈ normalizedSeriesDomain) : seriesCoordinate w ∈ energyDomain := by
  by_cases hi : w.im=0
  · have hre : |w.re| < 1/4 := hw.resolve_left (not_ne_iff.mpr hi)
    apply energyDomain_of_norm_gt_two
    have hn : ‖w‖ < 1/4 := by rwa [← Complex.abs_re_eq_norm.mpr hi]
    have hp : 0 < 2*‖w‖ := mul_pos (by norm_num) (norm_pos_iff.mpr hw0)
    rw [seriesCoordinate,norm_inv,norm_mul,Complex.norm_ofNat,inv_eq_one_div]
    apply (lt_div_iff₀ hp).mpr
    nlinarith
  · left
    change ((2*w)⁻¹).im ≠ 0
    rw [Complex.inv_im]
    apply div_ne_zero
    · simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hi
    · exact (Complex.normSq_pos.mpr (mul_ne_zero (by norm_num) hw0)).ne'

def rawNormalizedSeries (ν : Phase) (w : ℂ) : ℂ :=
  fullEnergySum ν .positive (seriesCoordinate w)

def normalizedSeries (ν : Phase) : ℂ → ℂ :=
  Function.update (rawNormalizedSeries ν) 0
    (Filter.limUnder (𝓝[≠] (0 : ℂ)) (rawNormalizedSeries ν))

theorem normalizedSeries_eq {ν : Phase} {w : ℂ} (hw : w ≠ 0) :
    normalizedSeries ν w = fullEnergySum ν .positive (seriesCoordinate w) :=
  Function.update_of_ne hw _ _

theorem rawNormalizedSeries_analyticAt (ν : Phase) {w : ℂ}
    (hw0 : w ≠ 0) (hw : w ∈ normalizedSeriesDomain) :
    AnalyticAt ℂ (rawNormalizedSeries ν) w :=
  (fullEnergySum_positive_analyticOn ν _ (seriesCoordinate_mem_energyDomain hw0 hw)).comp
    (seriesCoordinate_analyticAt hw0)

theorem seriesCoordinate_far_of_small {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ < 1/40) :
    17 < ‖seriesCoordinate w‖ := by
  have hp : 0 < 2*‖w‖ := mul_pos (by norm_num) (norm_pos_iff.mpr hw0)
  rw [seriesCoordinate,norm_inv,norm_mul,Complex.norm_ofNat,inv_eq_one_div]
  apply (lt_div_iff₀ hp).mpr
  nlinarith

theorem normalizedSeries_analyticAt_zero (ν : Phase) :
    AnalyticAt ℂ (normalizedSeries ν) 0 := by
  let U : Set ℂ := ball 0 (1/40)
  have hU : U ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ (by norm_num)
  have hd : DifferentiableOn ℂ (rawNormalizedSeries ν) (U \ {0}) := by
    intro w hw
    have hn : ‖w‖ < 1/40 := by simpa only [U,mem_ball,dist_zero_right] using hw.1
    have hD : w ∈ normalizedSeriesDomain := Or.inr
      ((Complex.abs_re_le_norm w).trans_lt (by linarith : ‖w‖ < 1/4))
    exact (rawNormalizedSeries_analyticAt ν hw.2 hD).differentiableAt.differentiableWithinAt
  obtain ⟨M,hM⟩ := fullEnergySum_far_bounded ν
  have hb : BddAbove (norm ∘ rawNormalizedSeries ν '' (U \ {0})) := by
    refine ⟨M, ?_⟩
    rintro y ⟨w,hw,rfl⟩
    exact hM _ (seriesCoordinate_far_of_small hw.2 (by
      simpa only [U,mem_ball,dist_zero_right] using hw.1))
  exact (Complex.differentiableOn_update_limUnder_of_bddAbove hU hd hb).analyticAt hU

theorem normalizedSeries_analyticOn (ν : Phase) :
    AnalyticOnNhd ℂ (normalizedSeries ν) normalizedSeriesDomain := by
  intro w hw
  by_cases hw0 : w=0
  · simpa only [hw0] using normalizedSeries_analyticAt_zero ν
  · apply (rawNormalizedSeries_analyticAt ν hw0 hw).congr
    filter_upwards [eventually_ne_nhds hw0] with z hz
    exact (normalizedSeries_eq hz).symm

/-- The same normalization is obtained on any energy collar. -/
theorem normalizedSeries_at_seriesCoordinate (ν : Phase) {E : ℂ} (hE : E ≠ 0) :
    normalizedSeries ν (seriesCoordinate E) = fullEnergySum ν .positive E := by
  rw [normalizedSeries_eq (seriesCoordinate_ne_zero hE), seriesCoordinate_involutive E]

end
end IsoProof
