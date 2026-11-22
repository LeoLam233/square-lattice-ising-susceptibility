import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Literal real graph and dispersion phase in manuscript Section 3.
The quantitative real curvature comes from the actual arccosine formula. -/
namespace IsoProof
noncomputable section
open scoped Topology

def cutHalfWidth (x : ℝ) : ℝ := Real.arccos (x-1)

def cutPhase (x r : ℝ) : ℝ := Real.arccos (x-Real.cos r)

/-- The odd piecewise-linear displacement on [-pi,pi]. Its values at the
identified endpoints are both zero; the contour is therefore periodic. -/
def contourDisplacement (b r : ℝ) : ℝ :=
  if |r| ≤ b then r else
    if 0 ≤ r then b*(Real.pi-r)/(Real.pi-b)
    else -b*(Real.pi+r)/(Real.pi-b)

theorem contourDisplacement_interior {b r : ℝ} (hr : |r| ≤ b) :
    contourDisplacement b r = r := by simp [contourDisplacement, hr]

theorem contourDisplacement_odd {b : ℝ} (hb : 0 ≤ b) (r : ℝ) :
    contourDisplacement b (-r) = -contourDisplacement b r := by
  unfold contourDisplacement
  simp only [abs_neg]
  split_ifs <;> try ring
  · have hr : r = 0 := by linarith
    subst r
    simp at *
    linarith
  · exfalso
    linarith

theorem contourDisplacement_endpoints {b : ℝ} (hb : b < Real.pi) :
    contourDisplacement b Real.pi = 0 ∧ contourDisplacement b (-Real.pi) = 0 := by
  have hpi := Real.pi_pos
  have hp : ¬ Real.pi ≤ b := not_le.mpr hb
  constructor
  · simp only [contourDisplacement, abs_of_pos hpi, hp, ite_false, hpi.le,
      ite_true, sub_self, mul_zero, zero_div]
  · simp only [contourDisplacement, abs_neg, abs_of_pos hpi, hp, ite_false,
      show ¬ 0 ≤ -Real.pi by linarith, add_neg_cancel, mul_zero, zero_div]

theorem cutHalfWidth_range {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    0 < cutHalfWidth x ∧ cutHalfWidth x < Real.pi := by
  constructor
  · exact Real.arccos_pos.mpr (by linarith)
  · exact Real.arccos_lt_pi.mpr (by linarith)

theorem cutPhase_argument_range {x r : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hr : |r| < cutHalfWidth x) :
    -1 < x-Real.cos r ∧ x-Real.cos r < 1 := by
  obtain ⟨hb,hbpi⟩ := cutHalfWidth_range hx hx2
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg r) hbpi.le hr
  rw [Real.cos_abs, cutHalfWidth, Real.cos_arccos (by linarith) (by linarith)] at hc
  constructor
  · linarith [Real.cos_le_one r]
  · linarith

theorem cutPhase_sin_pos {x r : ℝ}
    (hW : -1 < x-Real.cos r) (hW' : x-Real.cos r < 1) :
    0 < Real.sin (cutPhase x r) :=
  Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hW')
    (Real.arccos_lt_pi.mpr hW)

theorem cutPhase_hasDerivAt {x r : ℝ}
    (hW : -1 < x-Real.cos r) (hW' : x-Real.cos r < 1) :
    HasDerivAt (cutPhase x) (-Real.sin r / Real.sin (cutPhase x r)) r := by
  have hd := (Real.hasDerivAt_arccos (ne_of_gt hW) (ne_of_lt hW')).comp r
    ((Real.hasDerivAt_cos r).const_sub x)
  convert hd using 1
  · rfl
  · simp only [cutPhase, Real.sin_arccos]
    ring

/-- The twice-differentiated dispersion relation reduced algebraically. -/
theorem real_phase_curvature_quotient (x c t y z : ℝ) (hz : z ≠ 0)
    (hy : y = x-c) (ht : t^2+c^2=1) (hp : z^2+y^2=1) :
    ((-c)*z-(-t)*(y*(-t/z)))/z^2 = -x*(1-x*c+c^2)/z^3 := by
  rw [hy] at hp ⊢
  field_simp
  linear_combination -c*hp-(x-c)*ht

/-- The actual second derivative stated before equation (5). -/
theorem cutPhase_second_hasDerivAt {x r : ℝ}
    (hW : -1 < x-Real.cos r) (hW' : x-Real.cos r < 1) :
    HasDerivAt (deriv (cutPhase x))
      (-x*(1-x*Real.cos r+(Real.cos r)^2)/(Real.sin (cutPhase x r))^3) r := by
  have hw : ∀ᶠ t in 𝓝 r, -1 < x-Real.cos t ∧ x-Real.cos t < 1 := by
    have hc : ContinuousAt (fun t => x-Real.cos t) r := by fun_prop
    exact (continuousAt_const.eventually_lt hc hW).and
      (hc.eventually_lt continuousAt_const hW')
  have he : deriv (cutPhase x) =ᶠ[𝓝 r]
      (fun t => -Real.sin t / Real.sin (cutPhase x t)) := by
    filter_upwards [hw] with t ht
    exact (cutPhase_hasDerivAt ht.1 ht.2).deriv
  have hg := cutPhase_hasDerivAt hW hW'
  have hs : Real.sin (cutPhase x r) ≠ 0 := (cutPhase_sin_pos hW hW').ne'
  have hds := (Real.hasDerivAt_sin (cutPhase x r)).comp r hg
  have hq := ((Real.hasDerivAt_sin r).neg).div hds hs
  have hy : Real.cos (cutPhase x r) = x-Real.cos r :=
    Real.cos_arccos hW.le hW'.le
  have hr := real_phase_curvature_quotient x (Real.cos r) (Real.sin r)
    (Real.cos (cutPhase x r)) (Real.sin (cutPhase x r)) hs hy
    (Real.sin_sq_add_cos_sq r) (Real.sin_sq_add_cos_sq (cutPhase x r))
  simp only [Function.comp_apply, Pi.neg_apply] at hq
  rw [hr] at hq
  exact hq.congr_of_eventuallyEq he

/-- An explicit positive lower curvature constant, uniform throughout the
oscillatory interval; its construction does not use compactness. -/
theorem cutPhase_curvature_lower {x r : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hr : |r| < cutHalfWidth x) :
    0 < x*(1-x^2/4) ∧
    x*(1-x^2/4) ≤ -deriv (deriv (cutPhase x)) r := by
  obtain ⟨hW,hW'⟩ := cutPhase_argument_range hx hx2 hr
  have hs := cutPhase_sin_pos hW hW'
  have hA : 0 < x*(1-x^2/4) := by
    have : 0 < 1-x^2/4 := by nlinarith
    positivity
  have hnum : x*(1-x^2/4) ≤ x*(1-x*Real.cos r+(Real.cos r)^2) := by
    nlinarith [mul_nonneg hx.le (sq_nonneg (Real.cos r-x/2))]
  have hden : (Real.sin (cutPhase x r))^3 ≤ 1 :=
    pow_le_one₀ hs.le (Real.sin_le_one _)
  refine ⟨hA, ?_⟩
  rw [(cutPhase_second_hasDerivAt hW hW').deriv]
  have hbound : x*(1-x^2/4) ≤
      x*(1-x*Real.cos r+(Real.cos r)^2)/(Real.sin (cutPhase x r))^3 := by
    apply (le_div_iff₀ (pow_pos hs 3)).mpr
    exact (mul_le_mul_of_nonneg_left hden hA.le).trans (by simpa using hnum)
  convert hbound using 1; ring

/-- Integrating the actual strict curvature gives the real first-order
phase gain used in (5). -/
theorem cutPhase_slope_drop {x c r : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hc : |c| < cutHalfWidth x) (hr : |r| < cutHalfWidth x) (hcr : c < r) :
    x*(1-x^2/4)*(r-c) ≤ deriv (cutPhase x) c-deriv (cutPhase x) r := by
  have harg (t : ℝ) (ht : t ∈ Set.Icc c r) : |t| < cutHalfWidth x := by
    rw [abs_lt] at hc hr ⊢
    exact ⟨hc.1.trans_le ht.1, ht.2.trans_lt hr.2⟩
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc c r) :
      DifferentiableAt ℝ (deriv (cutPhase x)) t := by
    obtain ⟨hW,hW'⟩ := cutPhase_argument_range hx hx2 (harg t ht)
    exact (cutPhase_second_hasDerivAt hW hW').differentiableAt
  have hcont : ContinuousOn (deriv (cutPhase x)) (Set.Icc c r) :=
    fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
  have hdint : DifferentiableOn ℝ (deriv (cutPhase x)) (Set.Ioo c r) :=
    fun t ht => (hdiff t ⟨ht.1.le,ht.2.le⟩).differentiableWithinAt
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope (deriv (cutPhase x)) hcr hcont hdint
  have hcurv := (cutPhase_curvature_lower hx hx2 (harg t ⟨ht.1.le,ht.2.le⟩)).2
  rw [he] at hcurv
  have hs : (deriv (cutPhase x) r-deriv (cutPhase x) c)/(r-c) ≤
      -(x*(1-x^2/4)) := by linarith
  have hm := (div_le_iff₀ (sub_pos.mpr hcr)).mp hs
  nlinarith

/-- The exact positive quadratic real gain is valid on both sides of c. -/
theorem cutPhase_first_order_gain {x c r : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hc : |c| < cutHalfWidth x) (hr : |r| < cutHalfWidth x) :
    x*(1-x^2/4)*(r-c)^2 ≤
      (r-c)*(deriv (cutPhase x) c-deriv (cutPhase x) r) := by
  rcases lt_trichotomy c r with hcr | hcr | hcr
  · have h := mul_le_mul_of_nonneg_left
      (cutPhase_slope_drop hx hx2 hc hr hcr) (sub_nonneg.mpr hcr.le)
    nlinarith
  · subst r
    simp
  · have h := mul_le_mul_of_nonneg_left
      (cutPhase_slope_drop hx hx2 hr hc hcr) (sub_nonneg.mpr hcr.le)
    nlinarith

end
end IsoProof
