import IsoProof.ContourRoot
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! The continued phase is defined from the concrete root, rather than
introduced by an axiom about a physical lift. Its real boundary value,
dispersion identity and derivatives are read from that definition. -/
namespace IsoProof
noncomputable section
open scoped Topology

/-- The logarithm stays on its principal analytic sheet throughout the
protected dispersion domain. -/
theorem continuedTransferRoot_mem_slitPlane {W : ℂ} (hW : W ∈ contourRootDomain) :
    continuedTransferRoot W ∈ Complex.slitPlane := by
  let u := continuedTransferRoot W
  have hut : u+u⁻¹=2*W := continuedTransferRoot_trace W
  have hu0 : u ≠ 0 := continuedTransferRoot_ne_zero W
  by_cases hi : u.im ≠ 0
  · exact Or.inr hi
  · have hui : u.im=0 := not_ne_iff.mp hi
    have hreal : u = (u.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hui
    have htrace := congrArg Complex.re hut
    have him := congrArg Complex.im hut
    rw [hreal, ← Complex.ofReal_inv] at htrace him
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] at htrace
    simp at him
    have hWim : W.im=0 := by linarith
    have hlow : -1 < W.re := by
      rcases hW.2 with h | h
      · have hh : 0 < W.re+1 := by simpa using h
        linarith
      · simp [hWim] at h
    left
    by_contra hn
    have ha : u.re ≤ 0 := le_of_not_gt hn
    have ha0 : u.re ≠ 0 := by
      intro h
      apply hu0
      rw [hreal,h]
      simp
    have han : u.re < 0 := lt_of_le_of_ne ha ha0
    have hp := congrArg (fun z : ℝ => u.re*z) htrace
    simp only [mul_add,mul_inv_cancel₀ ha0] at hp
    have hneg : u.re*(W.re+1) < 0 :=
      mul_neg_of_neg_of_pos han (by linarith)
    nlinarith [sq_nonneg (u.re+1)]

def continuedPhase (W : ℂ) : ℂ := Complex.I*Complex.log (continuedTransferRoot W)

theorem continuedPhase_exp (W : ℂ) :
    Complex.exp (-Complex.I*continuedPhase W) = continuedTransferRoot W := by
  rw [continuedPhase]
  have h : -Complex.I*(Complex.I*Complex.log (continuedTransferRoot W)) =
      Complex.log (continuedTransferRoot W) := by
    calc
      _ = -(Complex.I^2)*Complex.log (continuedTransferRoot W) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [h,Complex.exp_log (continuedTransferRoot_ne_zero W)]

theorem continuedPhase_cos (W : ℂ) : Complex.cos (continuedPhase W)=W := by
  have hneg := continuedPhase_exp W
  have hpos : Complex.exp (Complex.I*continuedPhase W) = (continuedTransferRoot W)⁻¹ := by
    rw [show Complex.I*continuedPhase W = -(-Complex.I*continuedPhase W) by ring,
      Complex.exp_neg,hneg]
  have ht := continuedTransferRoot_trace W
  have hc := Complex.two_cos (continuedPhase W)
  rw [show continuedPhase W*Complex.I = Complex.I*continuedPhase W by ring,
    show -continuedPhase W*Complex.I = -Complex.I*continuedPhase W by ring,hpos,hneg] at hc
  linear_combination (hc+ht)/2

theorem continuedPhase_im (W : ℂ) :
    (continuedPhase W).im = Real.log ‖continuedTransferRoot W‖ := by
  simp [continuedPhase,Complex.log_re]

theorem continuedPhase_analyticAt {W : ℂ} (hW : W ∈ contourRootDomain) :
    AnalyticAt ℂ continuedPhase W := by
  exact analyticAt_const.mul
    ((continuedTransferRoot_analyticAt hW).clog (continuedTransferRoot_mem_slitPlane hW))

theorem continuedPhase_sin_ne_zero {W : ℂ} (hW : W ∈ contourRootDomain) :
    Complex.sin (continuedPhase W) ≠ 0 := by
  intro h
  have hp := Complex.sin_sq_add_cos_sq (continuedPhase W)
  rw [h,zero_pow (by decide),zero_add,continuedPhase_cos] at hp
  exact contourRootDomain_sq_ne_one hW hp

theorem continuedPhase_hasDerivAt {W : ℂ} (hW : W ∈ contourRootDomain) :
    HasDerivAt continuedPhase (-1/Complex.sin (continuedPhase W)) W := by
  have hφ := (continuedPhase_analyticAt hW).differentiableAt.hasDerivAt
  have hc := (Complex.hasDerivAt_cos (continuedPhase W)).comp W hφ
  have heq : (Complex.cos ∘ continuedPhase) = (fun W : ℂ => W) :=
    funext continuedPhase_cos
  rw [heq] at hc
  have hd := hc.unique (hasDerivAt_id W)
  have hs := continuedPhase_sin_ne_zero hW
  convert hφ using 1
  symm
  apply (eq_div_iff hs).mpr
  linear_combination -hd

theorem continuedPhase_real_interior {W : ℝ} (hW : -1 < W) (hW1 : W < 1) :
    continuedPhase (W : ℂ) = (Real.arccos W : ℂ) := by
  rw [continuedPhase,continuedTransferRoot_real_interior hW hW1]
  rw [Complex.log_exp]
  · calc
      _ = -(Complex.I^2)*(Real.arccos W : ℂ) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  · simp only [Complex.mul_im,Complex.neg_re,Complex.I_re,neg_zero,
      Complex.ofReal_im,mul_zero,Complex.neg_im,Complex.I_im,
      Complex.ofReal_re,neg_one_mul,zero_add]
    linarith [Real.arccos_lt_pi.mpr hW]
  · simp only [Complex.mul_im,Complex.neg_re,Complex.I_re,neg_zero,
      Complex.ofReal_im,mul_zero,Complex.neg_im,Complex.I_im,
      Complex.ofReal_re,neg_one_mul,zero_add]
    linarith [Real.arccos_nonneg W,Real.pi_pos]

theorem continuedPhase_angle_hasDerivAt {E q : ℂ}
    (hW : E-Complex.cos q ∈ contourRootDomain) :
    HasDerivAt (fun q => continuedPhase (E-Complex.cos q))
      (-Complex.sin q/Complex.sin (continuedPhase (E-Complex.cos q))) q := by
  have h := (continuedPhase_hasDerivAt hW).comp q
    ((Complex.hasDerivAt_cos q).const_sub E)
  convert h using 1
  · rfl
  · ring

end
end IsoProof
