import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-! A single explicit continued root for the manuscript's common contour.
The first square root has its cut directed downward from W=1, so traversing
the oscillatory interval does not reselect the root inside the unit disk. -/
namespace IsoProof
noncomputable section
open scoped Topology

def contourQuarterTurn : ℂ := (1+Complex.I)/(Real.sqrt 2 : ℂ)

def downwardSquareRoot (z : ℂ) : ℂ :=
  contourQuarterTurn * Complex.sqrt (-Complex.I*z)

def continuedTransferRoot (W : ℂ) : ℂ :=
  W-downwardSquareRoot (W-1)*Complex.sqrt (W+1)

def contourRootDomain : Set ℂ :=
  {W | -Complex.I*(W-1) ∈ Complex.slitPlane ∧ W+1 ∈ Complex.slitPlane}

theorem contourQuarterTurn_sq : contourQuarterTurn^2 = Complex.I := by
  have hs : (Real.sqrt (2 : ℝ) : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hnum : (1+Complex.I)^2 = (2 : ℂ)*Complex.I := by
    ring_nf
    simp [Complex.I_sq]
  rw [contourQuarterTurn, div_pow, hs, hnum]
  ring

theorem complex_sqrt_square (z : ℂ) : (Complex.sqrt z)^2 = z := by
  exact Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

theorem downwardSquareRoot_sq (z : ℂ) : (downwardSquareRoot z)^2 = z := by
  rw [downwardSquareRoot, mul_pow, contourQuarterTurn_sq, complex_sqrt_square]
  calc
    Complex.I*(-Complex.I*z) = -(Complex.I^2)*z := by ring
    _ = z := by rw [Complex.I_sq]; ring

theorem continuedTransferRoot_product (W : ℂ) :
    continuedTransferRoot W *
      (W+downwardSquareRoot (W-1)*Complex.sqrt (W+1)) = 1 := by
  rw [continuedTransferRoot]
  calc
    _ = W^2-(downwardSquareRoot (W-1)*Complex.sqrt (W+1))^2 := by ring
    _ = 1 := by
      rw [mul_pow, downwardSquareRoot_sq, complex_sqrt_square]
      ring

theorem continuedTransferRoot_ne_zero (W : ℂ) : continuedTransferRoot W ≠ 0 := by
  intro h
  have hp := continuedTransferRoot_product W
  rw [h, zero_mul] at hp
  exact zero_ne_one hp

theorem continuedTransferRoot_inverse (W : ℂ) :
    (continuedTransferRoot W)⁻¹ =
      W+downwardSquareRoot (W-1)*Complex.sqrt (W+1) :=
  inv_eq_of_mul_eq_one_right (continuedTransferRoot_product W)

theorem continuedTransferRoot_trace (W : ℂ) :
    continuedTransferRoot W+(continuedTransferRoot W)⁻¹ = 2*W := by
  rw [continuedTransferRoot_inverse, continuedTransferRoot]
  ring

theorem continuedTransferRoot_quadratic (W : ℂ) :
    (continuedTransferRoot W)^2-2*W*continuedTransferRoot W+1 = 0 := by
  have h := congrArg (fun z : ℂ => z*continuedTransferRoot W)
    (continuedTransferRoot_trace W)
  rw [add_mul, inv_mul_cancel₀ (continuedTransferRoot_ne_zero W)] at h
  linear_combination h

theorem continuedTransferRoot_analyticAt {W : ℂ} (hW : W ∈ contourRootDomain) :
    AnalyticAt ℂ continuedTransferRoot W := by
  have hrot : AnalyticAt ℂ (fun V : ℂ => -Complex.I*(V-1)) W := by fun_prop
  have hplus : AnalyticAt ℂ (fun V : ℂ => V+1) W := by fun_prop
  have hsr : AnalyticAt ℂ (fun V : ℂ => Complex.sqrt (-Complex.I*(V-1))) W :=
    hrot.cpow analyticAt_const hW.1
  have hsp : AnalyticAt ℂ (fun V : ℂ => Complex.sqrt (V+1)) W :=
    hplus.cpow analyticAt_const hW.2
  exact analyticAt_id.sub ((analyticAt_const.mul hsr).mul hsp)

theorem real_mem_contourRootDomain {W : ℝ} (hW : -1 < W) (hW1 : W ≠ 1) :
    (W : ℂ) ∈ contourRootDomain := by
  constructor
  · right
    simpa using sub_ne_zero.mpr hW1.symm
  · left
    simpa using (show 0 < W+1 by linarith)

theorem upper_mem_contourRootDomain {W : ℂ} (hW : -1 < W.re) (hWi : 0 < W.im) :
    W ∈ contourRootDomain := by
  constructor
  · left
    simpa using hWi
  · left
    simpa using (show 0 < W.re+1 by linarith)

theorem graph_dispersion_im (x y r t : ℝ) :
    (((x : ℂ)+Complex.I*(y : ℂ))-
      Complex.cos ((r : ℂ)+Complex.I*(t : ℂ))).im =
      y+Real.sin r*Real.sinh t := by
  rw [show Complex.I*(t : ℂ) = (t : ℂ)*Complex.I by ring,
    Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]

theorem contour_sqrt_ofReal (x : ℝ) (hx : 0 ≤ x) :
    Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, add_self_div_two]

theorem downwardSquareRoot_ofReal_pos {t : ℝ} (ht : 0 < t) :
    downwardSquareRoot (t : ℂ) = (Real.sqrt t : ℂ) := by
  have hs : (Real.sqrt (2 : ℝ) : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsq : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hs0 : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq
  have hhalf : Real.sqrt (t/2) = Real.sqrt t/Real.sqrt 2 := by
    apply (eq_div_iff hsq).mpr
    rw [← Real.sqrt_mul (by positivity : 0 ≤ t/2)]
    congr 1
    ring
  rw [downwardSquareRoot, Complex.sqrt_eq_real_add_ite]
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht, Complex.neg_re, Complex.I_re, neg_zero,
    Complex.mul_re, Complex.ofReal_re, Complex.neg_im, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, Complex.mul_im, zero_add,
    neg_one_mul, add_zero, sub_zero, show ¬ 0 ≤ -t by linarith, ite_false]
  rw [hhalf]
  unfold contourQuarterTurn
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq, hs]
  ring

theorem downwardSquareRoot_ofReal_neg {t : ℝ} (ht : t < 0) :
    downwardSquareRoot (t : ℂ) = Complex.I*(Real.sqrt (-t) : ℂ) := by
  have hs : (Real.sqrt (2 : ℝ) : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsq : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hs0 : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq
  have hhalf : Real.sqrt (-t/2) = Real.sqrt (-t)/Real.sqrt 2 := by
    apply (eq_div_iff hsq).mpr
    rw [← Real.sqrt_mul (by linarith : 0 ≤ -t/2)]
    congr 1
    ring
  rw [downwardSquareRoot, Complex.sqrt_eq_real_add_ite]
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_neg ht, Complex.neg_re, Complex.I_re, neg_zero,
    Complex.mul_re, Complex.ofReal_re, Complex.neg_im, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, Complex.mul_im, zero_add,
    neg_one_mul, add_zero, sub_zero, show 0 ≤ -t by linarith, ite_true, one_mul]
  rw [hhalf]
  unfold contourQuarterTurn
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq, hs]

theorem continuedTransferRoot_real_exterior {W : ℝ} (hW : 1 < W) :
    continuedTransferRoot (W : ℂ) =
      ((W-Real.sqrt (W^2-1) : ℝ) : ℂ) := by
  have hminus : 0 < W-1 := by linarith
  have hplus : 0 ≤ W+1 := by linarith
  rw [continuedTransferRoot, show (W : ℂ)-1 = ((W-1 : ℝ) : ℂ) by push_cast; rfl,
    show (W : ℂ)+1 = ((W+1 : ℝ) : ℂ) by push_cast; rfl,
    downwardSquareRoot_ofReal_pos hminus, contour_sqrt_ofReal _ hplus]
  have he : Real.sqrt (W-1)*Real.sqrt (W+1) = Real.sqrt (W^2-1) := by
    rw [← Real.sqrt_mul hminus.le]
    congr 1
    ring
  rw [← Complex.ofReal_mul, he]
  push_cast
  rfl

theorem continuedTransferRoot_real_interior {W : ℝ}
    (hW : -1 < W) (hW1 : W < 1) :
    continuedTransferRoot (W : ℂ) =
      Complex.exp (-Complex.I*(Real.arccos W : ℂ)) := by
  have hminus : W-1 < 0 := by linarith
  have hplus : 0 ≤ W+1 := by linarith
  rw [continuedTransferRoot, show (W : ℂ)-1 = ((W-1 : ℝ) : ℂ) by push_cast; rfl,
    show (W : ℂ)+1 = ((W+1 : ℝ) : ℂ) by push_cast; rfl,
    downwardSquareRoot_ofReal_neg hminus, contour_sqrt_ofReal _ hplus]
  have he : Real.sqrt (-(W-1))*Real.sqrt (W+1) = Real.sqrt (1-W^2) := by
    rw [← Real.sqrt_mul (by linarith : 0 ≤ -(W-1))]
    congr 1
    ring
  have hmul : Complex.I*(Real.sqrt (-(W-1)) : ℂ)*(Real.sqrt (W+1) : ℂ) =
      Complex.I*(Real.sqrt (1-W^2) : ℂ) := by
    rw [mul_assoc, ← Complex.ofReal_mul, he]
  rw [hmul, show -Complex.I*(Real.arccos W : ℂ) =
      ((-Real.arccos W : ℝ) : ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Real.cos_arccos hW.le hW1.le,
    Real.sin_arccos, Complex.ofReal_neg]
  ring

/-- Two reciprocal values of one single-valued dispersion root must have
identical W. This is why branch coherence matters for pair-pole exclusion. -/
theorem continuedTransferRoot_reciprocal_trace {W V : ℂ}
    (hp : continuedTransferRoot W*continuedTransferRoot V = 1) : W = V := by
  have hinv : (continuedTransferRoot W)⁻¹ = continuedTransferRoot V :=
    inv_eq_of_mul_eq_one_right hp
  have hinv' : (continuedTransferRoot V)⁻¹ = continuedTransferRoot W :=
    inv_eq_of_mul_eq_one_right (by simpa only [mul_comm] using hp)
  have hW := continuedTransferRoot_trace W
  have hV := continuedTransferRoot_trace V
  rw [hinv] at hW
  rw [hinv'] at hV
  have he : (2 : ℂ)*W = 2*V := by
    calc
      _ = continuedTransferRoot W+continuedTransferRoot V := hW.symm
      _ = continuedTransferRoot V+continuedTransferRoot W := add_comm _ _
      _ = _ := hV
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) he

/-- A pair pole can only occur at the one-body branch values ±1, for this
specific globally coherent local sheet. -/
theorem continuedTransferRoot_pair_ne_one {W V : ℂ}
    (hW : W^2 ≠ 1) : continuedTransferRoot W*continuedTransferRoot V ≠ 1 := by
  intro hp
  have hWV := continuedTransferRoot_reciprocal_trace hp
  subst V
  have hu : (continuedTransferRoot W)^2 = 1 := by simpa only [pow_two] using hp
  have hi : (continuedTransferRoot W)⁻¹ = continuedTransferRoot W :=
    inv_eq_of_mul_eq_one_right hp
  have ht := continuedTransferRoot_trace W
  rw [hi] at ht
  have he : continuedTransferRoot W = W := by linear_combination ht/2
  exact hW (he ▸ hu)

theorem contourRootDomain_sq_ne_one {W : ℂ} (hW : W ∈ contourRootDomain) :
    W^2 ≠ 1 := by
  intro h
  have hp : (W-1)*(W+1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hp with hp | hp
  · have he : W = 1 := sub_eq_zero.mp hp
    subst W
    norm_num [contourRootDomain, Complex.slitPlane] at hW
  · have he : W = -1 := eq_neg_of_add_eq_zero_left hp
    subst W
    norm_num [contourRootDomain, Complex.slitPlane] at hW

theorem continuedTransferRoot_pair_gap {W V : ℂ}
    (hW : W ∈ contourRootDomain) :
    0 < ‖1-continuedTransferRoot W*continuedTransferRoot V‖ := by
  apply norm_pos_iff.mpr
  exact sub_ne_zero.mpr (Ne.symm (continuedTransferRoot_pair_ne_one
    (contourRootDomain_sq_ne_one hW)))

end
end IsoProof
