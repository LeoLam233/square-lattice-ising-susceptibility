import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Exact constrained-contour and sector arithmetic in manuscript (5), (7), (8).
No pole gap or deformation identity is assumed or asserted by these lemmas. -/
namespace IsoProof
noncomputable section
open scoped BigOperators

/-- Center used in the common deformation of the constrained torus. -/
def contourCenter {N : ℕ} (f : ℝ → ℝ) (r : Fin N → ℝ) : ℝ :=
  (∑ i, f (r i))/(N : ℝ)

/-- Literal piecewise-linear graph from the manuscript. -/
def constrainedGraph {N : ℕ} (f : ℝ → ℝ) (r : Fin N → ℝ) (v : ℝ)
    (i : Fin N) : ℂ :=
  (r i : ℂ) + Complex.I*(v*(f (r i)-contourCenter f r) : ℝ)

theorem sum_centeredContour {N : ℕ} (hN : 0 < N)
    (f : ℝ → ℝ) (r : Fin N → ℝ) :
    (∑ i, (f (r i)-contourCenter f r)) = 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, contourCenter]
  field_simp
  ring

/-- The full complex angular sum is preserved exactly, not just modulo 2pi. -/
theorem constrainedGraph_sum {N : ℕ} (hN : 0 < N)
    (f : ℝ → ℝ) (r : Fin N → ℝ) (v : ℝ) :
    (∑ i, constrainedGraph f r v i) = ((∑ i, r i : ℝ) : ℂ) := by
  simp only [constrainedGraph, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_sum, ← Finset.mul_sum, sum_centeredContour hN, mul_zero,
    Complex.ofReal_zero, add_zero]

theorem constrainedGraph_im_sum {N : ℕ} (hN : 0 < N)
    (f : ℝ → ℝ) (r : Fin N → ℝ) (v : ℝ) :
    (∑ i, (constrainedGraph f r v i).im) = 0 := by
  have h := congrArg Complex.im (constrainedGraph_sum hN f r v)
  simpa using h

/-- In an interior collision chart the graph is affine with common slope. -/
theorem constrainedGraph_collision {N : ℕ} (hN : 0 < N)
    (f : ℝ → ℝ) (q₀ ε : ℝ) (w : Fin N → ℝ)
    (hw : ∑ i, w i = 0) (hf : ∀ i, f (q₀+w i) = q₀+w i) (i : Fin N) :
    constrainedGraph f (fun i => q₀+w i) ε i =
      (q₀ : ℂ)+(1+Complex.I*(ε : ℂ))*(w i : ℂ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : contourCenter f (fun i => q₀+w i) = q₀ := by
    simp only [contourCenter, hf, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hw, add_zero]
    field_simp
  simp only [constrainedGraph, hf, hc]
  push_cast
  ring

/-- A nonnegative imaginary part cannot cancel a ray strictly above the real axis. -/
theorem upper_quadratic_im_bound (η : ℂ) {d h ε Q : ℝ}
    (hd : 0 ≤ d) (_hh : 0 ≤ h) (_hε : 0 ≤ ε) (_hQ : 0 ≤ Q)
    (hη : 0 ≤ η.im) :
    2*h*ε*Q ≤ ‖(d : ℂ)*η+(h : ℂ)*(1+Complex.I*(ε : ℂ))^2*(Q : ℂ)‖ := by
  have him : ((d : ℂ)*η+(h : ℂ)*(1+Complex.I*(ε : ℂ))^2*(Q : ℂ)).im =
      d*η.im+2*h*ε*Q := by
    simp only [pow_two, Complex.mul_im, Complex.mul_re, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.one_re, Complex.one_im]
    ring
  have hn := Complex.im_le_norm ((d : ℂ)*η+(h : ℂ)*(1+Complex.I*(ε : ℂ))^2*(Q : ℂ))
  rw [him] at hn
  nlinarith [mul_nonneg hd hη]

/-- In particular the model denominator has no zero on the closed upper
half-plane whenever Q>0 and the graph has positive slope. -/
theorem upper_quadratic_ne_zero (η : ℂ) {d h ε Q : ℝ}
    (hd : 0 ≤ d) (hh : 0 < h) (hε : 0 < ε) (hQ : 0 < Q)
    (hη : 0 ≤ η.im) :
    (d : ℂ)*η+(h : ℂ)*(1+Complex.I*(ε : ℂ))^2*(Q : ℂ) ≠ 0 := by
  intro hz
  have hb := upper_quadratic_im_bound η hd hh.le hε.le hQ.le hη
  rw [hz, norm_zero] at hb
  have hp : 0 < 2*h*ε*Q := by positivity
  linarith

/-- The quadratic model in (8) has a uniform linear lower bound in
`norm eta + Q` throughout the closed upper half-plane.  The constant is
constructed explicitly from d,h,epsilon. -/
theorem upper_quadratic_uniform_lower {d h ε : ℝ}
    (hd : 0 < d) (hh : 0 < h) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (η : ℂ) (Q : ℝ), 0 ≤ η.im → 0 ≤ Q →
      c*(‖η‖+Q) ≤
        ‖(d : ℂ)*η+(h : ℂ)*(1+Complex.I*(ε : ℂ))^2*(Q : ℂ)‖ := by
  let a : ℝ := 2*h*ε
  let b : ℝ := h*‖(1+Complex.I*(ε : ℂ))^2‖
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hden : 0 < a+b+d := by positivity
  refine ⟨d*a/(a+b+d), by positivity, ?_⟩
  intro η Q hη hQ
  let D : ℂ := (d : ℂ)*η+(h : ℂ)*(1+Complex.I*(ε : ℂ))^2*(Q : ℂ)
  have hQbound : a*Q ≤ ‖D‖ := upper_quadratic_im_bound η hd.le hh.le hε.le hQ hη
  have hshift : (d : ℂ)*η = D - (h : ℂ)*(1+Complex.I*(ε : ℂ))^2*(Q : ℂ) := by
    dsimp [D]
    ring
  have hnorm : d*‖η‖ ≤ ‖D‖+b*Q := by
    have ht := norm_sub_le D ((h : ℂ)*(1+Complex.I*(ε : ℂ))^2*(Q : ℂ))
    rw [← hshift] at ht
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hd, abs_of_pos hh, abs_of_nonneg hQ, b] using ht
  have hmain : d*a*(‖η‖+Q) ≤ (a+b+d)*‖D‖ := by
    have hn := mul_le_mul_of_nonneg_left hnorm ha.le
    have hq := mul_le_mul_of_nonneg_left hQbound (add_nonneg hb hd.le)
    nlinarith
  rw [div_mul_eq_mul_div]
  change d*a*(‖η‖+Q)/(a+b+d) ≤ ‖D‖
  apply (div_le_iff₀ hden).mpr
  nlinarith

end
end IsoProof
