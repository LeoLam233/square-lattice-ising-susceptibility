import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The shrinking E-disc calculation in (6). This file proves the generic
Cauchy step; construction of the holomorphic site integral and the Gaussian
bound on that disc must supply its displayed hypotheses. -/
namespace IsoProof
noncomputable section
open Metric

theorem cauchy_site_exponent (f : ℂ → ℂ) (E : ℂ) (A N j : ℕ)
    {δ M : ℝ} (hδ : 0 < δ)
    (hf : DiffContOnCl ℂ f (ball E (δ/(1+(A : ℝ)))))
    (hM : ∀ z ∈ sphere E (δ/(1+(A : ℝ))),
      ‖f z‖ ≤ M*(1+(A : ℝ))^(-(N : ℝ)/2)) :
    ‖iteratedDeriv j f E‖ ≤
      ((j.factorial : ℝ)/δ^j)*M*(1+(A : ℝ))^((j : ℝ)-(N : ℝ)/2) := by
  have hbase : (0 : ℝ) < 1+(A : ℝ) := by positivity
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    j (div_pos hδ hbase) hf hM
  have hpow : (1+(A : ℝ))^(-(N : ℝ)/2)*(1+(A : ℝ))^j =
      (1+(A : ℝ))^((j : ℝ)-(N : ℝ)/2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hbase]
    congr 1
    ring
  have he : (j.factorial : ℝ)*(M*(1+(A : ℝ))^(-(N : ℝ)/2)) /
      (δ/(1+(A : ℝ)))^j =
      ((j.factorial : ℝ)/δ^j)*M*(1+(A : ℝ))^((j : ℝ)-(N : ℝ)/2) := by
    rw [← hpow, div_pow]
    field_simp
  exact hc.trans_eq he

/-- A fixed derivative-order factor can be absorbed in an exponential
particle envelope without changing the spatial exponent. -/
theorem fixed_factor_absorbed (K C t : ℝ) (hC : 0 ≤ C) (ht : 0 ≤ t)
    {N : ℕ} (hN : 0 < N) :
    K*(C*t)^N ≤ (max 1 K*C*t)^N := by
  have hm : K ≤ (max 1 K)^N :=
    (le_max_right 1 K).trans (le_self_pow₀ (le_max_left 1 K) hN.ne')
  calc
    K*(C*t)^N ≤ (max 1 K)^N*(C*t)^N :=
      mul_le_mul_of_nonneg_right hm (pow_nonneg (mul_nonneg hC ht) N)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end
end IsoProof
