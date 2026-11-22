import IsoProof.PhysicalIdentification
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The real restrictions of the prescribed complex fourth roots are the
positive real roots throughout the full physical temperature intervals. -/
namespace IsoProof
noncomputable section

theorem high_normalization_real {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    normalization .high (s:ℂ) = (((1-s^4)^(1/4:ℝ)/s : ℝ):ℂ) := by
  have hr : 0 < 1-s^4 := sub_pos.mpr (pow_lt_one₀ hs.le hs1 (by norm_num : 4 ≠ 0))
  have hc := Complex.ofReal_cpow hr.le (1/4:ℝ)
  simp only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow,
    Complex.ofReal_div,Complex.ofReal_ofNat] at hc
  simp only [normalization,Complex.ofReal_div,hc,Complex.cpow_eq_pow]

theorem low_normalization_real {s : ℝ} (hs : 1 < s) :
    normalization .low (s:ℂ) = (((1-s⁻¹^4)^(1/4:ℝ) : ℝ):ℂ) := by
  have hsi : 0 < s⁻¹ := inv_pos.mpr (zero_lt_one.trans hs)
  have hsi1 : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  have hr : 0 < 1-s⁻¹^4 := sub_pos.mpr
    (pow_lt_one₀ hsi.le hsi1 (by norm_num : 4 ≠ 0))
  have hc := Complex.ofReal_cpow hr.le (1/4:ℝ)
  simpa only [normalization,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow,
    Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.cpow_eq_pow] using hc.symm

/-- The low-temperature subtraction is precisely the positive fourth root
M squared, with its fourth-power law proved rather than supplied as input. -/
theorem spontaneousSquare_low_real_positive {s : ℝ} (hs : 1 < s) :
    spontaneousSquare .low s = (((1-s⁻¹^4)^(1/4:ℝ) : ℝ):ℂ) ∧
    0 < (spontaneousSquare .low s).re ∧
    (spontaneousSquare .low s)^4 = 1-(s:ℂ)⁻¹^4 := by
  have hsi : 0 < s⁻¹ := inv_pos.mpr (zero_lt_one.trans hs)
  have hr : 0 < 1-s⁻¹^4 := sub_pos.mpr
    (pow_lt_one₀ hsi.le (inv_lt_one_of_one_lt₀ hs) (by norm_num : 4 ≠ 0))
  refine ⟨low_normalization_real hs,?_,?_⟩
  · rw [spontaneousSquare,low_normalization_real hs,Complex.ofReal_re]
    exact Real.rpow_pos_of_pos hr _
  · change (Complex.cpow (1-(s:ℂ)⁻¹^4) (1/4:ℂ))^4 = _
    simpa only [one_div,Complex.cpow_eq_pow,Nat.cast_ofNat] using
      Complex.cpow_nat_inv_pow (1-(s:ℂ)⁻¹^4) (by norm_num : (4:ℕ) ≠ 0)

end
end IsoProof
