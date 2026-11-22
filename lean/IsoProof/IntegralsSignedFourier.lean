import IsoProof.IntegralsBridge
import IsingBulk.HT.Contour.FourierTorusCoordinates

/-! The signed horizontal Fourier slice is evaluated at zero or pi on the
actual total-angle torus.  Absolute summability is obtained from the proved
full-lattice contour representation before Fourier inversion is applied. -/
namespace IsoProof
noncomputable section
open Set IsingBulk.First IsingBulk.HT.Contour IsingBulk.HT.Final
open scoped BigOperators

local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- The manuscript's full square-lattice character, with integer signs
represented by natural absolute exponents. -/
def latticeSign (σ : Sign) (p : ℤ × ℤ) : ℂ :=
  signValue σ ^ (p.1.natAbs + p.2.natAbs)

@[simp] theorem signValue_norm (σ : Sign) : ‖signValue σ‖ = 1 := by
  cases σ <;> simp [signValue]

theorem signValue_ne_zero (σ : Sign) : signValue σ ≠ 0 := by
  cases σ <;> simp [signValue]

theorem signValue_zpow_natAbs (σ : Sign) (k : ℤ) :
    signValue σ ^ k = signValue σ ^ k.natAbs := by
  cases σ <;> cases k <;> simp [signValue, zpow_negSucc, ← inv_pow]

/-- This is exactly sigma^(a+b), including negative displacements. -/
theorem latticeSign_eq_zpow (σ : Sign) (p : ℤ × ℤ) :
    latticeSign σ p = signValue σ ^ (p.1+p.2) := by
  rw [zpow_add₀ (signValue_ne_zero σ), signValue_zpow_natAbs,
    signValue_zpow_natAbs]
  exact pow_add _ _ _

@[simp] theorem latticeSign_norm (σ : Sign) (p : ℤ × ℤ) :
    ‖latticeSign σ p‖ = 1 := by
  simp [latticeSign, norm_pow]

@[simp] theorem latticeSign_positive (p : ℤ × ℤ) : latticeSign .positive p = 1 := by
  simp [latticeSign, signValue]

/-- The horizontal character is the true Fourier mode at the signed
constraint, not an imposed Kronecker delta. -/
theorem fourier_at_signAngle (σ : Sign) (k : ℤ) :
    fourier k ((signAngle σ : ℝ) : AddCircle (2*Real.pi)) =
      signValue σ ^ k.natAbs := by
  rw [fourier_twoPi_eq_exp]
  cases σ with
  | positive => simp [signAngle, signValue]
  | negative =>
    change Complex.exp (Complex.I*(k:ℂ)*(Real.pi:ℂ)) = (-1:ℂ)^k.natAbs
    rw [show Complex.I*(k:ℂ)*(Real.pi:ℂ) =
      (k:ℂ)*((Real.pi:ℂ)*Complex.I) by ring,
      Complex.exp_int_mul, Complex.exp_pi_mul_I]
    exact signValue_zpow_natAbs .negative k

theorem torusMeanCircle_signAngle (σ : Sign) (n : ℕ)
    (F : (Fin (n+1) → ℝ) → ℂ) (hF : Continuous F)
    (hperiod : CoordinatePeriodic (n+1) F) :
    torusMeanCircle n F hF hperiod (signAngle σ : AddCircle (2*Real.pi)) =
      ((2*(Real.pi:ℂ))⁻¹)^n *
        multiAngleIntegral n (fun q => F (constrainedAngles σ n q)) := by
  have hs : signAngle σ ∈ Ico 0 (2*Real.pi) := by
    cases σ <;> simp only [signAngle, mem_Ico] <;> constructor <;>
      linarith [Real.pi_pos]
  change AddCircle.liftIco (2*Real.pi) 0 (torusMeanSlice n F)
    (signAngle σ : AddCircle (2*Real.pi)) = _
  rw [AddCircle.liftIco_zero_coe_apply hs]
  rfl

theorem constrainedAngles_continuous (σ : Sign) (n : ℕ) :
    Continuous (constrainedAngles σ n) := by
  exact (continuous_torusTotalAngle n).comp
    (continuous_const.prodMk continuous_id)

/-- The actual signed total-angle slice at a fixed vertical displacement.
The vertical character is inserted only when the vertical lattice is summed. -/
def signedConstrainedVerticalCoefficient (σ : Sign) (n : ℕ) (t : ℝ) (m : ℕ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹ * ((2*(Real.pi:ℂ))⁻¹)^n *
    multiAngleIntegral n (fun q =>
      ((physicalAngularWeight t (constrainedAngles σ n q) *
        physicalZ t (constrainedAngles σ n q)^m : ℝ):ℂ))

/-- True Fourier inversion at the sign-dependent total angle, for every
positive particle number and every vertical displacement. -/
theorem physicalLatticeCoefficient_horizontal_signed_tsum (σ : Sign) (n m : ℕ)
    {t : ℝ} (ht : 1 < t) :
    (∑' k : ℤ, signValue σ ^ k.natAbs * physicalLatticeCoefficient (n+1) t m k) =
      signedConstrainedVerticalCoefficient σ n t m := by
  let c : ℂ := ((n+1).factorial:ℂ)⁻¹
  let F : (Fin (n+1) → ℝ) → ℂ := fun q =>
    c*((physicalAngularWeight t q * physicalZ t q^m : ℝ):ℂ)
  have hF : Continuous F := continuous_const.mul (Complex.continuous_ofReal.comp
    ((physicalAngularWeight_continuous (n+1) ht).mul
      ((physicalZ_continuous (n+1) ht).pow m)))
  have hperiod : CoordinatePeriodic (n+1) F := by
    have hA : CoordinatePeriodic (n+1) (fun q =>
        ((physicalAngularWeight t q * physicalZ t q^m : ℝ):ℂ)) := by
      simpa only [Int.cast_zero,mul_zero,zero_mul,Complex.exp_zero,mul_one] using
        physical_latticeAngularIntegrand_periodic (n+1) ht m 0
    intro q j
    exact congrArg (fun z : ℂ => c*z) (hA q j)
  let f : C(AddCircle (2*Real.pi),ℂ) := torusMeanCircle n F hF hperiod
  have hcoefficient (k : ℤ) :
      physicalLatticeCoefficient (n+1) t m k = fourierCoeff f (-k) := by
    change physicalLatticeCoefficient (n+1) t m k =
      fourierCoeff (torusMeanCircle n F hF hperiod) (-k)
    rw [← torus_exponential_coefficient n F hF hperiod k]
    unfold physicalLatticeCoefficient
    simp only [F,mul_assoc]
    rw [physical_multiAngleIntegral_const_mul]
    dsimp only [c]
    ring
  have hq : Summable (fun k : ℤ => physicalLatticeCoefficient (n+1) t m k) := by
    simpa only [physicalFullLatticeCoefficient,Int.natAbs_natCast] using
      (IsingBulk.HT22.Physical.fullLattice_norm_summable (by omega : 0 < n+1)
        ht).of_norm.prod_factor (m:ℤ)
  have hcoeff : ∀ k : ℤ, physicalLatticeCoefficient (n+1) t m k =
      fourierCoeff f k := by
    intro k
    have hk := hcoefficient (-k)
    rw [neg_neg,physicalLatticeCoefficient_horizontal_reflection (n+1) ht m k] at hk
    exact hk
  have hf : Summable (fourierCoeff f) := hq.congr hcoeff
  calc
    (∑' k : ℤ, signValue σ ^ k.natAbs * physicalLatticeCoefficient (n+1) t m k) =
        f (signAngle σ : AddCircle (2*Real.pi)) := by
      convert (has_pointwise_sum_fourier_series_of_summable hf
        (signAngle σ : AddCircle (2*Real.pi))).tsum_eq using 1
      apply tsum_congr
      intro k
      rw [hcoeff k, fourier_at_signAngle]
      simp only [smul_eq_mul, mul_comm]
    _ = signedConstrainedVerticalCoefficient σ n t m := by
      change torusMeanCircle n F hF hperiod (signAngle σ : AddCircle (2*Real.pi)) = _
      rw [torusMeanCircle_signAngle]
      dsimp only [F]
      rw [physical_multiAngleIntegral_const_mul]
      unfold signedConstrainedVerticalCoefficient
      dsimp only [c]
      ring

end
end IsoProof
