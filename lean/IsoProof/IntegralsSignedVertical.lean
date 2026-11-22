import IsoProof.IntegralsSignedFourier

/-! The full signed vertical lattice is summed under the actual constrained
integral using a proved geometric majorant.  The endpoint is the literal
particle density, including the same sign in its constraint and pole factor. -/
namespace IsoProof
noncomputable section
open Set MeasureTheory IsingBulk.First IsingBulk.HT.Contour IsingBulk.HT.Final
open scoped BigOperators

/-- Both signed real densities, with their unchanged complete pair product. -/
theorem particleDensity_energy_real (σ : Sign) {N : ℕ} {t : ℝ}
    (ht : 1 < t) (q : Fin N → ℝ) :
    particleDensity σ (energy (t:ℂ)) q =
      (physicalAngularWeight t q:ℂ) *
        ((1+signValue σ*(physicalZ t q:ℂ))/(1-signValue σ*(physicalZ t q:ℂ))) := by
  cases σ with
  | positive =>
    rw [particleDensity_energy]
    change IsingBulk.HT22.Physical.signedAngularDensity false (t:ℂ) q = _
    rw [IsingBulk.HT22.Physical.signedAngularDensity_positive_real ht]
    simp only [signValue,one_mul,Complex.ofReal_mul,Complex.ofReal_div,
      Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_one]
  | negative =>
    rw [particleDensity_energy]
    change IsingBulk.HT22.Physical.signedAngularDensity true (t:ℂ) q = _
    rw [IsingBulk.HT22.Physical.signedAngularDensity_negative_real ht]
    simp only [signValue,neg_one_mul,sub_neg_eq_add,
      Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_add,
      Complex.ofReal_sub,Complex.ofReal_one]
    ring

/-- Every vertical displacement is retained, including zero and both signs;
there is no passage from a one-sided series to an unproved lattice formula. -/
theorem signedConstrainedVerticalCoefficient_summable_eq_particle
    (σ : Sign) (n : ℕ) {t : ℝ} (ht : 1 < t) :
    Summable (fun m : ℤ =>
      ‖signValue σ ^ m.natAbs * signedConstrainedVerticalCoefficient σ n t m.natAbs‖) ∧
    (∑' m : ℤ, signValue σ ^ m.natAbs *
      signedConstrainedVerticalCoefficient σ n t m.natAbs) =
      particleCoefficient σ (n+1) (energy (t:ℂ)) := by
  let S := angleBox n
  let K : ℂ := ((n+1).factorial:ℂ)⁻¹ * ((2*(Real.pi:ℂ))⁻¹)^n
  let A : (Fin n → ℝ) → ℂ := fun q =>
    (physicalAngularWeight t (constrainedAngles σ n q):ℂ)
  let Z0 : (Fin n → ℝ) → ℂ := fun q =>
    (physicalZ t (constrainedAngles σ n q):ℂ)
  let Z : (Fin n → ℝ) → ℂ := fun q => signValue σ * Z0 q
  let rho : ℝ := (physicalRoot t 0)^(n+1)
  let F : ℤ → (Fin n → ℝ) → ℂ := fun m q => A q * Z q^m.natAbs
  have hA : Continuous A := Complex.continuous_ofReal.comp
    ((physicalAngularWeight_continuous (n+1) ht).comp
      (constrainedAngles_continuous σ n))
  have hZ0c : Continuous Z0 := Complex.continuous_ofReal.comp
    ((physicalZ_continuous (n+1) ht).comp (constrainedAngles_continuous σ n))
  have hZc : Continuous Z := continuous_const.mul hZ0c
  have hrho : 0 ≤ rho := pow_nonneg (physicalRoot_bounds ht 0).1.le _
  have hrho1 : rho < 1 :=
    pow_lt_one₀ (physicalRoot_bounds ht 0).1.le (physicalRoot_bounds ht 0).2 (by omega)
  have hZ (q : Fin n → ℝ) : ‖Z q‖ ≤ rho := by
    simp only [Z,Z0,norm_mul,signValue_norm,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (physicalZ_pos ht (constrainedAngles σ n q))]
    exact physicalZ_le_zero_pow ht (constrainedAngles σ n q)
  have hZ1 (q : Fin n → ℝ) : ‖Z q‖ < 1 := (hZ q).trans_lt hrho1
  have hgap (q : Fin n → ℝ) : 1-Z q ≠ 0 := by
    intro he
    have hz : Z q=1 := (sub_eq_zero.mp he).symm
    have hh := hZ1 q
    rw [hz,norm_one] at hh
    exact lt_irrefl (1:ℝ) hh
  have hAi : IntegrableOn A S :=
    hA.continuousOn.integrableOn_compact isCompact_Icc
  have hFc (m : ℤ) : Continuous (F m) := hA.mul (hZc.pow m.natAbs)
  have hi (m : ℤ) : IntegrableOn (F m) S :=
    (hFc m).continuousOn.integrableOn_compact isCompact_Icc
  have hbound (m : ℤ) :
      (∫ q in S, ‖F m q‖) ≤ (∫ q in S, ‖A q‖)*rho^m.natAbs := by
    rw [← integral_mul_const]
    apply integral_mono (hi m).norm (hAi.norm.mul_const _)
    intro q
    simp only [F,norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg (Z q)) (hZ q) _) (norm_nonneg (A q))
  have hsI : Summable (fun m : ℤ => ∫ q in S, ‖F m q‖) :=
    ((physical_real_twoSided_geometric_summable hrho hrho1).mul_left
      (∫ q in S, ‖A q‖)).of_nonneg_of_le
        (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound
  have hsNorm : Summable (fun m : ℤ => ‖∫ q in S, F m q‖) :=
    hsI.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun _ => norm_integral_le_integral_norm _)
  have hbox0 (m : ℤ) : signedConstrainedVerticalCoefficient σ n t m.natAbs =
      K*(∫ q in S, A q*Z0 q^m.natAbs) := by
    have hc : Continuous (fun q : Fin n → ℝ =>
        ((physicalAngularWeight t (constrainedAngles σ n q) *
          physicalZ t (constrainedAngles σ n q)^m.natAbs : ℝ):ℂ)) := by
      have hc' : Continuous (fun q => A q * Z0 q ^ m.natAbs) :=
        hA.mul (hZ0c.pow m.natAbs)
      simpa only [A,Z0,Complex.ofReal_mul,Complex.ofReal_pow] using hc'
    unfold signedConstrainedVerticalCoefficient
    rw [multiAngleIntegral_eq_box n _ hc]
    simp only [Complex.ofReal_mul,Complex.ofReal_pow]
    rfl
  have hbox (m : ℤ) :
      signValue σ ^ m.natAbs * signedConstrainedVerticalCoefficient σ n t m.natAbs =
      K*(∫ q in S,F m q) := by
    rw [hbox0]
    have he : F m = fun q => signValue σ ^ m.natAbs * (A q*Z0 q^m.natAbs) := by
      funext q
      dsimp only [F,Z]
      rw [mul_pow]
      ring
    rw [he,integral_const_mul]
    ring
  have hKernel : Continuous (fun q => A q*((1+Z q)/(1-Z q))) :=
    hA.mul ((continuous_const.add hZc).div (continuous_const.sub hZc) hgap)
  have hparticle : particleCoefficient σ (n+1) (energy (t:ℂ)) =
      K*(∫ q in S,A q*((1+Z q)/(1-Z q))) := by
    have he : (fun q => particleDensity σ (energy (t:ℂ)) (constrainedAngles σ n q)) =
        fun q => A q*((1+Z q)/(1-Z q)) := by
      funext q
      exact particleDensity_energy_real σ ht _
    have hc : Continuous (fun q =>
        particleDensity σ (energy (t:ℂ)) (constrainedAngles σ n q)) := by
      rw [he]
      exact hKernel
    simp only [particleCoefficient,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
    change K * multiAngleIntegral n
      (fun q => particleDensity σ (energy (t:ℂ)) (constrainedAngles σ n q)) = _
    rw [multiAngleIntegral_eq_box n _ hc,he]
  constructor
  · simpa only [hbox,norm_mul] using hsNorm.mul_left ‖K‖
  · calc
      (∑' m : ℤ, signValue σ ^ m.natAbs *
          signedConstrainedVerticalCoefficient σ n t m.natAbs) =
          K*(∑' m : ℤ,∫ q in S,F m q) := by
        simp_rw [hbox]
        rw [tsum_mul_left]
      _ = K*(∫ q in S,∑' m : ℤ,F m q) := by
        rw [integral_tsum_of_summable_integral_norm hi hsI]
      _ = K*(∫ q in S,A q*((1+Z q)/(1-Z q))) := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Icc
        intro q _
        simp only [F,tsum_mul_left]
        rw [vertical_displacement_geometric_sum (hZ1 q)]
      _ = particleCoefficient σ (n+1) (energy (t:ℂ)) := hparticle.symm

/-- Formula (3) with its actual signed lattice character, at every real
physical exterior temperature and every positive particle number. -/
theorem particleCoefficient_eq_signed_site_tsum_real (σ : Sign)
    {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 1 < t) :
    particleCoefficient σ N (energy (t:ℂ)) =
      ∑' p : ℤ × ℤ, latticeSign σ p *
        siteCoefficient N p.1.natAbs p.2 (energy (t:ℂ)) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hs : Summable (fun p : ℤ × ℤ =>
      latticeSign σ p * physicalFullLatticeCoefficient (n+1) t p) := by
    apply Summable.of_norm
    simpa only [norm_mul,latticeSign_norm,one_mul] using
      IsingBulk.HT22.Physical.fullLattice_norm_summable (by omega : 0 < n+1) ht
  symm
  calc
    (∑' p : ℤ × ℤ, latticeSign σ p *
        siteCoefficient (n+1) p.1.natAbs p.2 (energy (t:ℂ))) =
        ∑' p : ℤ × ℤ, latticeSign σ p * physicalFullLatticeCoefficient (n+1) t p := by
      apply tsum_congr
      intro p
      rw [siteCoefficient_energy_real _ _ _ ht]
      rfl
    _ = ∑' a : ℤ, ∑' b : ℤ, latticeSign σ (a,b) *
        physicalFullLatticeCoefficient (n+1) t (a,b) := hs.tsum_prod
    _ = ∑' a : ℤ, signValue σ ^ a.natAbs *
        signedConstrainedVerticalCoefficient σ n t a.natAbs := by
      apply tsum_congr
      intro a
      rw [← physicalLatticeCoefficient_horizontal_signed_tsum σ n a.natAbs ht,
        ← tsum_mul_left]
      apply tsum_congr
      intro b
      simp only [latticeSign,pow_add,physicalFullLatticeCoefficient]
      ring
    _ = particleCoefficient σ (n+1) (energy (t:ℂ)) :=
      (signedConstrainedVerticalCoefficient_summable_eq_particle σ n ht).2

end
end IsoProof
