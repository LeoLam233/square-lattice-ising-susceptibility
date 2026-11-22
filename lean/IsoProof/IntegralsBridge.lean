import IsoProof.Objects
import IsingBulk.HT.Contour.PhysicalLatticeContour
import IsingBulk.HT22.Physical.RealIdentification

/-!
Exact bridges for equations (1)--(3) of the five-page manuscript. The energy
coordinate is literal. No convergence assertion is inferred merely from a
`tsum` definition. All statements below concern the defined integral.
-/
namespace IsoProof
noncomputable section
open scoped BigOperators
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour

private def signBool : Sign → Bool
  | .positive => false
  | .negative => true

theorem angleRoot_energy (s : ℂ) (q : ℝ) :
    angleRoot (energy s) q = IsingBulk.HT22.Physical.angularRoot s q := rfl

theorem angleRoot_ne_zero (E : ℂ) (q : ℝ) : angleRoot E q ≠ 0 :=
  IsingBulk.Preferred22.physicalRoot_ne_zero _

theorem angleRoot_trace (E : ℂ) (q : ℝ) :
    angleRoot E q + (angleRoot E q)⁻¹ = 2*(E - (Real.cos q : ℂ)) :=
  IsingBulk.Preferred22.physicalRoot_trace _

theorem angleRoot_inside {E : ℂ} (hE : E ∈ energyDomain) (q : ℝ) :
    ‖angleRoot E q‖ < 1 := by
  apply IsingBulk.Preferred22.physicalRoot_inside
  rcases hE with hE | hE
  · left
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hE
  · right
    simp only [Complex.sub_re, Complex.ofReal_re]
    rcases lt_or_gt_of_ne (show E.re ≠ 0 by intro h; rw [h, abs_zero] at hE; norm_num at hE) with hn | hp
    · have he : E.re < -2 := by rw [abs_of_neg hn] at hE; linarith
      rw [abs_of_neg (by linarith [Real.neg_one_le_cos q])]
      linarith [Real.neg_one_le_cos q]
    · have he : 2 < E.re := by simpa [abs_of_pos hp] using hE
      rw [abs_of_pos (by linarith [Real.cos_le_one q])]
      linarith [Real.cos_le_one q]

theorem angleRoot_analyticAt {E : ℂ} (hE : E ∈ energyDomain) (q : ℝ) :
    AnalyticAt ℂ (fun z => angleRoot z q) E := by
  have hW : IsingBulk.Preferred22.OffRealSegment (E - (Real.cos q : ℂ)) := by
    rcases hE with hE | hE
    · left
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hE
    · right
      simp only [Complex.sub_re, Complex.ofReal_re]
      by_cases he : 0 ≤ E.re
      · have hx : 2 < E.re := by simpa [abs_of_nonneg he] using hE
        rw [abs_of_pos (by linarith [Real.cos_le_one q])]
        linarith [Real.cos_le_one q]
      · have hx : E.re < -2 := by
          have := hE
          rw [abs_of_neg (lt_of_not_ge he)] at this
          linarith
        rw [abs_of_neg (by linarith [Real.neg_one_le_cos q])]
        linarith [Real.neg_one_le_cos q]
  exact (IsingBulk.Preferred22.physicalRoot_analyticAt hW).comp
    (f := fun z : ℂ => z - (Real.cos q : ℂ)) (analyticAt_id.sub analyticAt_const)

theorem root_pair_gap {E : ℂ} (hE : E ∈ energyDomain) (q r : ℝ) :
    1-angleRoot E q*angleRoot E r ≠ 0 := by
  intro h
  have he : angleRoot E q*angleRoot E r = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖angleRoot E q*angleRoot E r‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (angleRoot_inside hE r).le (norm_nonneg _)).trans_lt
      (by simpa using angleRoot_inside hE q)
  rw [he, norm_one] at hn
  exact lt_irrefl _ hn

/-- Formula (1), expressed by its removable rational value. In particular the
statement imposes no exclusion `z_i*z_j ≠ 1`. -/
theorem complete_pair_rational (E : ℂ) (q r : ℝ) :
    canceledPair (anglePoint q) (anglePoint r) (angleRoot E q) (angleRoot E r) =
      -(angleRoot E q*angleRoot E r)/(anglePoint q*anglePoint r) *
        ((anglePoint q-anglePoint r)/(1-angleRoot E q*angleRoot E r))^2 := by
  simp only [canceledPair, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  ring

theorem constrainedAngles_total (σ : Sign) (n : ℕ) (q : Fin n → ℝ) :
    (∑ i, constrainedAngles σ n q i) = signAngle σ := by
  simp only [constrainedAngles, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem particleDensity_energy (σ : Sign) {N : ℕ} (s : ℂ) (q : Fin N → ℝ) :
    particleDensity σ (energy s) q =
      IsingBulk.HT22.Physical.signedAngularDensity (signBool σ) s q := by
  cases σ <;>
    simp only [particleDensity, pairProduct, angleRoot_energy, anglePoint,
      signValue, signBool, IsingBulk.HT22.Physical.signedAngularDensity,
      IsingBulk.HT22.Physical.constraintSign, Bool.false_eq_true, ite_false, ite_true] <;> ring

theorem particleCoefficient_energy (σ : Sign) (N : ℕ) (s : ℂ) :
    particleCoefficient σ N (energy s) =
      IsingBulk.HT22.Physical.signedCoefficient (signBool σ) N s := by
  cases N with
  | zero => simp [particleCoefficient, IsingBulk.HT22.Physical.signedCoefficient]
  | succ n =>
    simp only [particleCoefficient, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
      IsingBulk.HT22.Physical.signedCoefficient_succ,
      IsingBulk.HT22.Physical.signedCoefficientWithAngles]
    congr 2
    funext q
    rw [particleDensity_energy]
    congr 1
    cases σ <;> rfl

/-- Both signs and every positive particle number use exactly N-1 independent
angles and the same factorial as the existing full-lattice coefficient. -/
theorem particleCoefficient_positive_energy (N : ℕ) (s : ℂ) :
    particleCoefficient .positive N (energy s) =
      IsingBulk.HT22.Physical.coefficient N s :=
  particleCoefficient_energy .positive N s

theorem particleCoefficient_negative_energy (N : ℕ) (s : ℂ) :
    particleCoefficient .negative N (energy s) =
      IsingBulk.HT22.Physical.signedCoefficient true N s :=
  particleCoefficient_energy .negative N s

/-- The whole positive odd sum, without a truncation or altered coefficient. -/
theorem fullEnergySum_high_energy (s : ℂ) :
    fullEnergySum .high .positive (energy s) = IsingBulk.HT22.Physical.oddSeries s := by
  apply tsum_congr
  intro n
  exact particleCoefficient_positive_energy (2*n+1) s

theorem energy_inv (s : ℂ) : energy s⁻¹ = energy s := by
  simp only [energy, inv_inv, add_comm]

/-- The concrete coefficient in (3) is the sum over the entire integer lattice
at each real temperature; its origin is included by the cited old theorem. -/
theorem particleCoefficient_eq_fullLattice_tsum {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 1 < t) :
    particleCoefficient .positive N (energy (t : ℂ)) =
      ∑' v : ℤ × ℤ, physicalFullLatticeCoefficient N t v := by
  rw [particleCoefficient_positive_energy]
  exact IsingBulk.HT22.Physical.coefficient_eq_fullLattice_tsum hN ht

/-- The literal site density (2) matches the published physical angular
coefficient, including negative horizontal displacement. -/
theorem siteCoefficient_energy_real (N A : ℕ) (B : ℤ) {t : ℝ} (ht : 1 < t) :
    siteCoefficient N A B (energy (t : ℂ)) = physicalLatticeCoefficient N t A B := by
  unfold siteCoefficient physicalLatticeCoefficient
  congr 2
  funext q
  have hp : pairProduct (energy (t : ℂ)) q = (physicalPairProduct t q : ℂ) := by
    unfold pairProduct
    simp_rw [angleRoot_energy, IsingBulk.HT22.Physical.angularRoot_eq_rightRoot_real ht]
    exact physical_canceledPairProduct ht q
  have hz : (∏ i, angleRoot (energy (t : ℂ)) (q i)) = (physicalZ t q : ℂ) := by
    simp only [angleRoot_energy, IsingBulk.HT22.Physical.angularRoot_real ht,
      physicalZ, Complex.ofReal_prod]
  have hy : (∏ i, anglePoint (q i))^B =
      Complex.exp (Complex.I*(B : ℂ)*(∑ i, (q i : ℂ))) :=
    physical_angle_coordinateProduct_zpow q B
  rw [hp]
  simp only [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_zpow]
  rw [hz, hy]
  simp only [angleRoot_energy, IsingBulk.HT22.Physical.angularRoot_real ht,
    IsingBulk.HT22.Physical.oneBody_physicalRoot t, physicalAngularWeight,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_prod]
  ring

/-- Formula (3) with the site's actual definition, at every real t>1. -/
theorem particleCoefficient_eq_site_tsum {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 1 < t) :
    particleCoefficient .positive N (energy (t : ℂ)) =
      ∑' v : ℤ × ℤ, siteCoefficient N v.1.natAbs v.2 (energy (t : ℂ)) := by
  rw [particleCoefficient_eq_fullLattice_tsum hN ht]
  apply tsum_congr
  intro v
  exact (siteCoefficient_energy_real N v.1.natAbs v.2 ht).symm

end
end IsoProof
