import IsoProof.SiteSymmetry
import IsingBulk.Preferred22.KernelBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Compact interior spatial summability, with the actual two-coordinate
site coefficient.  These estimates are used for analytic identification
of the site sum; the sharper boundary tail estimate is separate. -/
namespace IsoProof
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
set_option maxHeartbeats 800000

theorem energy_sub_real_off_segment {E : ℂ} (hE : E ∈ energyDomain)
    {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    IsingBulk.Preferred22.OffRealSegment (E-(c : ℂ)) := by
  simpa only [← Complex.ofReal_cos,Real.cos_arccos hc.1 hc.2] using
    physicalComplexAngleRoot_off_segment hE (Real.arccos c)

theorem compact_angleRoot_bound {K : Set ℂ} (hK : IsCompact K)
    (hD : K ⊆ energyDomain) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ E ∈ K, ∀ r : ℝ, ‖angleRoot E r‖ ≤ q := by
  by_cases hne : K.Nonempty
  · let F : ℂ × ℝ → ℂ := fun p => IsingBulk.Preferred22.physicalRoot (p.1-(p.2 : ℂ))
    have hc : ContinuousOn F (K ×ˢ Icc (-1 : ℝ) 1) := by
      intro p hp
      exact ((IsingBulk.Preferred22.physicalRoot_analyticAt
        (energy_sub_real_off_segment (hD hp.1) hp.2)).continuousAt.comp
        (f := fun p : ℂ × ℝ => p.1-(p.2 : ℂ))
        (continuous_fst.sub (Complex.continuous_ofReal.comp continuous_snd)).continuousAt).continuousWithinAt
    obtain ⟨p,hp,hmax⟩ := (hK.prod isCompact_Icc).exists_isMaxOn
      (hne.prod ⟨0,by norm_num⟩) hc.norm
    have hp1 : ‖F p‖ < 1 := IsingBulk.Preferred22.physicalRoot_inside
      (energy_sub_real_off_segment (hD hp.1) hp.2)
    refine ⟨(‖F p‖+1)/2,by nlinarith [norm_nonneg (F p)],by linarith,?_⟩
    intro E hE r
    have hb : ‖F (E,Real.cos r)‖ ≤ ‖F p‖ :=
      hmax ⟨hE,Real.neg_one_le_cos r,Real.cos_le_one r⟩
    change ‖angleRoot E r‖ ≤ ‖F p‖ at hb
    linarith
  · exact ⟨1/2,by norm_num,by norm_num,fun _ h => (hne ⟨_,h⟩).elim⟩

theorem physicalSiteDensity_real_continuous (N A : ℕ) (B : ℤ)
    {E : ℂ} (hE : E ∈ energyDomain) :
    Continuous (fun q : Fin N → ℝ => physicalSiteDensity A B E (fun i => (q i : ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact (physicalSiteDensity_joint_analyticAt A B _
    (fun i => physicalComplexAngleRoot_off_segment hE (q i))).continuousAt.comp
    (f := fun q : Fin N → ℝ => (E,fun i => (q i : ℂ)))
    (continuous_const.prodMk (continuous_pi (fun i =>
      Complex.continuous_ofReal.comp (continuous_apply i)))).continuousAt

theorem siteCoefficient_eq_box (N A : ℕ) (B : ℤ)
    {E : ℂ} (hE : E ∈ energyDomain) :
    siteCoefficient N A B E =
      (N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N *
        ∫ q in angleBox N, physicalSiteDensity A B E (fun i => (q i : ℂ)) := by
  rw [← multiAngleIntegral_eq_box N _ (physicalSiteDensity_real_continuous N A B hE)]
  unfold siteCoefficient
  congr 2
  funext q
  exact (physicalSiteDensity_real A B E q).symm

theorem siteDensity_norm_displacement {N : ℕ} (A : ℕ) (B : ℤ)
    (E : ℂ) (q : Fin N → ℝ) :
    ‖physicalSiteDensity A B E (fun i => (q i : ℂ))‖ =
      ‖physicalSiteDensity 0 0 E (fun i => (q i : ℂ))‖ *
        ‖∏ i, angleRoot E (q i)‖^A := by
  have he : physicalSiteDensity A B E (fun i => (q i : ℂ)) =
      physicalSiteDensity 0 0 E (fun i => (q i : ℂ)) *
        (∏ i, angleRoot E (q i))^A * (∏ i, anglePoint (q i))^B := by
    rw [physicalSiteDensity_real,physicalSiteDensity_real]
    simp only [pow_zero,zpow_zero,one_mul,Finset.prod_mul_distrib,
      Finset.prod_pow,Finset.prod_zpow]
    ring
  have hy : ‖∏ i, anglePoint (q i)‖ = 1 := by
    simp only [norm_prod,anglePoint,limitingAngle_norm,Finset.prod_const_one]
  rw [he,norm_mul,norm_mul,norm_pow,norm_zpow,hy,one_zpow,mul_one]

theorem compact_site_amplitude_bound (N : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hD : K ⊆ energyDomain) :
    ∃ M > 0, ∀ E ∈ K, ∀ q ∈ angleBox N,
      ‖physicalSiteDensity 0 0 E (fun i => (q i : ℂ))‖ ≤ M := by
  have hc : ContinuousOn (fun p : ℂ × (Fin N → ℝ) =>
      physicalSiteDensity 0 0 p.1 (fun i => (p.2 i : ℂ))) (K ×ˢ angleBox N) := by
    intro p hp
    exact (physicalSiteDensity_joint_analyticAt 0 0 _
      (fun i => physicalComplexAngleRoot_off_segment (hD hp.1) (p.2 i))).continuousAt.comp
      (f := fun p : ℂ × (Fin N → ℝ) => (p.1,fun i => (p.2 i : ℂ)))
      (continuous_fst.prodMk (continuous_pi (fun i =>
        Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd)))).continuousAt
      |>.continuousWithinAt
  obtain ⟨M,hM⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨|M|+1,by positivity,?_⟩
  intro E hE q hq
  exact (hM (E,q) ⟨hE,hq⟩).trans (by linarith [le_abs_self M])

theorem siteCoefficient_norm_le_geometric {N : ℕ} (hN : 0 < N) (A : ℕ) (B : ℤ)
    {E : ℂ} (hE : E ∈ energyDomain) {q M : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hM : 0 ≤ M) (hz : ∀ r : ℝ, ‖angleRoot E r‖ ≤ q)
    (hamp : ∀ r ∈ angleBox N,
      ‖physicalSiteDensity 0 0 E (fun i => (r i : ℂ))‖ ≤ M) :
    ‖siteCoefficient N A B E‖ ≤
      (‖(N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N‖ *
        (M*volume.real (angleBox N))) * q^A := by
  have hb (r) (hr : r ∈ angleBox N) :
      ‖physicalSiteDensity A B E (fun i => (r i : ℂ))‖ ≤ M*q^A := by
    rw [siteDensity_norm_displacement]
    exact mul_le_mul (hamp r hr)
      (pow_le_pow_left₀ (norm_nonneg _)
        (IsingBulk.Preferred22.product_norm_le_q hN hq hq1 _ (fun i => hz (r i))) A)
      (by positivity) hM
  have hi : ‖∫ r in angleBox N, physicalSiteDensity A B E (fun i => (r i : ℂ))‖ ≤
      (M*q^A)*volume.real (angleBox N) := by
    apply norm_setIntegral_le_of_norm_le_const_ae isCompact_Icc.measure_lt_top
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hb r hr
  rw [siteCoefficient_eq_box N A B hE,norm_mul]
  exact (mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans_eq (by ring)

theorem square_geometric_le_product {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (a b : ℕ) :
    q^(max a b) ≤ (Real.sqrt q)^a*(Real.sqrt q)^b := by
  have hs : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1
  calc
    _ = (Real.sqrt q)^(2*max a b) := by rw [pow_mul,Real.sq_sqrt hq]
    _ ≤ (Real.sqrt q)^(a+b) :=
      pow_le_pow_of_le_one (Real.sqrt_nonneg q) hs (by omega)
    _ = _ := pow_add _ _ _

/-- A compact energy set has an absolutely summable two-coordinate majorant
for every fixed positive particle number.  This is a proof about the literal
site coefficient and is independent of the future boundary estimate. -/
theorem compact_site_geometric_bound (N : ℕ) (hN : 0 < N)
    {K : Set ℂ} (hK : IsCompact K) (hD : K ⊆ energyDomain) :
    ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧ ∀ E ∈ K, ∀ p : ℤ × ℤ,
      ‖siteCoefficient N p.1.natAbs p.2 E‖ ≤ C*(q^p.1.natAbs*q^p.2.natAbs) := by
  obtain ⟨q,hq,hq1,hroot⟩ := compact_angleRoot_bound hK hD
  obtain ⟨M,hM,hamp⟩ := compact_site_amplitude_bound N hK hD
  let C : ℝ := ‖(N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N‖ *
    (M*volume.real (angleBox N))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,Real.sqrt q,by linarith,Real.sqrt_pos.mpr hq,
    (by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hq.le hq1),?_⟩
  intro E hE p
  rw [siteCoefficient_square_sector N hN p (hD hE)]
  have hb := siteCoefficient_norm_le_geometric hN
    (max p.1.natAbs p.2.natAbs) ((min p.1.natAbs p.2.natAbs : ℕ) : ℤ)
    (hD hE) hq.le hq1 hM.le (hroot E hE) (hamp E hE)
  apply hb.trans
  exact (mul_le_mul_of_nonneg_left (square_geometric_le_product hq.le hq1.le _ _) hC).trans
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end
end IsoProof
