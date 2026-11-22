import IsoProof.IntegralsOneParticle
import IsingBulk.HT22.Physical.Holomorphy
import IsingBulk.First.ExteriorIdentitySymmetry

/-! Holomorphy of every literal site coefficient throughout the physical
energy slit domain, and an identity theorem from its full real ray. -/
namespace IsoProof
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
open IsingBulk.First IsingBulk.Tail
set_option maxHeartbeats 800000

def physicalComplexAngleRoot (E q : ℂ) : ℂ :=
  IsingBulk.Preferred22.physicalRoot (E-Complex.cos q)

def physicalSiteDensity {N : ℕ} (A : ℕ) (B : ℤ) (E : ℂ) (q : Fin N → ℂ) : ℂ :=
  canceledPairProduct (fun i => physicalComplexAngleRoot E (q i))
    (fun i => IsingBulk.HT22.Physical.complexAngle (q i)) *
  ∏ i, (physicalComplexAngleRoot E (q i))^A *
    (IsingBulk.HT22.Physical.complexAngle (q i))^B *
    IsingBulk.HT22.Physical.oneBody (physicalComplexAngleRoot E (q i))

theorem physicalSiteDensity_joint_analyticAt {N : ℕ} (A : ℕ) (B : ℤ)
    (p : ℂ × (Fin N → ℂ))
    (hW : ∀ i, IsingBulk.Preferred22.OffRealSegment (p.1-Complex.cos (p.2 i))) :
    AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => physicalSiteDensity A B x.1 x.2) p := by
  have dq (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dy (i : Fin N) :
      AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => IsingBulk.HT22.Physical.complexAngle (x.2 i)) p :=
    (analyticAt_const.mul (dq i)).cexp
  have dz (i : Fin N) :
      AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => physicalComplexAngleRoot x.1 (x.2 i)) p :=
    (IsingBulk.Preferred22.physicalRoot_analyticAt (hW i)).comp
      (f := fun x : ℂ × (Fin N → ℂ) => x.1-Complex.cos (x.2 i))
      (analyticAt_fst.sub (Complex.analyticAt_cos.comp (dq i)))
  have hy0 (i : Fin N) : IsingBulk.HT22.Physical.complexAngle (p.2 i) ≠ 0 := Complex.exp_ne_zero _
  have hpair (i j : Fin N) :
      1-physicalComplexAngleRoot p.1 (p.2 i)*physicalComplexAngleRoot p.1 (p.2 j) ≠ 0 :=
    one_sub_mul_ne_zero_of_norm_lt_one
      (IsingBulk.Preferred22.physicalRoot_inside (hW i))
      (IsingBulk.Preferred22.physicalRoot_inside (hW j))
  have dpair (i j : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      canceledPair (IsingBulk.HT22.Physical.complexAngle (x.2 i)) (IsingBulk.HT22.Physical.complexAngle (x.2 j))
        (physicalComplexAngleRoot x.1 (x.2 i)) (physicalComplexAngleRoot x.1 (x.2 j))) p :=
    (((((dy i).sub (dy j)).pow 2).neg.mul (dz i)).mul (dz j)).div
      (((dy i).mul (dy j)).mul ((analyticAt_const.sub ((dz i).mul (dz j))).pow 2))
      (mul_ne_zero (mul_ne_zero (hy0 i) (hy0 j)) (pow_ne_zero 2 (hpair i j)))
  have dpairs : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      canceledPairProduct (fun i => physicalComplexAngleRoot x.1 (x.2 i))
        (fun i => IsingBulk.HT22.Physical.complexAngle (x.2 i))) p := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (Finset.univ.filter (fun j => i < j)).analyticAt_fun_prod
    intro j _
    exact dpair i j
  apply dpairs.mul
  apply Finset.univ.analyticAt_fun_prod
  intro i _
  have dbody : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) =>
      IsingBulk.HT22.Physical.oneBody (physicalComplexAngleRoot x.1 (x.2 i))) p := by
    simp_rw [IsingBulk.HT22.Physical.oneBody_eq_rational]
    exact (analyticAt_const.mul (dz i)).div (analyticAt_const.sub ((dz i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  exact (((dz i).pow A).mul ((dy i).zpow (hy0 i))).mul dbody

theorem isOpen_energyDomain : IsOpen energyDomain :=
  (isOpen_ne_fun Complex.continuous_im continuous_const).union
    (isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_re))

theorem physicalComplexAngleRoot_off_segment {E : ℂ} (hE : E ∈ energyDomain) (q : ℝ) :
    IsingBulk.Preferred22.OffRealSegment (E-Complex.cos (q : ℂ)) := by
  obtain ⟨hs,he⟩ := exteriorEnergyInverse_spec hE
  have h := IsingBulk.Preferred22.angularW_off_segment hs q
  change IsingBulk.Preferred22.OffRealSegment
    (energy (exteriorEnergyInverse E)-(Real.cos q : ℂ)) at h
  simpa only [he,Complex.ofReal_cos] using h

theorem physicalSiteDensity_real {N : ℕ} (A : ℕ) (B : ℤ) (E : ℂ) (q : Fin N → ℝ) :
    physicalSiteDensity A B E (fun i => (q i : ℂ)) =
      pairProduct E q * ∏ i, (angleRoot E (q i))^A * (anglePoint (q i))^B *
        IsingBulk.HT22.Physical.oneBody (angleRoot E (q i)) := by
  have hy (r : ℝ) : IsingBulk.HT22.Physical.complexAngle (r : ℂ)=anglePoint r := by
    unfold IsingBulk.HT22.Physical.complexAngle anglePoint limitingAngle
    congr 1
    ring
  simp only [physicalSiteDensity,physicalComplexAngleRoot,← Complex.ofReal_cos,
    angleRoot,pairProduct,hy]

theorem siteCoefficient_analyticAt (N A : ℕ) (B : ℤ) {E : ℂ} (hE : E ∈ energyDomain) :
    AnalyticAt ℂ (siteCoefficient N A B) E := by
  let psi : (Fin N → ℝ) → (Fin N → ℂ) := fun q i => (q i : ℂ)
  have hpsi : Continuous psi := continuous_pi (fun i =>
    Complex.continuous_ofReal.comp (continuous_apply i))
  let F : ℂ × (Fin N → ℂ) → ℂ := fun p => physicalSiteDensity A B p.1 p.2
  have hF : ∀ w ∈ energyDomain, ∀ q ∈ angleBox N, AnalyticAt ℂ F (w,psi q) := by
    intro w hw q _
    exact physicalSiteDensity_joint_analyticAt A B _
      (fun i => physicalComplexAngleRoot_off_segment hw (q i))
  have hcont (w : ℂ) (hw : w ∈ energyDomain) : Continuous (fun q => F (w,psi q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact (physicalSiteDensity_joint_analyticAt A B _
      (fun i => physicalComplexAngleRoot_off_segment hw (q i))).continuousAt.comp
      (f := fun q => (w,psi q)) (continuous_const.prodMk hpsi).continuousAt
  have ha := compact_analytic_shape_integral_analyticAt
    (μ := volume) (K := angleBox N) isCompact_Icc isOpen_energyDomain F psi hpsi
    (fun _ => (1 : ℂ)) continuous_const hF hE
  have hb : AnalyticAt ℂ (fun w => multiAngleIntegral N (fun q => F (w,psi q))) E := by
    apply ha.congr
    filter_upwards [isOpen_energyDomain.mem_nhds hE] with w hw
    simpa only [one_mul] using
      (multiAngleIntegral_eq_box N (fun q => F (w,psi q)) (hcont w hw)).symm
  have he : (fun w => multiAngleIntegral N (fun q => F (w,psi q))) =
      fun w => multiAngleIntegral N (fun q =>
        pairProduct w q * ∏ i, (angleRoot w (q i))^A * (anglePoint (q i))^B *
          IsingBulk.HT22.Physical.oneBody (angleRoot w (q i))) := by
    funext w
    congr 1
    funext q
    exact physicalSiteDensity_real A B w q
  rw [he] at hb
  exact analyticAt_const.mul hb

theorem energy_eq_of_real_temperature {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f energyDomain) (hg : AnalyticOnNhd ℂ g energyDomain)
    (hreal : ∀ t : ℝ, 1 < t → f (energy (t : ℂ))=g (energy (t : ℂ))) :
    EqOn f g energyDomain := by
  have hE {s : ℂ} (hs : 1 < ‖s‖) : AnalyticAt ℂ energy s := by
    have hs0 : s ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hs))
    exact analyticAt_id.add (analyticAt_id.inv hs0)
  have h := exterior_eq_of_real_ray (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun s => f (energy s)) (g := fun s => g (energy s))
    (fun s hs => (hf _ (energy_mem_domain_of_exterior hs)).comp (hE hs))
    (fun s hs => (hg _ (energy_mem_domain_of_exterior hs)).comp (hE hs)) hreal
  intro E hED
  obtain ⟨hs,he⟩ := exteriorEnergyInverse_spec hED
  simpa only [he] using h hs

end
end IsoProof
