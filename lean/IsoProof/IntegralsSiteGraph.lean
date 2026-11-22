import IsoProof.IntegralsGraphTensor
import IsingBulk.Preferred22.HorizontalFourier

/-! Complete original N-angle site coefficient equals the actual common
graph integral. The theorem is both-parity and has no contour-equality,
analyticity, pole-gap, or domination premise supplied externally. -/
namespace IsoProof
noncomputable section
open Set MeasureTheory
open scoped BigOperators

/-- The fixed common-graph analytic continuation, with the original
factorial and angular normalization. -/
def graphSiteCoefficient (b v c : ℝ) (N A : ℕ) (B : ℤ) (E : ℂ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N *
    protectedGraphMultiIntegral b v c N (continuedSiteDensity A B E)

theorem continuedSiteDensity_real_continuous {N : ℕ} (A : ℕ) (B : ℤ)
    {E : ℂ} (hE : 0 < E.im) :
    Continuous (fun q : Fin N → ℝ => continuedSiteDensity A B E (fun i => (q i : ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hW (i : Fin N) : E-Complex.cos (q i : ℂ) ∈ contourRootDomain := by
    apply upper_all_mem_contourRootDomain
    simpa only [← Complex.ofReal_cos, Complex.sub_im, Complex.ofReal_im, sub_zero] using hE
  exact (continuedSiteDensity_analyticAt A B E _ hW).continuousAt.comp
    (continuous_pi (fun i => Complex.continuous_ofReal.comp (continuous_apply i))).continuousAt

theorem continuedSiteDensity_real_periodic {N : ℕ} (A : ℕ) (B : ℤ) (E : ℂ) :
    IsingBulk.First.CoordinatePeriodic N
      (fun q : Fin N → ℝ => continuedSiteDensity A B E (fun i => (q i : ℂ))) := by
  intro q i
  have hu : (fun j => (Function.update q i (q i+2*Real.pi) j : ℂ)) =
      Function.update (fun j => (q j : ℂ)) i ((q i : ℂ)+2*(Real.pi : ℂ)) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp
    · simp [Function.update_of_ne hj]
  dsimp only
  rw [hu]
  exact continuedSiteDensity_coordinate_periodic A B E (fun j => (q j : ℂ)) i

set_option backward.isDefEq.respectTransparency false in
theorem siteCoefficient_eq_realAngleBox (N A : ℕ) (B : ℤ) {E : ℂ} (hE : 0 < E.im) :
    siteCoefficient N A B E =
      (N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N *
        ∫ q in realAngleBox N, continuedSiteDensity A B E (fun i => (q i : ℂ)) := by
  unfold siteCoefficient
  congr 1
  have he : (fun q : Fin N → ℝ => pairProduct E q *
      ∏ i, (angleRoot E (q i))^A * (anglePoint (q i))^B *
        IsingBulk.HT22.Physical.oneBody (angleRoot E (q i))) =
      fun q => continuedSiteDensity A B E (fun i => (q i : ℂ)) := by
    funext q
    exact (continuedSiteDensity_real A B hE q).symm
  rw [he]
  have hbox : IsingBulk.Preferred22.angularBox N =ᵐ[volume] realAngleBox N := by
    change (Set.pi Set.univ (fun _ : Fin N => Ioc (-Real.pi) Real.pi)) =ᵐ[volume]
      Icc (fun _ => -Real.pi) (fun _ => Real.pi)
    rw [← Set.pi_univ_Icc]
    exact Measure.pi_Ioc_ae_eq_pi_Icc
  exact (IsingBulk.Preferred22.angularBox_integral_eq_multiAngleIntegral (N := N) _
    (continuedSiteDensity_real_continuous A B hE)
    (continuedSiteDensity_real_periodic A B E)).symm.trans (setIntegral_congr_set hbox)

/-- Actual both-parity, full N-dimensional graph deformation, with the
literal factorial and angular normalization from formula (1). -/
theorem common_graph_site_transport {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε →
      ∀ c ∈ Icc (-d) d, ∀ y : ℝ, 0 < y →
        ∀ (N A : ℕ) (B : ℤ),
          siteCoefficient N A B ((x : ℂ)+Complex.I*(y : ℂ)) =
            (N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N *
              protectedGraphMultiIntegral (cutHalfWidth x) v c N
                (continuedSiteDensity A B ((x : ℂ)+Complex.I*(y : ℂ))) := by
  obtain ⟨ε,hε,hD⟩ := common_graph_homotopy_domain hx hx2 hd hdb
  refine ⟨ε,hε,?_⟩
  intro v hv hvε c hc y hy N A B
  rw [siteCoefficient_eq_realAngleBox N A B (by simpa using hy)]
  congr 1
  apply realAngleBox_eq_protectedGraphMultiIntegral N
    (cutHalfWidth_range hx hx2).1 (cutHalfWidth_range hx hx2).2 hv.le
  · intro q hq
    apply continuedSiteDensity_analyticAt
    intro i
    obtain ⟨t,ht,r,hr,he⟩ := hq i
    rw [he]
    exact hD v hv hvε c hc y hy t ht r hr
  · exact continuedSiteDensity_coordinate_periodic A B _

end
end IsoProof
