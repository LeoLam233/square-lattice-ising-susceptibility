import IsoProof.IntegralsGraphAnalytic
import IsoProof.ContourBounds
import IsoProof.SiteAnalytic

/-! Fixed-graph local analytic continuations of the actual site function.
The physical-root formula is compared by a proved upper-half-plane germ
identity; it is not differentiated across its branch cut. -/
namespace IsoProof
noncomputable section
open Set Filter Metric
open scoped Topology

theorem scalarGraph_continuous {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi) (v c : ℝ) :
    Continuous (fun r : ℝ => scalarGraph b v r c) := by
  have hf := contourDisplacement_continuous hb.le hbpi
  exact Complex.continuous_ofReal.add
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul (hf.sub continuous_const))))

theorem scalarGraph_homotopy_continuous {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi) (c : ℝ) :
    Continuous (fun p : ℝ × ℝ => scalarGraph b p.1 p.2 c) := by
  have hf := contourDisplacement_continuous hb.le hbpi
  exact (Complex.continuous_ofReal.comp continuous_snd).add
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_fst.mul ((hf.comp continuous_snd).sub continuous_const))))

theorem graphSiteCoefficient_analyticOn {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (v c : ℝ) (N A : ℕ) (B : ℤ) {U : Set ℂ} (hU : IsOpen U)
    (hD : ∀ E∈U, ∀ r∈Icc (-Real.pi) Real.pi,
      E-Complex.cos (scalarGraph b v r c) ∈ contourRootDomain) :
    AnalyticOnNhd ℂ (graphSiteCoefficient b v c N A B) U := by
  have ha := protectedGraphMultiIntegral_analyticOnNhd N hb hbpi v c hU
    (fun p : ℂ × (Fin N → ℂ) => continuedSiteDensity A B p.1 p.2) (by
      intro E hE q hq
      exact continuedSiteDensity_joint_analyticAt A B _
        (fun i => hD E hE (q i) ⟨hq.1 i,hq.2 i⟩))
  intro E hE
  exact analyticAt_const.mul (ha E hE)

/-- Pointwise domain protection on the complete compact graph constructs
its own open E-neighborhood, even when E is on the real cut. -/
theorem graphSiteCoefficient_analyticAt {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (v c : ℝ) (N A : ℕ) (B : ℤ) (E : ℂ)
    (hD : ∀ r∈Icc (-Real.pi) Real.pi,
      E-Complex.cos (scalarGraph b v r c) ∈ contourRootDomain) :
    AnalyticAt ℂ (graphSiteCoefficient b v c N A B) E := by
  have hW : Continuous (fun r : ℝ => E-Complex.cos (scalarGraph b v r c)) :=
    continuous_const.sub (Complex.continuous_cos.comp (scalarGraph_continuous hb hbpi v c))
  obtain ⟨δ,hδ,hδD⟩ := compact_dispersion_energy_disk isCompact_Icc _ hW hD
  apply graphSiteCoefficient_analyticOn hb hbpi v c N A B isOpen_ball _ E (Metric.mem_ball_self hδ)
  intro E' hE' r hr
  have h := hδD (E'-E) (by simpa only [Metric.mem_ball,dist_eq_norm] using hE') r hr
  convert h using 1
  ring

/-- Complete finite-dimensional transport for any legal actual homotopy. -/
theorem siteCoefficient_eq_graph_of_homotopy_domain {b v c : ℝ}
    (hb : 0 < b) (hbpi : b < Real.pi) (hv : 0 ≤ v)
    (N A : ℕ) (B : ℤ) {E : ℂ} (hE : 0 < E.im)
    (hD : ∀ t∈Icc 0 v, ∀ r∈Icc (-Real.pi) Real.pi,
      E-Complex.cos (scalarGraph b t r c) ∈ contourRootDomain) :
    siteCoefficient N A B E = graphSiteCoefficient b v c N A B E := by
  rw [siteCoefficient_eq_realAngleBox N A B hE]
  unfold graphSiteCoefficient
  congr 1
  apply realAngleBox_eq_protectedGraphMultiIntegral N hb hbpi hv
  · intro q hq
    apply continuedSiteDensity_analyticAt
    intro i
    obtain ⟨t,ht,r,hr,he⟩ := hq i
    rw [he]
    exact hD t ht r hr
  · exact continuedSiteDensity_coordinate_periodic A B E

/-- Equality of actual germs, not only equality along one vertical ray.
Compactness protects every mixed homotopy point under a complex E shift. -/
theorem siteCoefficient_graph_germ_of_homotopy_domain {b v c : ℝ}
    (hb : 0 < b) (hbpi : b < Real.pi) (hv : 0 ≤ v)
    (N A : ℕ) (B : ℤ) {E : ℂ} (hE : 0 < E.im)
    (hD : ∀ t∈Icc 0 v, ∀ r∈Icc (-Real.pi) Real.pi,
      E-Complex.cos (scalarGraph b t r c) ∈ contourRootDomain) :
    GermEqAt E (siteCoefficient N A B) (graphSiteCoefficient b v c N A B) := by
  let K : Set (ℝ × ℝ) := Icc 0 v ×ˢ Icc (-Real.pi) Real.pi
  have hW : Continuous (fun p : ℝ × ℝ => E-Complex.cos (scalarGraph b p.1 p.2 c)) :=
    continuous_const.sub (Complex.continuous_cos.comp (scalarGraph_homotopy_continuous hb hbpi c))
  obtain ⟨δ,hδ,hδD⟩ := compact_dispersion_energy_disk (isCompact_Icc.prod isCompact_Icc)
    _ hW (show ∀ p∈K, E-Complex.cos (scalarGraph b p.1 p.2 c) ∈ contourRootDomain from
      fun p hp => hD p.1 hp.1 p.2 hp.2)
  have hu : ∀ᶠ z : ℂ in 𝓝 E, 0 < z.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hE
  filter_upwards [Metric.ball_mem_nhds E hδ,hu] with z hz hzi
  apply siteCoefficient_eq_graph_of_homotopy_domain hb hbpi hv N A B hzi
  intro t ht r hr
  have h := hδD (z-E) (by simpa only [Metric.mem_ball,dist_eq_norm] using hz) (t,r) ⟨ht,hr⟩
  convert h using 1
  ring

theorem common_graph_site_germ {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε →
      ∀ c∈Icc (-d) d, ∀ y : ℝ, 0 < y → ∀ (N A : ℕ) (B : ℤ),
        GermEqAt ((x : ℂ)+Complex.I*(y : ℂ)) (siteCoefficient N A B)
          (graphSiteCoefficient (cutHalfWidth x) v c N A B) := by
  obtain ⟨ε,hε,hD⟩ := common_graph_homotopy_domain hx hx2 hd hdb
  refine ⟨ε,hε,?_⟩
  intro v hv hvε c hc y hy N A B
  exact siteCoefficient_graph_germ_of_homotopy_domain
    (cutHalfWidth_range hx hx2).1 (cutHalfWidth_range hx hx2).2 hv.le N A B
    (by simpa using hy) (hD v hv hvε c hc y hy)

end
end IsoProof
