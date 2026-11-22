import IsoProof.IntegralsSiteContinuation
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros
import IsingBulk.First.DominatedAnalyticIntegral

/-! Actual site-by-site analytic extensions through every real interior
energy, obtained from one fixed protected graph. -/
namespace IsoProof
noncomputable section
open Set Filter Metric
open scoped Topology

/-- One common graph works for every N,A,B and for every center in the
compact interval. The identity holds on a full upper half disk. -/
theorem common_graph_site_analytic_extension {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε → ∃ ρ > 0,
      ∀ c∈Icc (-d) d, ∀ (N A : ℕ) (B : ℤ),
        AnalyticOnNhd ℂ (graphSiteCoefficient (cutHalfWidth x) v c N A B) (ball (x : ℂ) ρ) ∧
        EqOn (siteCoefficient N A B) (graphSiteCoefficient (cutHalfWidth x) v c N A B)
          (ball (x : ℂ) ρ ∩ {E : ℂ | 0 < E.im}) := by
  obtain ⟨ε₁,hε₁,hscalar⟩ := common_graph_scalar_bounds hx hx2 hd hdb
  obtain ⟨ε₂,hε₂,hgerm⟩ := common_graph_site_germ hx hx2 hd hdb
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro v hv hvε
  obtain ⟨ρ,hρ,M,_hM,δ,_hδ,hD,_bounds⟩ := hscalar v hv (hvε.trans_le (min_le_left _ _))
  refine ⟨ρ,hρ,?_⟩
  intro c hc N A B
  have hdomain (E : ℂ) (hE : E∈ball (x : ℂ) ρ)
      (r : ℝ) (hr : r∈Icc (-Real.pi) Real.pi) :
      E-Complex.cos (scalarGraph (cutHalfWidth x) v r c) ∈ contourRootDomain := by
    have he : E-(x : ℂ) ∈ closedBall (0 : ℂ) ρ := by
      simpa only [mem_closedBall,dist_zero_right] using
        (show ‖E-(x : ℂ)‖ ≤ ρ from (show ‖E-(x : ℂ)‖ < ρ from
          by simpa only [mem_ball,dist_eq_norm] using hE).le)
    have ht : (E-(x : ℂ),(0 : ℝ),(r,c)) ∈
        closedBall (0 : ℂ) ρ ×ˢ commonGraphBox d :=
      ⟨he,⟨⟨le_rfl,zero_le_one⟩,hr,hc⟩⟩
    have hh := hD _ ht
    simpa only [commonGraphEnergy,commonGraphAngle,Complex.ofReal_zero,mul_zero,
      add_zero,add_sub_cancel] using hh
  have ha := graphSiteCoefficient_analyticOn (cutHalfWidth_range hx hx2).1
    (cutHalfWidth_range hx hx2).2 v c N A B isOpen_ball hdomain
  refine ⟨ha,?_⟩
  let D : Set ℂ := ball (x : ℂ) ρ ∩ {E : ℂ | 0 < E.im}
  have hf : AnalyticOnNhd ℂ (siteCoefficient N A B) D :=
    fun E hE => siteCoefficient_analyticAt N A B (Or.inl hE.2.ne')
  have hconn : IsPreconnected D :=
    ((convex_ball (x : ℂ) ρ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  let z₀ : ℂ := (x : ℂ)+Complex.I*((ρ/2 : ℝ) : ℂ)
  have hy : 0 < ρ/2 := by positivity
  have hz₀ : z₀∈D := by
    constructor
    · rw [mem_ball,dist_eq_norm]
      change ‖((x : ℂ)+Complex.I*((ρ/2 : ℝ) : ℂ))-(x : ℂ)‖ < ρ
      rw [add_sub_cancel_left,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos hy]
      linarith
    · change 0 < z₀.im
      simpa only [z₀,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
        Complex.I_re,Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add] using hy
  exact hf.eqOn_of_preconnected_of_eventuallyEq (ha.mono inter_subset_left) hconn hz₀
    (hgerm v hv (hvε.trans_le (min_le_right _ _)) c hc (ρ/2) hy N A B)

/-- The boundary jet is the derivative of the fixed analytic graph
extension. It is not the derivative of a reset physical-root formula on
the real cut. -/
theorem site_upperJetTrace_of_local_extension (N A : ℕ) (B : ℤ) (j : ℕ)
    (x ρ : ℝ) (hρ : 0 < ρ) (G : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G (ball (x : ℂ) ρ))
    (hEq : EqOn (siteCoefficient N A B) G (ball (x : ℂ) ρ ∩ {E : ℂ | 0 < E.im})) :
    UpperJetTrace (siteCoefficient N A B) j x (iteratedDeriv j G (x : ℂ)) := by
  have hEqJet : ∀ E∈ball (x : ℂ) ρ ∩ {E : ℂ | 0 < E.im},
      iteratedDeriv j (siteCoefficient N A B) E=iteratedDeriv j G E := by
    intro E hE
    have hnb : ball (x : ℂ) ρ ∩ {E : ℂ | 0 < E.im} ∈ 𝓝 E :=
      (isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)).mem_nhds hE
    have he : siteCoefficient N A B =ᶠ[𝓝 E] G := Filter.Eventually.mono hnb (fun z hz => hEq hz)
    exact he.iteratedDeriv_eq j
  have he : (fun E => iteratedDeriv j (siteCoefficient N A B) E) =ᶠ[
      𝓝[{E : ℂ | 0 < E.im}] (x : ℂ)] iteratedDeriv j G := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (x : ℂ) hρ)] with E hE hball
    exact hEqJet E ⟨hball,hE⟩
  have hc := (IsingBulk.First.analyticAt_iteratedDeriv
    (hG (x : ℂ) (mem_ball_self hρ)) j).continuousAt
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm

theorem site_upperJetTrace_exists {x : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (N A : ℕ) (B : ℤ) (j : ℕ) :
    ∃ L : ℂ, UpperJetTrace (siteCoefficient N A B) j x L := by
  obtain ⟨ε,hε,hgraph⟩ := common_graph_site_analytic_extension hx hx2 (by norm_num : (0 : ℝ) ≤ 0)
    (cutHalfWidth_range hx hx2).1
  obtain ⟨ρ,hρ,hsite⟩ := hgraph (ε/2) (by positivity) (by linarith)
  obtain ⟨ha,he⟩ := hsite 0 (by simp) N A B
  exact ⟨_,site_upperJetTrace_of_local_extension N A B j x ρ hρ _ ha he⟩

end
end IsoProof
