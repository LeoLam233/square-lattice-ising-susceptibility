import IsoProof.IntegralsSiteBoundary

/-! A fixed protected graph at one reference energy identifies the actual
site function throughout any connected protected upper domain.  No new
homotopy is required as the real part of the energy varies. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology

/-- Analytic continuation of the already proved actual seed germ. -/
theorem graphSiteCoefficient_eq_site_on_preconnected_upper
    {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi) (v c : ℝ)
    (N A : ℕ) (B : ℤ) {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hupper : ∀ E∈U, 0 < E.im)
    (hD : ∀ E∈U, ∀ r∈Icc (-Real.pi) Real.pi,
      E-Complex.cos (scalarGraph b v r c) ∈ contourRootDomain)
    {E₀ : ℂ} (hE₀ : E₀∈U)
    (hseed : GermEqAt E₀ (siteCoefficient N A B) (graphSiteCoefficient b v c N A B)) :
    EqOn (graphSiteCoefficient b v c N A B) (siteCoefficient N A B) U := by
  have hf : AnalyticOnNhd ℂ (siteCoefficient N A B) U :=
    fun E hE => siteCoefficient_analyticAt N A B (Or.inl (hupper E hE).ne')
  exact (hf.eqOn_of_preconnected_of_eventuallyEq
    (graphSiteCoefficient_analyticOn hb hbpi v c N A B hU hD) hconn hE₀ hseed).symm

/-- The seed is constructed from the actual Stokes theorem at x₀+i y₀.
The remaining domain premise is pointwise protection of the same fixed
contour, and is supplied by the quantitative fixed-graph producer. -/
theorem common_graph_site_identity_on_upper_domain {x₀ d : ℝ}
    (hx : 0 < x₀) (hx2 : x₀ < 2) (hd : 0 ≤ d) (hdb : d < cutHalfWidth x₀) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε → ∀ c∈Icc (-d) d,
      ∀ U : Set ℂ, IsOpen U → IsPreconnected U →
      (∀ E∈U, 0 < E.im) →
      (∀ E∈U, ∀ r∈Icc (-Real.pi) Real.pi,
        E-Complex.cos (scalarGraph (cutHalfWidth x₀) v r c) ∈ contourRootDomain) →
      ∀ y₀ : ℝ, 0 < y₀ → (x₀:ℂ)+Complex.I*(y₀:ℂ)∈U →
      ∀ (N A : ℕ) (B : ℤ),
        EqOn (graphSiteCoefficient (cutHalfWidth x₀) v c N A B) (siteCoefficient N A B) U := by
  obtain ⟨ε,hε,hseed⟩ := common_graph_site_germ hx hx2 hd hdb
  refine ⟨ε,hε,?_⟩
  intro v hv hvε c hc U hU hconn hupper hD y₀ hy₀ hE₀ N A B
  exact graphSiteCoefficient_eq_site_on_preconnected_upper
    (cutHalfWidth_range hx hx2).1 (cutHalfWidth_range hx hx2).2 v c N A B
    hU hconn hupper hD hE₀ (hseed v hv hvε c hc y₀ hy₀ N A B)

/-- An open upper rectangle with a reference real center. -/
def siteUpperRectangle (x₀ ρ Y : ℝ) : Set ℂ :=
  {E : ℂ | x₀-ρ < E.re} ∩ {E : ℂ | E.re < x₀+ρ} ∩
    {E : ℂ | 0 < E.im} ∩ {E : ℂ | E.im < Y}

theorem siteUpperRectangle_isOpen (x₀ ρ Y : ℝ) : IsOpen (siteUpperRectangle x₀ ρ Y) :=
  (((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).inter
      (isOpen_lt continuous_const Complex.continuous_im)).inter
        (isOpen_lt Complex.continuous_im continuous_const)

theorem siteUpperRectangle_isPreconnected (x₀ ρ Y : ℝ) :
    IsPreconnected (siteUpperRectangle x₀ ρ Y) :=
  ((((convex_halfSpace_re_gt (x₀-ρ)).inter (convex_halfSpace_re_lt (x₀+ρ))).inter
    (convex_halfSpace_im_gt 0)).inter (convex_halfSpace_im_lt Y)).isPreconnected

/-- Actual graph/site identity on an upper rectangle, with the vertical
seed chosen internally at half its height. -/
theorem common_graph_site_identity_on_upper_rectangle {x₀ d : ℝ}
    (hx : 0 < x₀) (hx2 : x₀ < 2) (hd : 0 ≤ d) (hdb : d < cutHalfWidth x₀) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε → ∀ c∈Icc (-d) d,
      ∀ ρ Y : ℝ, 0 < ρ → 0 < Y →
      (∀ E∈siteUpperRectangle x₀ ρ Y, ∀ r∈Icc (-Real.pi) Real.pi,
        E-Complex.cos (scalarGraph (cutHalfWidth x₀) v r c) ∈ contourRootDomain) →
      ∀ (N A : ℕ) (B : ℤ),
        EqOn (graphSiteCoefficient (cutHalfWidth x₀) v c N A B)
          (siteCoefficient N A B) (siteUpperRectangle x₀ ρ Y) := by
  obtain ⟨ε,hε,hEq⟩ := common_graph_site_identity_on_upper_domain hx hx2 hd hdb
  refine ⟨ε,hε,?_⟩
  intro v hv hvε c hc ρ Y hρ hY hD N A B
  apply hEq v hv hvε c hc (siteUpperRectangle x₀ ρ Y)
    (siteUpperRectangle_isOpen x₀ ρ Y) (siteUpperRectangle_isPreconnected x₀ ρ Y)
    (fun _ hE => hE.1.2) hD (Y/2) (by positivity) _ N A B
  simp only [siteUpperRectangle,mem_inter_iff,mem_ofPred_eq,Complex.add_re,
    Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,
    Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,Complex.add_im,
    Complex.mul_im,one_mul,zero_add]
  exact ⟨⟨⟨by linarith,by linarith⟩,by linarith⟩,by linarith⟩

end
end IsoProof
