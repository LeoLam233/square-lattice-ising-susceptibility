import IsoProof.IntegralsGraphContour
import IsoProof.IntegralsGraphDensity

/-! One-coordinate transport of the actual site integrand. The root-domain
producer is the short manuscript's protected graph, including the t=0 cap. -/
namespace IsoProof
noncomputable section
open Set

set_option backward.isDefEq.respectTransparency false in
theorem continuedSiteDensity_coordinate_transport {N : ℕ} (A : ℕ) (B : ℤ)
    (E : ℂ) (q : Fin N → ℂ) (i : Fin N) {b v c : ℝ}
    (hb : 0 < b) (hbpi : b < Real.pi) (hv : 0 ≤ v)
    (hother : ∀ j, j ≠ i → E-Complex.cos (q j) ∈ contourRootDomain)
    (hgraph : ∀ t∈Icc 0 v, ∀ r∈Icc (-Real.pi) Real.pi,
      E-Complex.cos (scalarGraph b t r c) ∈ contourRootDomain) :
    protectedGraphIntegral
      (fun z => continuedSiteDensity A B E (Function.update q i z)) b v c =
      ∫ r : ℝ in (-Real.pi)..Real.pi,
        continuedSiteDensity A B E (Function.update q i (r : ℂ)) := by
  apply protectedGraphIntegral_eq_real hb hbpi hv
  · intro z
    simpa only [Function.update_self, Function.update_idem] using
      continuedSiteDensity_coordinate_periodic A B E (Function.update q i z) i
  · intro t ht r hr
    have hW : ∀ j, E-Complex.cos (Function.update q i (scalarGraph b t r c) j) ∈
        contourRootDomain := by
      intro j
      by_cases hj : j=i
      · subst j
        simpa only [Function.update_self] using hgraph t ht r hr
      · simpa only [Function.update_of_ne hj] using hother j hj
    have hu : AnalyticAt ℂ (fun z : ℂ => Function.update q i z) (scalarGraph b t r c) := by
      apply analyticAt_pi_iff.mpr
      intro j
      by_cases hj : j=i
      · subst j
        simp only [Function.update_self]
        convert (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) (scalarGraph b t r c)) using 1
        rfl
      · simpa only [Function.update_of_ne hj] using
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => q j) (scalarGraph b t r c))
    exact ((continuedSiteDensity_analyticAt A B E _ hW).comp
      (f := fun z : ℂ => Function.update q i z) hu).differentiableAt

/-- The complete homotopy, including its undeformed endpoint, stays on the
same analytic sheet for upper-half-plane energy. -/
theorem common_graph_homotopy_domain {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε →
      ∀ c ∈ Icc (-d) d, ∀ y : ℝ, 0 < y →
        ∀ t∈Icc 0 v, ∀ r∈Icc (-Real.pi) Real.pi,
          ((x : ℂ)+Complex.I*(y : ℂ))-Complex.cos
            (scalarGraph (cutHalfWidth x) t r c) ∈ contourRootDomain := by
  obtain ⟨ε,hε,hD⟩ := common_graph_domain hx hx2 hd hdb
  refine ⟨ε,hε,?_⟩
  intro v _ hv c hc y hy t ht r hr
  by_cases ht0 : t=0
  · subst t
    apply upper_all_mem_contourRootDomain
    simpa [scalarGraph, ← Complex.ofReal_cos] using hy
  · exact hD t (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (ht.2.trans_lt hv) r hr c hc y hy.le

/-- No contour legality premise remains here: it is produced for the actual
common graph. Other coordinates may already be anywhere on the coherent
root domain, enabling subsequent finite-dimensional Fubini transport. -/
theorem common_graph_site_coordinate_transport {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε →
      ∀ c ∈ Icc (-d) d, ∀ y : ℝ, 0 < y →
        ∀ (N A : ℕ) (B : ℤ) (q : Fin N → ℂ) (i : Fin N),
          (∀ j, j ≠ i → ((x : ℂ)+Complex.I*(y : ℂ))-Complex.cos (q j) ∈ contourRootDomain) →
          protectedGraphIntegral
            (fun z => continuedSiteDensity A B ((x : ℂ)+Complex.I*(y : ℂ))
              (Function.update q i z)) (cutHalfWidth x) v c =
          ∫ r : ℝ in (-Real.pi)..Real.pi,
            continuedSiteDensity A B ((x : ℂ)+Complex.I*(y : ℂ))
              (Function.update q i (r : ℂ)) := by
  obtain ⟨ε,hε,hD⟩ := common_graph_homotopy_domain hx hx2 hd hdb
  refine ⟨ε,hε,?_⟩
  intro v hv hvε c hc y hy N A B q i hother
  exact continuedSiteDensity_coordinate_transport A B _ q i
    (cutHalfWidth_range hx hx2).1 (cutHalfWidth_range hx hx2).2 hv.le hother
    (hD v hv hvε c hc y hy)

end
end IsoProof
