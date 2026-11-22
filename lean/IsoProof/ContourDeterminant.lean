import IsoProof.ContourBounds
import IsoProof.IntegralsDeterminant

/-! The both-parity N^(3N/4) pair bound on the concrete common graph,
including a uniform complex E-disk. This invokes the exact removable
kernel product and retains the continuation sheet constructed earlier. -/
namespace IsoProof
noncomputable section
open scoped BigOperators
open Set

/-- Uniformity is simultaneous in particle number, angle tuple, center,
upper energy height and complex energy error. -/
theorem common_graph_pair_bound {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε → ∃ ρ > 0, ∃ C > 0,
      ∀ e : ℂ, ‖e‖ ≤ ρ → ∀ y ∈ Icc (0 : ℝ) 1, ∀ c ∈ Icc (-d) d,
      ∀ N : ℕ, 0 < N → ∀ r : Fin N → ℝ, (∀ i, r i ∈ Icc (-Real.pi) Real.pi) →
      let E := (x : ℂ)+Complex.I*(y : ℂ)+e
      let q := fun i => scalarGraph (cutHalfWidth x) v (r i) c
      ‖IsingBulk.Tail.canceledPairProduct
        (fun i => continuedTransferRoot (E-Complex.cos (q i)))
        (fun i => Complex.exp (Complex.I*q i))‖ ≤
          (C*(N : ℝ)^(3/4 : ℝ))^N := by
  obtain ⟨ε,hε,hbounds⟩ := common_graph_scalar_bounds hx hx2 hd hdb
  refine ⟨ε,hε,?_⟩
  intro v hv hvε
  obtain ⟨ρ,hρ,M,hM,δ,hδ,hDom,hy0,hy,hz,hgap⟩ := hbounds v hv hvε
  have hC : 0 < 4*(pairEntryEnvelope M δ)^2 := by
    have hone : 1 ≤ pairEntryEnvelope M δ := le_max_left _ _
    nlinarith
  refine ⟨ρ,hρ,4*(pairEntryEnvelope M δ)^2,hC,?_⟩
  intro e he y hyc c hc N hN r hr
  let E : ℂ := (x : ℂ)+Complex.I*(y : ℂ)+e
  let q : Fin N → ℂ := fun i => scalarGraph (cutHalfWidth x) v (r i) c
  let t : Fin N → ℂ × (ℝ × (ℝ × ℝ)) := fun i => (e,(y,(r i,c)))
  have ht (i : Fin N) : t i ∈ Metric.closedBall (0 : ℂ) ρ ×ˢ commonGraphBox d := by
    exact ⟨by simpa using he,hyc,hr i,hc⟩
  exact complex_pairProduct_three_quarters N hN E
    (fun i => Complex.exp (Complex.I*q i))
    (fun i => continuedTransferRoot (E-Complex.cos (q i))) hM.le hδ
    (fun i => hy0 (t i) (ht i)) (fun i => hy (t i) (ht i))
    (fun i => continuedTransferRoot_ne_zero _) (fun i => hz (t i) (ht i))
    (fun i => exponential_dispersion (q i) E)
    (fun i j => hgap (t i) (ht i) (t j) (ht j))

end
end IsoProof
