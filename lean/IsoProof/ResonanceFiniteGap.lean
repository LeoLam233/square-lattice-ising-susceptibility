import IsoProof.ResonanceFiniteArithmetic
import IsoProof.ContourGlobal
import IsoProof.ContourBounds

/-! Actual finite-order product gaps on the full common constrained graph.
The quantitative phase producer and exact arithmetic are both consumed;
no denominator bound is an input to the prime-family result. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def constrainedRootProduct {N : ℕ} (x v y : ℝ) (r : Fin N→ℝ) : ℂ :=
  ∏i,continuedTransferRoot (graphDispersion x (cutHalfWidth x) v y (r i)
    (contourCenter (contourDisplacement (cutHalfWidth x)) r))

/-- Cancellation of the common slope term is exact because the imaginary
angular constraint is preserved. -/
theorem constrained_phase_sum {N : ℕ} (hN : 0<N) (x v y : ℝ) (r : Fin N→ℝ) :
    (∑ i,commonPhaseGain x v y (r i)
      (contourCenter (contourDisplacement (cutHalfWidth x)) r))=
      -Real.log ‖constrainedRootProduct x v y r‖ := by
  rw [constrainedRootProduct,norm_prod,Real.log_prod
    (fun i _=>norm_ne_zero_iff.mpr (continuedTransferRoot_ne_zero _))]
  simp only [←continuedPhase_im,commonPhaseGain_eq,Finset.sum_sub_distrib]
  have hz := sum_centeredContour hN (contourDisplacement (cutHalfWidth x)) r
  rw [←Finset.mul_sum,←Finset.mul_sum,hz,mul_zero,mul_zero,zero_sub]

private theorem signValue_norm (σ : Sign) : ‖signValue σ‖=1 := by
  cases σ <;> simp [signValue]

/-- At a product pole the actual quantitative phase estimate forces height
zero and full angular equality; mixed configurations cannot create a pole. -/
theorem constrained_product_pole_forces_equality {N : ℕ} (hN : 0<N)
    {x v y a : ℝ} {σ : Sign} {r : Fin N→ℝ} (ha : 0<a) (hv : 0<v) (hy : 0≤y)
    (hgain : ∀i,a*(y+v*(r i-contourCenter (contourDisplacement (cutHalfWidth x)) r)^2)
      ≤commonPhaseGain x v y (r i) (contourCenter (contourDisplacement (cutHalfWidth x)) r))
    (hpole : constrainedRootProduct x v y r=signValue σ) :
    y=0 ∧ ∀i,r i=contourCenter (contourDisplacement (cutHalfWidth x)) r := by
  have hsum : (∑i,commonPhaseGain x v y (r i)
      (contourCenter (contourDisplacement (cutHalfWidth x)) r))=0 := by
    rw [constrained_phase_sum hN,hpole,signValue_norm,Real.log_one,neg_zero]
  have hnonneg (i : Fin N) : 0≤commonPhaseGain x v y (r i)
      (contourCenter (contourDisplacement (cutHalfWidth x)) r) :=
    (mul_nonneg ha.le (add_nonneg hy (mul_nonneg hv.le (sq_nonneg _)))).trans (hgain i)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _=>hnonneg i)).mp hsum
  have hle (i : Fin N) : a*(y+v*(r i-contourCenter (contourDisplacement (cutHalfWidth x)) r)^2)≤0 := by
    simpa only [hzero i (Finset.mem_univ _)] using hgain i
  have hy0 : y=0 := by
    have hi := hle ⟨0,hN⟩
    have hsq := sq_nonneg (r ⟨0,hN⟩-contourCenter (contourDisplacement (cutHalfWidth x)) r)
    nlinarith [mul_nonneg hv.le hsq]
  refine ⟨hy0,?_⟩
  intro i
  have hi := hle i
  rw [hy0,zero_add] at hi
  have hs : (r i-contourCenter (contourDisplacement (cutHalfWidth x)) r)^2=0 := by
    have : 0≤(r i-contourCenter (contourDisplacement (cutHalfWidth x)) r)^2 := sq_nonneg _
    nlinarith [mul_pos ha hv]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)

/-- Actual both-sign finite-order resolvent protection on the entire
constrained graph and the complete small closed upper height interval. -/
theorem prime_finite_product_gap {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) {N : ℕ} (hN : 0<N)
    (hNp : 2*N<p) (σ : Sign) :
    ∃ ε : ℝ,0<ε ∧ ∀v,0<v → v≤ε → ∀y∈Icc (0:ℝ) ε,
      ∀r∈constrainedAngularTorus N σ,
      1-signValue σ*constrainedRootProduct (2*Real.cos (IsingBulk.PrimeFamily.angle p a)) v y r≠0 := by
  let x := 2*Real.cos (IsingBulk.PrimeFamily.angle p a)
  have hgeo := admissible_root_geometry hp hp5 ha
  have hx : 0<x := hgeo.2.2.2.2.1
  have hx2 : x<2 := hgeo.2.2.2.2.2
  obtain ⟨d,hd,hdb,hcent⟩ := prime_constrained_contourCenter_uniform hp hp5 ha N hN σ
  obtain ⟨A,hA,ε,hε,hgain⟩ := common_phase_gain hx hx2 hd hdb
  refine ⟨ε,hε,?_⟩
  intro v hv hvε y hy r hr hzero
  let c := contourCenter (contourDisplacement (cutHalfWidth x)) r
  have hc : c∈Icc (-d) d := hcent r hr
  have hpole : constrainedRootProduct x v y r=signValue σ := by
    have hm : signValue σ*constrainedRootProduct x v y r=1 := (sub_eq_zero.mp hzero).symm
    have hs : signValue σ*signValue σ=1 := by cases σ <;> norm_num [signValue]
    calc
      _=signValue σ*(signValue σ*constrainedRootProduct x v y r) := by rw [←mul_assoc,hs,one_mul]
      _=signValue σ := by rw [hm,mul_one]
  obtain ⟨hy0,hconst⟩ := constrained_product_pole_forces_equality hN hA hv hy.1
    (fun i=>hgain v hv hvε y hy (r i) (hr.1 i) c hc) hpole
  have hrconst : r=fun _=>c := funext hconst
  have hcb : |c|<cutHalfWidth x := (abs_le.mpr hc).trans_lt hdb
  have hf : contourDisplacement (cutHalfWidth x) c=c := contourDisplacement_interior hcb.le
  let z := continuedTransferRoot ((x:ℂ)-(Real.cos c:ℂ))
  have hproduct : constrainedRootProduct x v y r=z^N := by
    unfold constrainedRootProduct
    change (∏i,continuedTransferRoot (graphDispersion x (cutHalfWidth x) v y (r i) c))=z^N
    simp only [hrconst,hy0,graphDispersion,scalarGraph,hf,sub_self,mul_zero,
      Complex.ofReal_zero,mul_zero,add_zero,←Complex.ofReal_cos,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin,z]
  have hangle : Complex.exp ((((N:ℝ)*c:ℝ):ℂ)*Complex.I)=signValue σ := by
    simpa only [hrconst,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hr.2
  apply prime_no_constant_signed_collision hp hp5 ha hN hNp σ hangle
    (by simpa only [prime_root_energy,x] using continuedTransferRoot_trace ((x:ℂ)-(Real.cos c:ℂ)))
  exact hproduct.symm.trans hpole

end
end IsoProof
