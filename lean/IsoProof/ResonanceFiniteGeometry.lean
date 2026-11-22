import IsoProof.ContourProtected
import IsoProof.ContourAlgebra
import IsoProof.Objects
import Mathlib.Topology.Instances.Real.Lemmas

/-! Compact geometry of the literal constrained common contour.  Endpoint
arithmetic forces the arithmetic mean of the displacement strictly inside
its two endpoints, uniformly on the entire constrained torus. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem contourDisplacement_nonnegative_side {b r : ℝ}
    (hb : 0<b) (hbpi : b<Real.pi) (hr0 : 0≤r) (hrpi : r≤Real.pi) :
    0≤contourDisplacement b r ∧ contourDisplacement b r≤b ∧
      (contourDisplacement b r=b ↔ r=b) := by
  by_cases hrb : r≤b
  · rw [contourDisplacement_interior (by rwa [abs_of_nonneg hr0])]
    exact ⟨hr0,hrb,Iff.rfl⟩
  · have hrb' : b<r := lt_of_not_ge hrb
    have hform : contourDisplacement b r=b*(Real.pi-r)/(Real.pi-b) := by
      simp only [contourDisplacement,abs_of_nonneg hr0,hrb,ite_false,hr0,ite_true]
    have hp : 0<Real.pi-b := sub_pos.mpr hbpi
    have hlo : 0≤b*(Real.pi-r)/(Real.pi-b) :=
      div_nonneg (mul_nonneg hb.le (sub_nonneg.mpr hrpi)) hp.le
    have hhi : b*(Real.pi-r)/(Real.pi-b)<b := by
      apply (div_lt_iff₀ hp).mpr
      nlinarith
    rw [hform]
    exact ⟨hlo,hhi.le,iff_of_false hhi.ne (ne_of_gt hrb')⟩

theorem contourDisplacement_range_and_extrema {b r : ℝ}
    (hb : 0<b) (hbpi : b<Real.pi) (hr : r∈Icc (-Real.pi) Real.pi) :
    -b≤contourDisplacement b r ∧ contourDisplacement b r≤b ∧
      (contourDisplacement b r=b ↔ r=b) ∧
      (contourDisplacement b r= -b ↔ r= -b) := by
  by_cases hr0 : 0≤r
  · obtain ⟨hlo,hhi,he⟩ := contourDisplacement_nonnegative_side hb hbpi hr0 hr.2
    refine ⟨by linarith,hhi,he,?_⟩
    exact iff_of_false (by intro h; linarith) (by intro h; linarith)
  · have hr0' : r<0 := lt_of_not_ge hr0
    obtain ⟨hlo,hhi,he⟩ := contourDisplacement_nonnegative_side hb hbpi
      (by linarith : 0≤ -r) (by linarith [hr.1] : -r≤Real.pi)
    have hf : contourDisplacement b r= -contourDisplacement b (-r) := by
      simpa only [neg_neg] using contourDisplacement_odd hb.le (-r)
    rw [hf]
    refine ⟨by linarith,by linarith,?_,?_⟩
    · exact iff_of_false (by intro h; linarith) (by intro h; linarith)
    · simpa only [neg_inj,neg_eq_iff_eq_neg,neg_neg] using he

/-- Principal real representatives of the actual angular constraint.  The
exponential equation allows all winding components of the same torus. -/
def constrainedAngularTorus (N : ℕ) (σ : Sign) : Set (Fin N→ℝ) :=
  {r | (∀ i,r i∈Icc (-Real.pi) Real.pi) ∧
    Complex.exp ((((∑ i,r i):ℝ):ℂ)*Complex.I)=signValue σ}

theorem constrainedAngularTorus_isCompact (N : ℕ) (σ : Sign) :
    IsCompact (constrainedAngularTorus N σ) := by
  have hbox : IsCompact {r : Fin N→ℝ | ∀ i,r i∈Icc (-Real.pi) Real.pi} := by
    convert (isCompact_univ_pi (fun _ : Fin N=>
      isCompact_Icc (a:= -Real.pi) (b:=Real.pi))) using 1
    ext r
    simp [Pi.le_def,forall_and]
  have hc : Continuous (fun r : Fin N→ℝ=>Complex.exp ((((∑ i,r i):ℝ):ℂ)*Complex.I)) := by
    fun_prop
  exact hbox.inter_right (isClosed_eq hc continuous_const)

theorem contourCenter_continuous {N : ℕ} {b : ℝ} (hb : 0≤b) (hbpi : b<Real.pi) :
    Continuous (contourCenter (N:=N) (contourDisplacement b)) := by
  have hf := contourDisplacement_continuous hb hbpi
  unfold contourCenter
  fun_prop

private theorem contourCenter_endpoint_forces_constant {N : ℕ} (hN : 0<N)
    {b : ℝ} (hb : 0<b) (hbpi : b<Real.pi) {r : Fin N→ℝ}
    (hr : ∀ i,r i∈Icc (-Real.pi) Real.pi)
    (he : contourCenter (contourDisplacement b) r=b) : r=fun _=>b := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hsum : (∑ i,contourDisplacement b (r i))=∑ _i : Fin N,b := by
    have h := (div_eq_iff hN0).mp he
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm]
      using h
  have heach := (Finset.sum_eq_sum_iff_of_le
    (fun i (_hi : i∈Finset.univ)=>(contourDisplacement_range_and_extrema hb hbpi (hr i)).2.1)).mp hsum
  funext i
  exact (contourDisplacement_range_and_extrema hb hbpi (hr i)).2.2.1.mp
    (heach i (Finset.mem_univ _))

/-- With both endpoint tuples arithmetically excluded, no constrained tuple
can have its displacement mean equal to either endpoint. -/
theorem constrained_contourCenter_strict {N : ℕ} (hN : 0<N) {σ : Sign}
    {b : ℝ} (hb : 0<b) (hbpi : b<Real.pi)
    (hplus : Complex.exp ((((N:ℝ)*b:ℝ):ℂ)*Complex.I)≠signValue σ)
    (hminus : Complex.exp ((((N:ℝ)*(-b):ℝ):ℂ)*Complex.I)≠signValue σ)
    {r : Fin N→ℝ} (hr : r∈constrainedAngularTorus N σ) :
    |contourCenter (contourDisplacement b) r|<b := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hbounds (i : Fin N) := contourDisplacement_range_and_extrema hb hbpi (hr.1 i)
  have hsumU := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(hbounds i).2.1)
  have hsumL := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(hbounds i).1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsumU hsumL
  have hU : contourCenter (contourDisplacement b) r≤b := by
    exact (div_le_iff₀ hNp).mpr (by simpa only [mul_comm] using hsumU)
  have hL : -b≤contourCenter (contourDisplacement b) r := by
    exact (le_div_iff₀ hNp).mpr (by simpa only [mul_comm] using hsumL)
  have heU : contourCenter (contourDisplacement b) r≠b := by
    intro he
    have heq := contourCenter_endpoint_forces_constant hN hb hbpi hr.1 he
    apply hplus
    simpa only [heq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hr.2
  have heL : contourCenter (contourDisplacement b) r≠ -b := by
    intro he
    have hrneg : ∀i,-r i∈Icc (-Real.pi) Real.pi := fun i=>
      ⟨by linarith [(hr.1 i).2],by linarith [(hr.1 i).1]⟩
    have heNeg : contourCenter (contourDisplacement b) (fun i=> -r i)=b := by
      simp only [contourCenter,contourDisplacement_odd hb.le,Finset.sum_neg_distrib,
        neg_div] at he ⊢
      linarith
    have heq := contourCenter_endpoint_forces_constant hN hb hbpi hrneg heNeg
    have hrconst : r=fun _=> -b := by
      funext i
      have hi := congrFun heq i
      linarith
    apply hminus
    simpa only [hrconst,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hr.2
  exact abs_lt.mpr ⟨lt_of_le_of_ne hL heL.symm,lt_of_le_of_ne hU heU⟩

/-- The center interval is compactly contained in the oscillatory interval.
The bound is shared by every angular point in the same constrained torus. -/
theorem constrained_contourCenter_uniform {N : ℕ} (hN : 0<N) {σ : Sign}
    {b : ℝ} (hb : 0<b) (hbpi : b<Real.pi)
    (hplus : Complex.exp ((((N:ℝ)*b:ℝ):ℂ)*Complex.I)≠signValue σ)
    (hminus : Complex.exp ((((N:ℝ)*(-b):ℝ):ℂ)*Complex.I)≠signValue σ) :
    ∃ d : ℝ,0≤d ∧ d<b ∧ ∀r∈constrainedAngularTorus N σ,
      contourCenter (contourDisplacement b) r∈Icc (-d) d := by
  let K := constrainedAngularTorus N σ
  have hK : IsCompact K := constrainedAngularTorus_isCompact N σ
  have hf : Continuous (fun r : Fin N→ℝ=>|contourCenter (contourDisplacement b) r|) :=
    (contourCenter_continuous hb.le hbpi).abs
  by_cases hne : K.Nonempty
  · obtain ⟨r,hr,hmax⟩ := hK.exists_isMaxOn hne hf.continuousOn
    refine ⟨|contourCenter (contourDisplacement b) r|,abs_nonneg _,
      constrained_contourCenter_strict hN hb hbpi hplus hminus hr,?_⟩
    intro u hu
    exact abs_le.mp (hmax hu)
  · refine ⟨0,le_rfl,hb,?_⟩
    intro u hu
    exact (hne ⟨u,hu⟩).elim

/-- The concrete graph stays on its analytic continued transfer-root domain,
with its actual constrained mean and all winding components retained. -/
theorem constrained_common_graph_domain {N : ℕ} (hN : 0<N) {σ : Sign}
    {x : ℝ} (hx : 0<x) (hx2 : x<2)
    (hplus : Complex.exp ((((N:ℝ)*cutHalfWidth x:ℝ):ℂ)*Complex.I)≠signValue σ)
    (hminus : Complex.exp ((((N:ℝ)*(-cutHalfWidth x):ℝ):ℂ)*Complex.I)≠signValue σ) :
    ∃ ε : ℝ,0<ε ∧ ∀v,0<v → v<ε → ∀r∈constrainedAngularTorus N σ,
      ∀y,0≤y → ∀i : Fin N,
      graphDispersion x (cutHalfWidth x) v y (r i)
        (contourCenter (contourDisplacement (cutHalfWidth x)) r)∈contourRootDomain := by
  obtain ⟨hb,hbpi⟩ := cutHalfWidth_range hx hx2
  obtain ⟨d,hd,hdb,hcent⟩ := constrained_contourCenter_uniform hN hb hbpi hplus hminus
  obtain ⟨ε,hε,hdom⟩ := common_graph_domain hx hx2 hd hdb
  exact ⟨ε,hε,fun v hv hvε r hr y hy i=>hdom v hv hvε (r i) (hr.1 i)
    _ (hcent r hr) y hy⟩

end
end IsoProof
