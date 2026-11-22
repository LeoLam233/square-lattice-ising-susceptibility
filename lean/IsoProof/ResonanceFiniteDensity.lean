import IsoProof.ResonanceFiniteGap
import IsoProof.ContourPhysical
import IsingBulk.First.CompactIntegralHolomorphic
import IsingBulk.HT22.Physical.ComplexAnalytic

/-! The actual continued finite particle density and its open analytic
domain.  Compact finite constrained cycles are protected on a genuine
complex energy disk, including the real cut itself. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open IsingBulk.Tail IsingBulk.HT22.Physical
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def continuedAngularRoot (E q : ℂ) : ℂ := continuedTransferRoot (E-Complex.cos q)

def finiteAngularDomain (N : ℕ) (σ : Sign) : Set (ℂ×(Fin N→ℂ)) :=
  {z | (∀i,z.1-Complex.cos (z.2 i)∈contourRootDomain) ∧
    1-signValue σ*∏i,continuedAngularRoot z.1 (z.2 i)≠0}

def continuedParticleDensity (σ : Sign) {N : ℕ} (z : ℂ×(Fin N→ℂ)) : ℂ :=
  let u := fun i=>continuedAngularRoot z.1 (z.2 i)
  let y := fun i=>Complex.exp (Complex.I*z.2 i)
  ((1+signValue σ*∏i,u i)/(1-signValue σ*∏i,u i))*
    canceledPairProduct u y*∏i,oneBody (u i)

theorem finiteAngularDomain_isOpen (N : ℕ) (σ : Sign) : IsOpen (finiteAngularDomain N σ) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hW (i : Fin N) : Continuous (fun w : ℂ×(Fin N→ℂ)=>w.1-Complex.cos (w.2 i)) := by fun_prop
  have hr (i : Fin N) : ContinuousAt
      (fun w : ℂ×(Fin N→ℂ)=>continuedAngularRoot w.1 (w.2 i)) z :=
    (continuedTransferRoot_analyticAt (hz.1 i)).continuousAt.comp
      (f:=fun w : ℂ×(Fin N→ℂ)=>w.1-Complex.cos (w.2 i)) (hW i).continuousAt
  have hd : ContinuousAt (fun w : ℂ×(Fin N→ℂ)=>
      1-signValue σ*∏i,continuedAngularRoot w.1 (w.2 i)) z := by
    exact continuousAt_const.sub (continuousAt_const.mul (tendsto_finsetProd _ (fun i _=>hr i)))
  have hroots : ∀ᶠ w in 𝓝 z,∀i,w.1-Complex.cos (w.2 i)∈contourRootDomain := by
    rw [Filter.eventually_all]
    intro i
    exact (hW i).continuousAt.preimage_mem_nhds (contourRootDomain_isOpen.mem_nhds (hz.1 i))
  filter_upwards [hroots,hd.eventually_ne hz.2] with w hw hgap
  exact ⟨hw,hgap⟩

/-- Joint holomorphy of the literal continued density, in energy and every
complex angle, with all pair and one-body denominators produced from the
single coherent root sheet. -/
theorem continuedParticleDensity_analyticAt {N : ℕ} {σ : Sign}
    {z : ℂ×(Fin N→ℂ)} (hz : z∈finiteAngularDomain N σ) :
    AnalyticAt ℂ (@continuedParticleDensity σ N) z := by
  have dq (i : Fin N) : AnalyticAt ℂ (fun w : ℂ×(Fin N→ℂ)=>w.2 i) z :=
    (ContinuousLinearMap.proj i : (Fin N→ℂ)→L[ℂ]ℂ).analyticAt _ |>.comp analyticAt_snd
  have dy (i : Fin N) : AnalyticAt ℂ (fun w : ℂ×(Fin N→ℂ)=>Complex.exp (Complex.I*w.2 i)) z :=
    (analyticAt_const.mul (dq i)).cexp
  have dr (i : Fin N) : AnalyticAt ℂ
      (fun w : ℂ×(Fin N→ℂ)=>continuedAngularRoot w.1 (w.2 i)) z :=
    (continuedTransferRoot_analyticAt (hz.1 i)).comp_of_eq
      (analyticAt_fst.sub (Complex.analyticAt_cos.comp (dq i))) rfl
  have hpair (i j : Fin N) : 1-continuedAngularRoot z.1 (z.2 i)*continuedAngularRoot z.1 (z.2 j)≠0 :=
    norm_pos_iff.mp (continuedTransferRoot_pair_gap (hz.1 i))
  have dZ := Finset.univ.analyticAt_fun_prod (fun i _=>dr i)
  have dbody : AnalyticAt ℂ (fun w : ℂ×(Fin N→ℂ)=>∏i,oneBody (continuedAngularRoot w.1 (w.2 i))) z := by
    simp_rw [oneBody_eq_rational]
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dr i)).div (analyticAt_const.sub ((dr i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  have dpair (i j : Fin N) : AnalyticAt ℂ (fun w : ℂ×(Fin N→ℂ)=>
      canceledPair (Complex.exp (Complex.I*w.2 i)) (Complex.exp (Complex.I*w.2 j))
        (continuedAngularRoot w.1 (w.2 i)) (continuedAngularRoot w.1 (w.2 j))) z := by
    exact (((((dy i).sub (dy j)).pow 2).neg.mul (dr i)).mul (dr j)).div
      (((dy i).mul (dy j)).mul ((analyticAt_const.sub ((dr i).mul (dr j))).pow 2))
      (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
        (pow_ne_zero 2 (hpair i j)))
  have dpairs : AnalyticAt ℂ (fun w : ℂ×(Fin N→ℂ)=>
      canceledPairProduct (fun i=>continuedAngularRoot w.1 (w.2 i))
        (fun i=>Complex.exp (Complex.I*w.2 i))) z := by
    apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (Finset.univ.filter (fun j=>i<j)).analyticAt_fun_prod
    intro j _
    exact dpair i j
  exact (((analyticAt_const.add (analyticAt_const.mul dZ)).div
    (analyticAt_const.sub (analyticAt_const.mul dZ)) hz.2).mul dpairs).mul dbody

/-- Every undeformed upper-energy real angular tuple lies in the same
continued analytic domain, including every signed product denominator. -/
theorem real_angles_upper_mem_finiteAngularDomain {N : ℕ} (hN : 0<N) (σ : Sign)
    {E : ℂ} (hE : 0<E.im) (q : Fin N→ℝ) :
    (E,fun i=>(q i:ℂ))∈finiteAngularDomain N σ := by
  have hi (i : Fin N) : 0<(E-Complex.cos (q i:ℂ)).im := by simpa using hE
  constructor
  · intro i
    constructor
    · left
      simpa using hi i
    · right
      simpa using (hi i).ne'
  · apply IsingBulk.HT.Contour.signed_product_gap_ne_zero hN
    · cases σ <;> simp [signValue]
    · intro i
      exact continuedTransferRoot_upper_norm (hi i)

/-- On the undeformed real torus this is the identical physical-root
integrand of the literal particleCoefficient definition. -/
theorem continuedParticleDensity_eq_actual {N : ℕ} (σ : Sign) {E : ℂ} (hE : 0<E.im)
    (q : Fin N→ℝ) :
    continuedParticleDensity σ (E,fun i=>(q i:ℂ))=particleDensity σ E q := by
  have hr (i : Fin N) : continuedAngularRoot E (q i:ℂ)=angleRoot E (q i) := by
    unfold continuedAngularRoot angleRoot
    rw [←Complex.ofReal_cos,continuedTransferRoot_eq_physicalRoot]
    simpa using hE
  simp only [continuedParticleDensity,particleDensity,pairProduct,hr]
  have hy (i : Fin N) : Complex.exp (Complex.I*(q i:ℂ))=anglePoint (q i) := by
    simp only [anglePoint,IsingBulk.Tail.limitingAngle,mul_comm]
  simp only [hy]

/-- A general compact parameter family in the true open analytic domain
has one complex energy radius, chosen before any derivative order. -/
theorem compact_finite_angular_energy_disk {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {N : ℕ} {σ : Sign} (E : ℂ)
    (q : X→Fin N→ℂ) (hq : Continuous q)
    (hgood : ∀r∈K,(E,q r)∈finiteAngularDomain N σ) :
    ∃ρ : ℝ,0<ρ ∧ ∀e : ℂ,‖e‖<ρ → ∀r∈K,(E+e,q r)∈finiteAngularDomain N σ := by
  have he : ∀ᶠ e : ℂ in 𝓝 0,∀r∈K,(E+e,q r)∈finiteAngularDomain N σ := by
    apply hK.eventually_forall_of_forall_eventually
    intro r hr
    have hc : Continuous (fun z : ℂ×X=>(E+z.1,q z.2)) := by fun_prop
    exact ((finiteAngularDomain_isOpen N σ).preimage hc).mem_nhds (by simpa using hgood r hr)
  obtain ⟨ρ,hρ,hprop⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨ρ,hρ,fun e he r hr=>hprop (y:=e) (by simpa using he) r hr⟩

/-- The entire finite constrained torus has one true complex neighborhood
at a sufficiently high prime energy level.  The result covers both signs. -/
theorem prime_finite_analytic_graph_and_homotopy {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) {N : ℕ} (hN : 0<N)
    (hNp : 2*N<p) (σ : Sign) :
    ∃v : ℝ,0<v ∧ ∃ρ : ℝ,0<ρ ∧
      (∀e : ℂ,‖e‖<ρ → ∀r∈constrainedAngularTorus N σ,
      (((2*Real.cos (IsingBulk.PrimeFamily.angle p a):ℝ):ℂ)+e,
        constrainedGraph (contourDisplacement (cutHalfWidth (2*Real.cos (IsingBulk.PrimeFamily.angle p a)))) r v)
        ∈finiteAngularDomain N σ) ∧
      (∀y∈Ioc (0:ℝ) ρ,∀t∈Icc (0:ℝ) 1,∀r∈constrainedAngularTorus N σ,
      (((2*Real.cos (IsingBulk.PrimeFamily.angle p a):ℝ):ℂ)+Complex.I*(y:ℂ),
        constrainedGraph (contourDisplacement (cutHalfWidth (2*Real.cos (IsingBulk.PrimeFamily.angle p a)))) r (t*v))
        ∈finiteAngularDomain N σ) := by
  let x := 2*Real.cos (IsingBulk.PrimeFamily.angle p a)
  obtain ⟨εD,hεD,hD⟩ := prime_constrained_common_graph_domain hp hp5 ha N hN σ
  obtain ⟨εP,hεP,hP⟩ := prime_finite_product_gap hp hp5 ha hN hNp σ
  let v := min εD εP/2
  have hv : 0<v := by dsimp [v]; positivity
  have hvD : v<εD := by have := min_le_left εD εP; dsimp [v]; linarith
  have hvP : v≤εP := by have := min_le_right εD εP; dsimp [v]; linarith
  have hg : ∀r∈constrainedAngularTorus N σ,
      ((x:ℂ),constrainedGraph (contourDisplacement (cutHalfWidth x)) r v)∈finiteAngularDomain N σ := by
    intro r hr
    constructor
    · intro i
      simpa only [graphDispersion,scalarGraph,constrainedGraph,Complex.ofReal_zero,mul_zero,add_zero]
        using hD v hv hvD r hr 0 le_rfl i
    · simpa only [continuedAngularRoot,constrainedRootProduct,graphDispersion,scalarGraph,
        constrainedGraph,Complex.ofReal_zero,mul_zero,add_zero] using
        hP v hv hvP 0 ⟨le_rfl,hεP.le⟩ r hr
  have hf := contourDisplacement_continuous (cutHalfWidth_range
    (admissible_root_geometry hp hp5 ha).2.2.2.2.1
    (admissible_root_geometry hp hp5 ha).2.2.2.2.2).1.le
    (cutHalfWidth_range (admissible_root_geometry hp hp5 ha).2.2.2.2.1
      (admissible_root_geometry hp hp5 ha).2.2.2.2.2).2
  have hq : Continuous (fun r : Fin N→ℝ=>constrainedGraph (contourDisplacement (cutHalfWidth x)) r v) := by
    unfold constrainedGraph contourCenter
    fun_prop
  obtain ⟨ρ,hρ,hgood⟩ := compact_finite_angular_energy_disk
    (constrainedAngularTorus_isCompact N σ) (x:ℂ) _ hq hg
  refine ⟨v,hv,min ρ εP,lt_min hρ hεP,?_,?_⟩
  · intro e he r hr
    exact hgood e (he.trans_le (min_le_left _ _)) r hr
  · intro y hy t ht r hr
    by_cases ht0 : t=0
    · have hg0 : constrainedGraph (contourDisplacement (cutHalfWidth x)) r 0=
          (fun i=>(r i:ℂ)) := by funext i; simp [constrainedGraph]
      change ((x:ℂ)+Complex.I*(y:ℂ),constrainedGraph (contourDisplacement (cutHalfWidth x)) r (t*v))∈_
      rw [ht0,zero_mul,hg0]
      exact real_angles_upper_mem_finiteAngularDomain hN σ
        (E:=(x:ℂ)+Complex.I*(y:ℂ)) (by simpa using hy.1) r
    · have htv : 0<t*v := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hv
      have htvD : t*v<εD := (mul_le_of_le_one_left hv.le ht.2).trans_lt hvD
      have htvP : t*v≤εP := (mul_le_of_le_one_left hv.le ht.2).trans hvP
      have hyP : y∈Icc (0:ℝ) εP := ⟨hy.1.le,hy.2.trans (min_le_right _ _)⟩
      constructor
      · intro i
        exact hD (t*v) htv htvD r hr y hy.1.le i
      · exact hP (t*v) htv htvP y hyP r hr

end
end IsoProof
