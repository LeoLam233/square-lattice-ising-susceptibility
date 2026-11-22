import IsoProof.ResonancePeriodicGeometry
import Mathlib.Topology.MetricSpace.Thickening

/-! Uniform perturbation of the finite common cycle into a smooth periodic
cycle.  Compact openness preserves every actual root and product gap;
there is no unproved homotopy or denominator hypothesis in the prime output. -/
namespace IsoProof
noncomputable section
open Complex Filter Set Metric Function
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem contourCenter_dist_le {N : ℕ} (hN : 0<N) {f g : ℝ→ℝ} {ε : ℝ}
    (hfg : ∀x,dist (g x) (f x)≤ε) (r : Fin N→ℝ) :
    dist (contourCenter g r) (contourCenter f r)≤ε := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  rw [Real.dist_eq,contourCenter,contourCenter,←sub_div,←Finset.sum_sub_distrib,
    abs_div,abs_of_pos hNp]
  apply (div_le_iff₀ hNp).mpr
  calc
    |(∑ i, (g (r i)-f (r i)))| ≤ ∑ i, |g (r i)-f (r i)| := Finset.abs_sum_le_sum_abs _ _
    _≤∑_i : Fin N,ε := Finset.sum_le_sum (fun i _=>hfg (r i))
    _=ε*(N:ℝ) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem constrainedGraph_dist_le {N : ℕ} (hN : 0<N) {f g : ℝ→ℝ} {ε : ℝ} (hε : 0≤ε)
    (hfg : ∀x,dist (g x) (f x)≤ε) (r : Fin N→ℝ) (t : ℝ) :
    dist (constrainedGraph g r t) (constrainedGraph f r t)≤2*|t| * ε := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hm := contourCenter_dist_le hN hfg r
  have hp := norm_sub_le (g (r i)-f (r i)) (contourCenter g r-contourCenter f r)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs] at hp
  have hd : |g (r i)-contourCenter g r-(f (r i)-contourCenter f r)|≤2*ε := by
    have hi : |g (r i)-f (r i)|≤ε := hfg (r i)
    have hm' : |contourCenter g r-contourCenter f r|≤ε := hm
    convert hp.trans (add_le_add hi hm') using 1 <;> ring
  rw [dist_eq_norm]
  have he : constrainedGraph g r t i-constrainedGraph f r t i=
      Complex.I*((t*(g (r i)-contourCenter g r-(f (r i)-contourCenter f r)):ℝ):ℂ) := by
    simp only [constrainedGraph]
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hd (abs_nonneg t)]

/-- Uniformly close smooth periodic displacements preserve an arbitrary
compact family of protected finite constrained cycles. -/
theorem smooth_periodic_graph_in_domain {N : ℕ} (hN : 0<N) (σ : Sign)
    {b : ℝ} (hb : 0≤b) (hbpi : b<Real.pi)
    {K : Set (ℂ×(ℝ×(Fin N→ℝ)))} (hK : IsCompact K) {V : ℝ} (hV : 0≤V)
    (ht : ∀z∈K,|z.2.1|≤V)
    (hgood : ∀z∈K,(z.1,constrainedGraph (periodicContourDisplacement b) z.2.2 z.2.1)
      ∈finiteAngularDomain N σ) :
    ∃g : ℝ→ℝ,ContDiff ℝ ∞ g ∧ Periodic g (2*Real.pi) ∧
      ∀z∈K,(z.1,constrainedGraph g z.2.2 z.2.1)∈finiteAngularDomain N σ := by
  let F : (ℂ×(ℝ×(Fin N→ℝ)))→ℂ×(Fin N→ℂ) := fun z=>
    (z.1,constrainedGraph (periodicContourDisplacement b) z.2.2 z.2.1)
  have hf := periodicContourDisplacement_continuous hb hbpi
  have hF : Continuous F := by unfold F constrainedGraph contourCenter; fun_prop
  obtain ⟨δ,hδ,hδsub⟩ := (hK.image hF).exists_thickening_subset_open
    (finiteAngularDomain_isOpen N σ) (by rintro _ ⟨z,hz,rfl⟩; exact hgood z hz)
  let ε := δ/(4*(V+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  obtain ⟨g,hg,hgp,happrox⟩ := contourDisplacement_smooth_periodic_uniform_approx hb hbpi hε
  refine ⟨g,hg,hgp,?_⟩
  intro z hz
  apply hδsub
  apply mem_thickening_iff.mpr
  refine ⟨F z,mem_image_of_mem F hz,?_⟩
  change dist (z.1,constrainedGraph g z.2.2 z.2.1)
    (z.1,constrainedGraph (periodicContourDisplacement b) z.2.2 z.2.1)<δ
  rw [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)]
  have hdist := constrainedGraph_dist_le hN hε.le (fun x=>(happrox x).le) z.2.2 z.2.1
  have hbound : 2*|z.2.1| * ε≤2*V*ε := by nlinarith [ht z hz]
  have hsmall : 2*V*ε<δ := by
    dsimp [ε]
    have hden : 0<4*(V+1) := by positivity
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  exact hdist.trans_lt (hbound.trans_lt hsmall)

theorem constrainedGraph_cos_eq_principal_of_periodic {g : ℝ→ℝ}
    (hg : Periodic g (2*Real.pi)) {N : ℕ} (r : Fin N→ℝ) (v : ℝ) (i : Fin N) :
    Complex.cos (constrainedGraph g r v i)=
      Complex.cos (constrainedGraph g (fun j=>principalContourAngle (r j)) v i) := by
  have hc : contourCenter g (fun j=>principalContourAngle (r j))=contourCenter g r := by
    simp only [contourCenter,periodic_principalContourAngle hg]
  unfold constrainedGraph
  rw [hc,periodic_principalContourAngle hg]
  exact (periodic_principalContourAngle (real_shifted_complex_cos_periodic _) (r i)).symm

theorem finiteAngularDomain_graph_of_periodic {N : ℕ} {σ : Sign} {g : ℝ→ℝ}
    (hg : Periodic g (2*Real.pi)) {E : ℂ} {v : ℝ} (r : Fin N→ℝ)
    (hphase : Complex.exp ((((∑i,r i):ℝ):ℂ)*Complex.I)=signValue σ)
    (hgood : ∀q∈constrainedAngularTorus N σ,
      (E,constrainedGraph g q v)∈finiteAngularDomain N σ) :
    (E,constrainedGraph g r v)∈finiteAngularDomain N σ := by
  have h := hgood _ (principal_tuple_mem_constrainedAngularTorus r hphase)
  constructor
  · intro i
    change E-Complex.cos (constrainedGraph g r v i)∈contourRootDomain
    rw [constrainedGraph_cos_eq_principal_of_periodic hg r v i]
    exact h.1 i
  · have hroots : (fun i=>continuedAngularRoot E (constrainedGraph g r v i))=
        (fun i=>continuedAngularRoot E (constrainedGraph g (fun j=>principalContourAngle (r j)) v i)) := by
      funext i
      unfold continuedAngularRoot
      rw [constrainedGraph_cos_eq_principal_of_periodic hg r v i]
    change 1-signValue σ*∏i,continuedAngularRoot E (constrainedGraph g r v i)≠0
    rw [show (∏i,continuedAngularRoot E (constrainedGraph g r v i))=
      ∏i,continuedAngularRoot E (constrainedGraph g (fun j=>principalContourAngle (r j)) v i) from
      congrArg (fun u : Fin N→ℂ=>∏i,u i) hroots]
    exact h.2

private theorem constrainedGraph_periodic_eq {b : ℝ} (hbpi : b<Real.pi) {N : ℕ}
    {r : Fin N→ℝ} (hr : ∀i,r i∈Icc (-Real.pi) Real.pi) (v : ℝ) :
    constrainedGraph (periodicContourDisplacement b) r v=
      constrainedGraph (contourDisplacement b) r v := by
  funext i
  simp only [constrainedGraph,contourCenter,periodicContourDisplacement_agrees hbpi (hr _)]

/-- A concrete smooth periodic finite constrained cycle, with an entire
complex endpoint neighborhood and one complete upper-side homotopy.  Every
analytic-domain assertion is produced from the actual common graph. -/
theorem prime_smooth_protected_cycle {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) {N : ℕ} (hN : 0<N)
    (hNp : 2*N<p) (σ : Sign) :
    ∃v : ℝ,0<v ∧ ∃ρ : ℝ,0<ρ ∧ ∃g : ℝ→ℝ,ContDiff ℝ ∞ g ∧ Periodic g (2*Real.pi) ∧
      (∀E : ℂ,‖E-((2*Real.cos (IsingBulk.PrimeFamily.angle p a):ℝ):ℂ)‖<ρ →
        ∀r∈constrainedAngularTorus N σ,(E,constrainedGraph g r v)∈finiteAngularDomain N σ) ∧
      (∀t∈Icc (0:ℝ) 1,∀r∈constrainedAngularTorus N σ,
        (((2*Real.cos (IsingBulk.PrimeFamily.angle p a):ℝ):ℂ)+Complex.I*((ρ/2:ℝ):ℂ),
          constrainedGraph g r (t*v))∈finiteAngularDomain N σ) := by
  let x := 2*Real.cos (IsingBulk.PrimeFamily.angle p a)
  let b := cutHalfWidth x
  obtain ⟨hb,hbpi⟩ := cutHalfWidth_range (admissible_root_geometry hp hp5 ha).2.2.2.2.1
    (admissible_root_geometry hp hp5 ha).2.2.2.2.2
  obtain ⟨v,hv,ρ,hρ,hend,hhom⟩ := prime_finite_analytic_graph_and_homotopy hp hp5 ha hN hNp σ
  let E₀ : ℂ := (x:ℂ)+Complex.I*((ρ/4:ℝ):ℂ)
  let K₀ : Set (ℂ×(Fin N→ℝ)) := closedBall (0:ℂ) (ρ/2) ×ˢ constrainedAngularTorus N σ
  let K₁ : Set (ℝ×(Fin N→ℝ)) := Icc (0:ℝ) 1 ×ˢ constrainedAngularTorus N σ
  let F₀ : (ℂ×(Fin N→ℝ))→ℂ×(ℝ×(Fin N→ℝ)) := fun z=>((x:ℂ)+z.1,(v,z.2))
  let F₁ : (ℝ×(Fin N→ℝ))→ℂ×(ℝ×(Fin N→ℝ)) := fun z=>(E₀,(z.1*v,z.2))
  let K := F₀ '' K₀ ∪ F₁ '' K₁
  have hc₀ : Continuous F₀ := by unfold F₀; fun_prop
  have hc₁ : Continuous F₁ := by unfold F₁; fun_prop
  have hK₀ : IsCompact K₀ := (isCompact_closedBall (0:ℂ) (ρ/2)).prod (constrainedAngularTorus_isCompact N σ)
  have hK₁ : IsCompact K₁ := isCompact_Icc.prod (constrainedAngularTorus_isCompact N σ)
  have hK : IsCompact K := (hK₀.image hc₀).union (hK₁.image hc₁)
  have htime : ∀z∈K,|z.2.1|≤v := by
    rintro z (⟨w,hw,rfl⟩|⟨w,hw,rfl⟩)
    · change |v|≤v
      rw [abs_of_pos hv]
    · change |w.1*v|≤v
      rw [abs_of_nonneg (mul_nonneg hw.1.1 hv.le)]
      exact mul_le_of_le_one_left hv.le hw.1.2
  have hgood : ∀z∈K,(z.1,constrainedGraph (periodicContourDisplacement b) z.2.2 z.2.1)
      ∈finiteAngularDomain N σ := by
    rintro z (⟨w,hw,rfl⟩|⟨w,hw,rfl⟩)
    · dsimp only [F₀]
      rw [constrainedGraph_periodic_eq hbpi hw.2.1]
      exact hend w.1 ((show ‖w.1‖≤ρ/2 by simpa using hw.1).trans_lt (half_lt_self hρ)) w.2 hw.2
    · dsimp only [F₁]
      rw [constrainedGraph_periodic_eq hbpi hw.2.1]
      exact hhom (ρ/4) ⟨by positivity,by linarith⟩ w.1 hw.1 w.2 hw.2
  obtain ⟨g,hg,hgp,hgK⟩ := smooth_periodic_graph_in_domain hN σ hb.le hbpi hK hv.le htime hgood
  refine ⟨v,hv,ρ/2,half_pos hρ,g,hg,hgp,?_,?_⟩
  · intro E hE r hr
    have harg : (E-(x:ℂ),r)∈K₀ := ⟨by
      rw [mem_closedBall,dist_zero_right]
      exact hE.le,hr⟩
    have h := hgK (F₀ (E-(x:ℂ),r)) (Or.inl (mem_image_of_mem F₀ harg))
    simpa only [F₀,show (x:ℂ)+(E-(x:ℂ))=E by ring] using h
  · intro t ht r hr
    have h := hgK (F₁ (t,r)) (Or.inr (mem_image_of_mem F₁ (show (t,r)∈K₁ from ⟨ht,hr⟩)))
    convert h using 1
    dsimp [F₁,E₀]
    congr 2
    push_cast
    ring

end
end IsoProof
