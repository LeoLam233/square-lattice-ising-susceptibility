import IsoProof.ResonanceFiniteContinuation
import Mathlib.Analysis.Complex.Convex

/-! A manufactured analytic continuation of every finite particle integral
at a sufficiently high prime energy.  All contour and nonresonance inputs
are proved producers in this import chain. -/
namespace IsoProof
noncomputable section
open Complex Filter Set MeasureTheory Function Metric
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every finite constrained particle coefficient has a genuine complex
analytic continuation at a prime level above twice its particle order.
The statement covers both signs and the complete upper half disk. -/
theorem prime_particleCoefficient_analytic_extension_succ {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) (n : ℕ)
    (hNp : 2*(n+1)<p) (σ : Sign) :
    ∃ρ : ℝ,0<ρ ∧ ∃G : ℂ→ℂ,
      AnalyticOnNhd ℂ G (ball ((2*Real.cos (IsingBulk.PrimeFamily.angle p a):ℝ):ℂ) ρ) ∧
      EqOn (particleCoefficient σ (n+1)) G
        (ball ((2*Real.cos (IsingBulk.PrimeFamily.angle p a):ℝ):ℂ) ρ ∩ {E : ℂ | 0<E.im}) := by
  let x : ℝ := 2*Real.cos (IsingBulk.PrimeFamily.angle p a)
  obtain ⟨v,_hv,ρ,hρ,g,hg,hgp,hend,hhom⟩ :=
    prime_smooth_protected_cycle hp hp5 ha (show 0<n+1 by omega) hNp σ
  let G := smoothConstrainedCoefficient σ n g v 1
  let E₀ : ℂ := (x:ℂ)+Complex.I*((ρ/2:ℝ):ℂ)
  have hE₀im : 0<E₀.im := by simp only [E₀,Complex.add_im,Complex.ofReal_im,
    Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add]; positivity
  have hE₀ball : E₀∈ball (x:ℂ) ρ := by
    rw [mem_ball,dist_eq_norm]
    simp only [E₀,add_sub_cancel_left,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (half_pos hρ)]
    exact half_lt_self hρ
  have hGa : AnalyticOnNhd ℂ G (ball (x:ℂ) ρ) := by
    apply smoothConstrainedCoefficient_analyticOnNhd σ n hg v 1 isOpen_ball
    intro E hE θ _
    rw [smoothConstrainedHomotopy_full]
    simp only [Fin.cons_zero,Fin.cons_succ,one_mul]
    exact finiteAngularDomain_graph_of_periodic hgp _ (constrainedAngles_phase σ n θ)
      (hend E (by simpa only [mem_ball,dist_eq_norm] using hE))
  let K := Icc (IsingBulk.Preferred22.homotopyBoxLower n) (IsingBulk.Preferred22.homotopyBoxUpper n)
  let Q : (Fin (n+1)→ℝ)→Fin (n+1)→ℂ := fun z=>
    constrainedComplexAngles σ n (smoothConstrainedHomotopy σ n g v z)
  have hQ : Continuous Q := by
    have hcc : Continuous (constrainedComplexAngles σ n) :=
      continuous_iff_continuousAt.mpr (fun q=>(constrainedComplexAngles_analyticAt σ n q).continuousAt)
    exact hcc.comp (smoothConstrainedHomotopy_contDiff σ n hg v).continuous
  have hgood₀ : ∀z∈K,(E₀,Q z)∈finiteAngularDomain (n+1) σ := by
    intro z hz
    dsimp only [Q]
    rw [smoothConstrainedHomotopy_full]
    apply finiteAngularDomain_graph_of_periodic hgp _ (constrainedAngles_phase σ n _)
    exact hhom (z 0) ⟨hz.1 0,hz.2 0⟩
  obtain ⟨δ,hδ,hδgood⟩ := compact_finite_angular_energy_disk
    (show IsCompact K from isCompact_Icc) E₀ Q hQ hgood₀
  have heq : particleCoefficient σ (n+1)=ᶠ[𝓝 E₀]G := by
    have him : ∀ᶠ E : ℂ in 𝓝 E₀,0<E.im :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hE₀im
    filter_upwards [ball_mem_nhds E₀ hδ,him] with E hE hIm
    symm
    apply smoothConstrainedCoefficient_eq_particle σ n hg hgp v hIm
    intro z hz
    have h := hδgood (E-E₀) (by simpa only [mem_ball,dist_eq_norm] using hE) z hz
    simpa only [add_sub_cancel] using h
  let D := ball (x:ℂ) ρ ∩ {E : ℂ | 0<E.im}
  have hA : AnalyticOnNhd ℂ (particleCoefficient σ (n+1)) D :=
    fun E hE=>particleCoefficient_analyticAt σ (n+1) (Or.inl hE.2.ne')
  have hD : IsPreconnected D := ((convex_ball (x:ℂ) ρ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  refine ⟨ρ,hρ,G,hGa,?_⟩
  exact hA.eqOn_of_preconnected_of_eventuallyEq (hGa.mono inter_subset_left) hD
    ⟨hE₀ball,hE₀im⟩ heq

/-- The finite particle order is literal `N`, with no continuation, trace,
tail, or pole exclusion hypothesis on the right hand side. -/
theorem prime_particleCoefficient_analytic_extension {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a) {N : ℕ} (hN : 0<N)
    (hNp : 2*N<p) (σ : Sign) :
    ∃ρ : ℝ,0<ρ ∧ ∃G : ℂ→ℂ,
      AnalyticOnNhd ℂ G (ball ((2*Real.cos (IsingBulk.PrimeFamily.angle p a):ℝ):ℂ) ρ) ∧
      EqOn (particleCoefficient σ N) G
        (ball ((2*Real.cos (IsingBulk.PrimeFamily.angle p a):ℝ):ℂ) ρ ∩ {E : ℂ | 0<E.im}) := by
  cases N with
  | zero => omega
  | succ n => exact prime_particleCoefficient_analytic_extension_succ hp hp5 ha n hNp σ

/-- Any nonempty interior cut interval contains a point at which all
finitely many positive particle orders have actual upper analytic extensions.
The individual radii may subsequently be intersected by finite induction. -/
theorem finite_particleCoefficient_extensions_in_interval (σ : Sign) (M : ℕ)
    {L U : ℝ} (hL : 0<L) (hLU : L<U) (hU : U<2) :
    ∃x : ℝ,x∈Ioo L U ∧ ∀N : ℕ,0<N→N≤M→
      ∃ρ : ℝ,0<ρ ∧ ∃G : ℂ→ℂ,AnalyticOnNhd ℂ G (ball (x:ℂ) ρ) ∧
        EqOn (particleCoefficient σ N) G (ball (x:ℂ) ρ∩{E : ℂ|0<E.im}) := by
  let x := (L+U)/2
  let θ := Real.arccos (x/2)
  have hx : x∈Ioo L U := by dsimp [x]; constructor <;> linarith
  have hx0 : 0<x := hL.trans hx.1
  have hx2 : x<2 := hx.2.trans hU
  have hθ0 : 0<θ := Real.arccos_pos.mpr (by linarith)
  have hθπ : θ<Real.pi/2 := Real.arccos_lt_pi_div_two.mpr (by linarith)
  have hcos : 2*Real.cos θ=x := by
    dsimp only [θ]
    rw [Real.cos_arccos (by linarith) (by linarith)]
    ring
  have hneigh : {t : ℝ|2*Real.cos t∈Ioo L U}∈𝓝 θ :=
    (continuous_const.mul Real.continuous_cos).continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds (by change 2*Real.cos θ∈Ioo L U; rw [hcos]; exact hx))
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hneigh
  obtain ⟨p,a,b,hp,hp11,hpM,_hab,ha,_hb,hclose,_hcloseb⟩ :=
    neighboring_prime_angles_above (2*M+1) hθ0 hθπ hδ
  refine ⟨2*Real.cos (IsingBulk.PrimeFamily.angle p a),?_,?_⟩
  · apply hδsub
    simpa only [mem_ball,Real.dist_eq] using hclose
  · intro N hN hNM
    exact prime_particleCoefficient_analytic_extension hp (by omega) ha hN (by omega) σ

end
end IsoProof
