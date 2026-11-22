import IsoProof.IntegralsSiteGraph
import IsingBulk.First.CompactIntegralHolomorphic
import Mathlib.Topology.Order.ProjIcc

/-! True parameter differentiation of the piecewise graph integral.
The angular corners are kept as three compact real integrals; they are
never differentiated as if the graph were a globally smooth parametrization. -/
namespace IsoProof
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_parametric_intervalIntegral
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]
    {U : Set P} (hU : IsOpen U) (l r : ℝ) (hlr : l ≤ r)
    (H : P → ℝ → ℂ) (hH : ContinuousOn (Function.uncurry H) (U ×ˢ Icc l r)) :
    ContinuousOn (fun p => ∫ u : ℝ in l..r, H p u) U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let g : U → ℝ → ℂ := fun p u => H p.1 (Set.projIcc l r hlr u)
  have hg : Continuous (Function.uncurry g) := by
    apply continuousOn_univ.mp
    change ContinuousOn ((Function.uncurry H) ∘
      (fun p : U × ℝ => (p.1.1, (Set.projIcc l r hlr p.2 : ℝ)))) univ
    apply hH.comp
    · exact ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))).continuousOn
    · intro p _
      exact ⟨p.1.property,(Set.projIcc l r hlr p.2).property⟩
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hg
    (s := Icc l r) isCompact_Icc
  have he (p : U) : (∫ u in Icc l r, g p u) = ∫ u : ℝ in l..r, H p.1 u := by
    rw [intervalIntegral.integral_of_le hlr, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    simp only [g, Set.projIcc_of_mem hlr hu]
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun p : U => ∫ u : ℝ in l..r, H p.1 u)
  simpa only [he] using hi

def realPieceGraphIntegral (b v : ℝ) (H : ℝ → ℂ) : ℂ :=
  (∫ r : ℝ in (-Real.pi)..(-b), H r *
    (1+Complex.I*((v : ℂ)*((-b/(Real.pi-b) : ℝ) : ℂ)))) +
  (∫ r : ℝ in (-b)..b, H r * (1+Complex.I*(v : ℂ))) +
  (∫ r : ℝ in b..Real.pi, H r *
    (1+Complex.I*((v : ℂ)*((-b/(Real.pi-b) : ℝ) : ℂ))))

def realPieceGraphMultiIntegral (b v : ℝ) :
    (N : ℕ) → ((Fin N → ℝ) → ℂ) → ℂ
  | 0, H => H Fin.elim0
  | n+1, H => realPieceGraphIntegral b v
      (fun r => realPieceGraphMultiIntegral b v n (fun q => H (Fin.cons r q)))

theorem protectedGraphMultiIntegral_eq_realPiece (N : ℕ) {b : ℝ}
    (hb : 0 < b) (hbpi : b < Real.pi) (v c : ℝ) (F : (Fin N → ℂ) → ℂ) :
    protectedGraphMultiIntegral b v c N F =
      realPieceGraphMultiIntegral b v N (fun q => F (fun i => scalarGraph b v (q i) c)) := by
  induction N with
  | zero =>
    simp only [protectedGraphMultiIntegral, realPieceGraphMultiIntegral]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    rw [protectedGraphMultiIntegral, protectedGraphIntegral_eq_graph hb hbpi]
    simp only [ih, realPieceGraphMultiIntegral, realPieceGraphIntegral]
    have hcons (r : ℝ) (q : Fin n → ℝ) :
        (fun i => scalarGraph b v ((Fin.cons r q : Fin (n+1) → ℝ) i) c) =
          Fin.cons (scalarGraph b v r c) (fun i => scalarGraph b v (q i) c) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    simp only [hcons]

theorem realPieceGraphIntegral_congr {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi)
    (v : ℝ) {F G : ℝ → ℂ} (h : EqOn F G (Icc (-Real.pi) Real.pi)) :
    realPieceGraphIntegral b v F = realPieceGraphIntegral b v G := by
  unfold realPieceGraphIntegral
  congr 1
  · congr 1
    · apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le (by linarith : -Real.pi ≤ -b)] at hr
      dsimp only
      rw [h ⟨hr.1,hr.2.trans (by linarith)⟩]
    · apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le (by linarith : -b ≤ b)] at hr
      dsimp only
      rw [h ⟨(by linarith : -Real.pi ≤ -b).trans hr.1,hr.2.trans hbpi.le⟩]
  · apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hbpi.le] at hr
    dsimp only
    rw [h ⟨(by linarith : -Real.pi ≤ b).trans hr.1,hr.2⟩]

theorem realPieceGraphMultiIntegral_congr (N : ℕ) {b : ℝ}
    (hb : 0 < b) (hbpi : b < Real.pi) (v : ℝ) {F G : (Fin N → ℝ) → ℂ}
    (h : EqOn F G (realAngleBox N)) :
    realPieceGraphMultiIntegral b v N F = realPieceGraphMultiIntegral b v N G := by
  induction N with
  | zero =>
    exact h ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    apply realPieceGraphIntegral_congr hb hbpi v
    intro r hr
    apply ih
    intro q hq
    apply h
    constructor <;> intro i
    · exact Fin.cases hr.1 (fun j => hq.1 j) i
    · exact Fin.cases hr.2 (fun j => hq.2 j) i

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_realPieceGraphIntegral
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]
    {U : Set P} (hU : IsOpen U) {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi) (v : ℝ)
    (H : P → ℝ → ℂ) (hH : ContinuousOn (Function.uncurry H) (U ×ˢ univ)) :
    ContinuousOn (fun p => realPieceGraphIntegral b v (H p)) U := by
  have hcont (l r : ℝ) (hlr : l ≤ r) (J : ℂ) :
      ContinuousOn (fun p => ∫ u : ℝ in l..r, H p u*J) U :=
    continuousOn_parametric_intervalIntegral hU l r hlr (fun p u => H p u*J)
      ((hH.mul continuousOn_const).mono (Set.prod_mono (Subset.refl _) (subset_univ _)))
  exact ((hcont (-Real.pi) (-b) (by linarith) _).add
    (hcont (-b) b (by linarith) _)).add (hcont b Real.pi hbpi.le _)

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_realPieceGraphMultiIntegral (N : ℕ)
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]
    {U : Set P} (hU : IsOpen U) {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi) (v : ℝ)
    (H : P → (Fin N → ℝ) → ℂ)
    (hH : ContinuousOn (Function.uncurry H) (U ×ˢ univ)) :
    ContinuousOn (fun p => realPieceGraphMultiIntegral b v N (H p)) U := by
  induction N generalizing P with
  | zero =>
    exact hH.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun p hp => ⟨hp,mem_univ _⟩)
  | succ n ih =>
    apply continuousOn_realPieceGraphIntegral hU hb hbpi v
    apply ih (hU.prod isOpen_univ) (fun p : P × ℝ => fun q => H p.1 (Fin.cons p.2 q))
    change ContinuousOn ((Function.uncurry H) ∘
      (fun p : (P × ℝ) × (Fin n → ℝ) => (p.1.1, Fin.cons p.1.2 p.2))) _
    apply hH.comp
    · exact (by fun_prop : Continuous (fun p : (P × ℝ) × (Fin n → ℝ) =>
        (p.1.1, (Fin.cons p.1.2 p.2 : Fin (n+1) → ℝ)))).continuousOn
    · intro p hp
      exact ⟨hp.1.1,mem_univ _⟩

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_realPieceGraphIntegral {U : Set ℂ} (hU : IsOpen U)
    {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi) (v : ℝ)
    (H K : ℂ → ℝ → ℂ)
    (hH : ContinuousOn (Function.uncurry H) (U ×ˢ univ))
    (hK : ContinuousOn (Function.uncurry K) (U ×ˢ univ))
    (hd : ∀ s∈U, ∀ r, HasDerivAt (fun z => H z r) (K s r) s)
    {s : ℂ} (hs : s∈U) :
    HasDerivAt (fun z => realPieceGraphIntegral b v (H z))
      (realPieceGraphIntegral b v (K s)) s := by
  have hstep (l r : ℝ) (hlr : l ≤ r) (J : ℂ) :
      HasDerivAt (fun z => ∫ u : ℝ in l..r, H z u*J)
        (∫ u : ℝ in l..r, K s u*J) s := by
    have hh := IsingBulk.First.hasDerivAt_compact_integral (μ := volume) (K := Icc l r) isCompact_Icc
      (hU.mem_nhds hs) (fun z u => H z u*J) (fun z u => K z u*J)
      ((hH.mul continuousOn_const).mono (Set.prod_mono (Subset.refl _) (subset_univ _)))
      ((hK.mul continuousOn_const).mono (Set.prod_mono (Subset.refl _) (subset_univ _)))
      (fun z hz u _ => (hd z hz u).mul_const J)
    simpa only [intervalIntegral.integral_of_le hlr, ← integral_Icc_eq_integral_Ioc] using hh
  exact ((hstep (-Real.pi) (-b) (by linarith) _).add
    (hstep (-b) b (by linarith) _)).add (hstep b Real.pi hbpi.le _)

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_realPieceGraphMultiIntegral (N : ℕ) {U : Set ℂ} (hU : IsOpen U)
    {b : ℝ} (hb : 0 < b) (hbpi : b < Real.pi) (v : ℝ)
    (H K : ℂ → (Fin N → ℝ) → ℂ)
    (hH : ContinuousOn (Function.uncurry H) (U ×ˢ univ))
    (hK : ContinuousOn (Function.uncurry K) (U ×ˢ univ))
    (hd : ∀ s∈U, ∀ q, HasDerivAt (fun z => H z q) (K s q) s)
    {s : ℂ} (hs : s∈U) :
    HasDerivAt (fun z => realPieceGraphMultiIntegral b v N (H z))
      (realPieceGraphMultiIntegral b v N (K s)) s := by
  induction N generalizing s with
  | zero => exact hd s hs Fin.elim0
  | succ n ih =>
    have hcont (L : ℂ → (Fin (n+1) → ℝ) → ℂ)
        (hL : ContinuousOn (Function.uncurry L) (U ×ˢ univ)) :
        ContinuousOn (fun p : ℂ × ℝ => realPieceGraphMultiIntegral b v n
          (fun q => L p.1 (Fin.cons p.2 q))) (U ×ˢ univ) := by
      apply continuousOn_realPieceGraphMultiIntegral n (hU.prod isOpen_univ) hb hbpi v
        (fun p : ℂ × ℝ => fun q => L p.1 (Fin.cons p.2 q))
      change ContinuousOn ((Function.uncurry L) ∘
        (fun p : (ℂ × ℝ) × (Fin n → ℝ) => (p.1.1, Fin.cons p.1.2 p.2))) _
      exact hL.comp (by fun_prop) (fun p hp => ⟨hp.1.1,mem_univ _⟩)
    apply hasDerivAt_realPieceGraphIntegral hU hb hbpi v
      (fun z r => realPieceGraphMultiIntegral b v n (fun q => H z (Fin.cons r q)))
      (fun z r => realPieceGraphMultiIntegral b v n (fun q => K z (Fin.cons r q)))
      (hcont H hH) (hcont K hK) _ hs
    intro z hz r
    apply ih (fun z q => H z (Fin.cons r q)) (fun z q => K z (Fin.cons r q))
    · change ContinuousOn ((Function.uncurry H) ∘
        (fun p : ℂ × (Fin n → ℝ) => (p.1, Fin.cons r p.2))) _
      exact hH.comp (by fun_prop) (fun p hp => ⟨hp.1,mem_univ _⟩)
    · change ContinuousOn ((Function.uncurry K) ∘
        (fun p : ℂ × (Fin n → ℝ) => (p.1, Fin.cons r p.2))) _
      exact hK.comp (by fun_prop) (fun p hp => ⟨hp.1,mem_univ _⟩)
    · exact fun t ht q => hd t ht (Fin.cons r q)
    · exact hz

def realAngleClamp (r : ℝ) : ℝ :=
  Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) r

theorem realAngleClamp_mem (r : ℝ) : realAngleClamp r ∈ Icc (-Real.pi) Real.pi :=
  (Set.projIcc (-Real.pi) Real.pi (by linarith [Real.pi_pos]) r).property

theorem realAngleClamp_eq {r : ℝ} (hr : r∈Icc (-Real.pi) Real.pi) : realAngleClamp r=r := by
  simp only [realAngleClamp, Set.projIcc_of_mem _ hr]

theorem realAngleClamp_continuous : Continuous realAngleClamp :=
  continuous_subtype_val.comp continuous_projIcc

def clampedGraphAngles {N : ℕ} (b v c : ℝ) (q : Fin N → ℝ) : Fin N → ℂ :=
  fun i => scalarGraph b v (realAngleClamp (q i)) c

theorem clampedGraphAngles_continuous (N : ℕ) {b : ℝ}
    (hb : 0 < b) (hbpi : b < Real.pi) (v c : ℝ) :
    Continuous (@clampedGraphAngles N b v c) := by
  have hf := contourDisplacement_continuous hb.le hbpi
  apply continuous_pi
  intro i
  have hr : Continuous (fun q : Fin N → ℝ => realAngleClamp (q i)) :=
    realAngleClamp_continuous.comp (continuous_apply i)
  exact (Complex.continuous_ofReal.comp hr).add
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul ((hf.comp hr).sub continuous_const))))

/- Analyticity of the genuine complete piecewise graph integral. The
proof differentiates its actual compact parameter integrals and constructs
the integrated derivative; no holomorphy of the integral is an input. -/
set_option backward.isDefEq.respectTransparency false in
theorem protectedGraphMultiIntegral_analyticOnNhd (N : ℕ) {b : ℝ}
    (hb : 0 < b) (hbpi : b < Real.pi) (v c : ℝ)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ × (Fin N → ℂ) → ℂ)
    (hF : ∀ E∈U, ∀ q∈realAngleBox N,
      AnalyticAt ℂ F (E, fun i => scalarGraph b v (q i) c)) :
    AnalyticOnNhd ℂ (fun E => protectedGraphMultiIntegral b v c N (fun q => F (E,q))) U := by
  let H : ℕ → ℂ → (Fin N → ℝ) → ℂ :=
    fun j E q => IsingBulk.First.jointParameterJet F j (E,clampedGraphAngles b v c q)
  have hs (E : ℂ) (hE : E∈U) (q : Fin N → ℝ) :
      AnalyticAt ℂ F (E,clampedGraphAngles b v c q) := by
    apply hF E hE (fun i => realAngleClamp (q i))
    exact ⟨fun i => (realAngleClamp_mem (q i)).1,fun i => (realAngleClamp_mem (q i)).2⟩
  have hg : Continuous (fun p : ℂ × (Fin N → ℝ) => (p.1,clampedGraphAngles b v c p.2)) :=
    continuous_fst.prodMk ((clampedGraphAngles_continuous N hb hbpi v c).comp continuous_snd)
  have hc (j : ℕ) : ContinuousOn (Function.uncurry (H j)) (U ×ˢ univ) := by
    intro p hp
    exact ((IsingBulk.First.jointParameterJet_analyticAt (hs p.1 hp.1 p.2) j).continuousAt.comp
      (f := fun p : ℂ × (Fin N → ℝ) => (p.1,clampedGraphAngles b v c p.2))
      hg.continuousAt).continuousWithinAt
  have hd (j : ℕ) (E : ℂ) (hE : E∈U) (q : Fin N → ℝ) :
      HasDerivAt (fun z => H j z q) (H (j+1) E q) E := by
    have ha := (IsingBulk.First.jointParameterJet_analyticAt (hs E hE q) j).comp
      (f := fun z : ℂ => (z,clampedGraphAngles b v c q)) (analyticAt_id.prod analyticAt_const)
    convert ha.differentiableAt.hasDerivAt using 1 <;>
      simp only [H, IsingBulk.First.jointParameterJet, Function.iterate_succ',
        Function.comp_def, IsingBulk.First.parameterDeriv]
  have hI : AnalyticOnNhd ℂ (fun E => realPieceGraphMultiIntegral b v N (H 0 E)) U := by
    intro E hE
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [hU.mem_nhds hE] with z hz
    exact (hasDerivAt_realPieceGraphMultiIntegral N hU hb hbpi v (H 0) (H 1)
      (hc 0) (hc 1) (hd 0) hz).differentiableAt
  have he : (fun E => protectedGraphMultiIntegral b v c N (fun q => F (E,q))) =
      fun E => realPieceGraphMultiIntegral b v N (H 0 E) := by
    funext E
    rw [protectedGraphMultiIntegral_eq_realPiece N hb hbpi]
    apply realPieceGraphMultiIntegral_congr N hb hbpi v
    intro q hq
    change F (E,fun i => scalarGraph b v (q i) c) = F (E,clampedGraphAngles b v c q)
    congr 1
    congr 1
    funext i
    rw [clampedGraphAngles,realAngleClamp_eq ⟨hq.1 i,hq.2 i⟩]
  rw [he]
  exact hI

end
end IsoProof
