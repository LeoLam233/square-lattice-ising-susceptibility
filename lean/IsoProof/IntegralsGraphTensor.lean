import IsoProof.IntegralsGraphFubini
import IsoProof.IntegralsGraphTransport

/-! Finite-dimensional tensor transport of the full coupled site density.
Fubini is used only with continuity on actual compact parameter boxes. -/
namespace IsoProof
noncomputable section
open Set MeasureTheory

def realAngleBox (N : ℕ) : Set (Fin N → ℝ) :=
  Icc (fun _ => -Real.pi) (fun _ => Real.pi)

def graphHomotopySet (b v c : ℝ) : Set ℂ :=
  {z | ∃ t∈Icc 0 v, ∃ r∈Icc (-Real.pi) Real.pi, z=scalarGraph b t r c}

theorem real_mem_graphHomotopySet {v r : ℝ} (hv : 0 ≤ v)
    (hr : r ∈ Icc (-Real.pi) Real.pi) (b c : ℝ) :
    (r : ℂ) ∈ graphHomotopySet b v c := by
  refine ⟨0,⟨le_rfl,hv⟩,r,hr,?_⟩
  simp [scalarGraph]

def protectedGraphMultiIntegral (b v c : ℝ) :
    (N : ℕ) → ((Fin N → ℂ) → ℂ) → ℂ
  | 0, F => F Fin.elim0
  | n+1, F => protectedGraphIntegral
      (fun z => protectedGraphMultiIntegral b v c n (fun q => F (Fin.cons z q))) b v c

set_option backward.isDefEq.respectTransparency false in
theorem realAngleBox_integral_succ (n : ℕ) (F : (Fin (n+1) → ℝ) → ℂ)
    (hF : ContinuousOn F (realAngleBox (n+1))) :
    (∫ q in realAngleBox (n+1), F q) = ∫ q in realAngleBox n,
      ∫ u : ℝ in (-Real.pi)..Real.pi, F (Fin.cons u q) := by
  let e : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n+1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm _
  have he : ∀ p : ℝ × (Fin n → ℝ), e p=Fin.cons p.1 p.2 := by
    intro p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hbox : e ⁻¹' realAngleBox (n+1) =
      Icc (-Real.pi) Real.pi ×ˢ realAngleBox n := by
    ext p
    simp only [mem_preimage, he, realAngleBox, mem_Icc, mem_prod]
    constructor
    · intro hp
      exact ⟨⟨hp.1 0,hp.2 0⟩,⟨fun i => hp.1 i.succ,fun i => hp.2 i.succ⟩⟩
    · intro hp
      constructor <;> intro i
      · exact Fin.cases hp.1.1 (fun j => hp.2.1 j) i
      · exact Fin.cases hp.1.2 (fun j => hp.2.2 j) i
  have hcomp : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => F (e p))
      (Icc (-Real.pi) Real.pi ×ˢ realAngleBox n) := by
    apply hF.comp
    · have hc : Continuous (fun p : ℝ × (Fin n → ℝ) => e p) := by
        simp only [he]
        fun_prop
      exact hc.continuousOn
    · intro p hp
      rw [← hbox] at hp
      exact hp
  have hi : IntegrableOn (fun p => F (e p))
      (Icc (-Real.pi) Real.pi ×ˢ realAngleBox n) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hcomp.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [← hem.map_eq, setIntegral_map_equiv, hbox, Measure.volume_eq_prod,
    IsingBulk.First.setIntegral_prod_reverse volume volume _ _ _ hi]
  apply setIntegral_congr_fun measurableSet_Icc
  intro q _
  dsimp only
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u _
  dsimp only
  rw [he]

theorem complex_cons_update_succ {n : ℕ} (z : ℂ) (q : Fin n → ℂ) (i : Fin n) (w : ℂ) :
    (Fin.cons z (Function.update q i w) : Fin (n+1) → ℂ) =
      Function.update (Fin.cons z q) i.succ w := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  · by_cases hk : k=i
    · subst k
      simp
    · simp [Fin.succ_inj,hk]

theorem complex_cons_update_zero {n : ℕ} (z : ℂ) (q : Fin n → ℂ) (w : ℂ) :
    Function.update (Fin.cons z q : Fin (n+1) → ℂ) 0 w = Fin.cons w q := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp

set_option backward.isDefEq.respectTransparency false in
theorem analyticAt_complex_cons_head {n : ℕ} (q : Fin n → ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => (Fin.cons w q : Fin (n+1) → ℂ)) z := by
  apply analyticAt_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i
  · exact analyticAt_id
  · exact analyticAt_const

set_option backward.isDefEq.respectTransparency false in
theorem analyticAt_complex_cons_tail {n : ℕ} (z : ℂ) (q : Fin n → ℂ) :
    AnalyticAt ℂ (fun w : Fin n → ℂ => (Fin.cons z w : Fin (n+1) → ℂ)) q := by
  apply analyticAt_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact analyticAt_const
  · exact (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt q

set_option backward.isDefEq.respectTransparency false in
theorem realAngleBox_eq_protectedGraphMultiIntegral (N : ℕ) {b v c : ℝ}
    (hb : 0 < b) (hbpi : b < Real.pi) (hv : 0 ≤ v)
    (F : (Fin N → ℂ) → ℂ)
    (hF : ∀ q, (∀ i, q i ∈ graphHomotopySet b v c) → AnalyticAt ℂ F q)
    (hp : ∀ q i, F (Function.update q i (q i+2*(Real.pi : ℂ)))=F q) :
    (∫ q in realAngleBox N, F (fun i => (q i : ℂ))) =
      protectedGraphMultiIntegral b v c N F := by
  classical
  induction N with
  | zero =>
    rw [Measure.volume_pi_eq_dirac (Fin.elim0 : Fin 0 → ℝ), setIntegral_dirac]
    have he : (Fin.elim0 : Fin 0 → ℝ) ∈ realAngleBox 0 := by
      constructor <;> intro i <;> exact Fin.elim0 i
    simp only [he, ite_true, protectedGraphMultiIntegral]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    have hflat : ContinuousOn (fun q : Fin (n+1) → ℝ => F (fun i => (q i : ℂ)))
        (realAngleBox (n+1)) := by
      intro q hq
      exact ((hF _ (fun i => real_mem_graphHomotopySet hv ⟨hq.1 i,hq.2 i⟩ b c)).continuousAt.comp
        (continuous_pi (fun i => Complex.continuous_ofReal.comp (continuous_apply i))).continuousAt).continuousWithinAt
    rw [realAngleBox_integral_succ n _ hflat]
    have hconsCast (u : ℝ) (q : Fin n → ℝ) :
        (fun i => ((Fin.cons u q : Fin (n+1) → ℝ) i : ℂ)) =
          Fin.cons (u : ℂ) (fun i => (q i : ℂ)) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    simp only [hconsCast]
    calc
      _ = ∫ q in realAngleBox n,
          protectedGraphIntegral (fun z => F (Fin.cons z (fun i => (q i : ℂ)))) b v c := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro q hq
        symm
        apply protectedGraphIntegral_eq_real hb hbpi hv
        · intro z
          simpa only [Fin.cons_zero, complex_cons_update_zero] using
            hp (Fin.cons z (fun i => (q i : ℂ))) 0
        · intro t ht r hr
          apply AnalyticAt.differentiableAt
          apply (hF _ ?_).comp (analyticAt_complex_cons_head _ _)
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact ⟨t,ht,r,hr,rfl⟩
          · exact real_mem_graphHomotopySet hv ⟨hq.1 j,hq.2 j⟩ b c
      _ = protectedGraphIntegral
          (fun z => ∫ q in realAngleBox n, F (Fin.cons z (fun i => (q i : ℂ)))) b v c := by
        apply protectedGraphIntegral_box_fubini isCompact_Icc hb hbpi v c
        intro p hp'
        have ha : AnalyticAt ℂ F (Fin.cons (scalarGraph b v p.1 c) (fun i => (p.2 i : ℂ))) := by
          apply hF
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact ⟨v,⟨hv,le_rfl⟩,p.1,hp'.1,rfl⟩
          · exact real_mem_graphHomotopySet hv ⟨hp'.2.1 j,hp'.2.2 j⟩ b c
        have hg : Continuous (fun p : ℝ × (Fin n → ℝ) =>
            (Fin.cons (scalarGraph b v p.1 c) (fun i => (p.2 i : ℂ)) : Fin (n+1) → ℂ)) := by
          have hf := contourDisplacement_continuous hb.le hbpi
          apply continuous_pi
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact (Complex.continuous_ofReal.comp continuous_fst).add
              (continuous_const.mul (Complex.continuous_ofReal.comp
                (continuous_const.mul ((hf.comp continuous_fst).sub continuous_const))))
          · exact Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_snd)
        exact (ha.continuousAt.comp (f := fun p : ℝ × (Fin n → ℝ) =>
          (Fin.cons (scalarGraph b v p.1 c) (fun i => (p.2 i : ℂ)) : Fin (n+1) → ℂ))
          hg.continuousAt).continuousWithinAt
      _ = _ := by
        unfold protectedGraphMultiIntegral
        apply protectedGraphIntegral_congr hb hbpi v c
        intro r hr
        apply ih (fun q : Fin n → ℂ => F (Fin.cons (scalarGraph b v r c) q))
        · intro q hq
          apply (hF _ ?_).comp (analyticAt_complex_cons_tail _ q)
          intro i
          refine Fin.cases ?_ (fun j => hq j) i
          exact ⟨v,⟨hv,le_rfl⟩,r,hr,rfl⟩
        · intro q i
          rw [complex_cons_update_succ]
          exact hp (Fin.cons (scalarGraph b v r c) q) i.succ

end
end IsoProof
