import IsoProof.DifferentialFlatten
import IsoProof.DifferentialOrder
import IsoProof.SeparantMinimality
import IsoProof.BoundaryZeroTrace

/-! Analytic and limiting steps of the separant argument.  The functions in
this file are genuine iterated complex derivatives.  Boundary hypotheses here
are explicit inputs to a general analytic criterion; they are not asserted as
facts about the susceptibility without a separate producer. -/
namespace IsoProof
noncomputable section
open Filter MvPolynomial Set
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem analyticAt_iteratedDeriv {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (j : ℕ) : AnalyticAt ℂ (iteratedDeriv j f) z := by
  simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv j

theorem evaluate_formalDerivative_eq_deriv (P : DifferentialPolynomial)
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    evaluateDifferentialPolynomial (formalDerivative P) f z =
      deriv (evaluateDifferentialPolynomial P f) z := by
  exact (hasDerivAt_evaluateDifferentialPolynomial P f
    (fun j => (analyticAt_iteratedDeriv hf j).differentiableAt)).deriv.symm

theorem formalDerivative_preserves_zero_germ {P : DifferentialPolynomial}
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hP : evaluateDifferentialPolynomial P f =ᶠ[𝓝 a] (fun _ => 0)) :
    evaluateDifferentialPolynomial (formalDerivative P) f =ᶠ[𝓝 a] (fun _ => 0) := by
  have hder := hP.deriv
  filter_upwards [hf.eventually_analyticAt, hder] with z hfz hdz
  rw [evaluate_formalDerivative_eq_deriv P hfz, hdz]
  exact deriv_const z 0

theorem iterated_formalDerivative_zero_germ {P : DifferentialPolynomial}
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hP : evaluateDifferentialPolynomial P f =ᶠ[𝓝 a] (fun _ => 0)) (m : ℕ) :
    evaluateDifferentialPolynomial ((formalDerivative^[m]) P) f =ᶠ[𝓝 a]
      (fun _ => 0) := by
  induction m with
  | zero => exact hP
  | succ m ih =>
      simpa only [Function.iterate_succ_apply'] using
        formalDerivative_preserves_zero_germ hf ih

theorem differential_relation_global {D : Set ℂ} {f : ℂ → ℂ} {a : ℂ}
    (hD : IsPreconnected D) (ha : a ∈ D) (hf : AnalyticOnNhd ℂ f D)
    {P : DifferentialPolynomial}
    (hP : evaluateDifferentialPolynomial P f =ᶠ[𝓝 a] (fun _ => 0)) :
    EqOn (evaluateDifferentialPolynomial P f) 0 D := by
  have han : AnalyticOnNhd ℂ (evaluateDifferentialPolynomial P f) D :=
    fun z hz => polynomial_jet_evaluation_analyticAt P (hf z hz)
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD ha hP

theorem iterated_formalDerivative_zero_on {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hf : AnalyticOnNhd ℂ f D) {P : DifferentialPolynomial}
    (hP : EqOn (evaluateDifferentialPolynomial P f) 0 D) (m : ℕ) :
    EqOn (evaluateDifferentialPolynomial ((formalDerivative^[m]) P) f) 0 D := by
  intro z hz
  apply Filter.EventuallyEq.eq_of_nhds
  apply iterated_formalDerivative_zero_germ (hf z hz)
  filter_upwards [hD.mem_nhds hz] with w hw
  exact hP hw

/-- Boundedness is only eventual along the approach filter. -/
def NormBoundedAlong {α : Type*} (l : Filter α) (g : α → ℂ) : Prop :=
  ∃ C : ℝ, ∀ᶠ t in l, ‖g t‖ ≤ C

theorem NormBoundedAlong.add {α : Type*} {l : Filter α} {g h : α → ℂ}
    (hg : NormBoundedAlong l g) (hh : NormBoundedAlong l h) :
    NormBoundedAlong l (fun t => g t + h t) := by
  obtain ⟨C, hC⟩ := hg
  obtain ⟨D, hD⟩ := hh
  refine ⟨C+D, ?_⟩
  filter_upwards [hC,hD] with t ht ht'
  exact (norm_add_le _ _).trans (add_le_add ht ht')

theorem NormBoundedAlong.mul {α : Type*} {l : Filter α} {g h : α → ℂ}
    (hg : NormBoundedAlong l g) (hh : NormBoundedAlong l h) :
    NormBoundedAlong l (fun t => g t * h t) := by
  obtain ⟨C, hC⟩ := hg
  obtain ⟨D, hD⟩ := hh
  refine ⟨|C| * |D|, ?_⟩
  filter_upwards [hC,hD] with t ht ht'
  rw [norm_mul]
  exact mul_le_mul (ht.trans (le_abs_self C)) (ht'.trans (le_abs_self D))
    (norm_nonneg _) (abs_nonneg _)

theorem normBoundedAlong_of_tendsto {α : Type*} {l : Filter α} {g : α → ℂ} {v : ℂ}
    (hg : Tendsto g l (𝓝 v)) : NormBoundedAlong l g := by
  refine ⟨‖v‖+1, ?_⟩
  exact ((hg.norm).eventually (eventually_lt_nhds (by linarith : ‖v‖ < ‖v‖+1))).mono
    (fun _ h => h.le)

/-- Bounded lower jets give bounded value for every polynomial using only
those jets.  The supported-subalgebra proof keeps the order restriction. -/
theorem polynomial_boundedAlong {α : Type*} {l : Filter α}
    {u : ℕ → α → ℂ} {P : DifferentialPolynomial} {n : ℕ}
    (hP : VariableBound P n) (hu : ∀ i ≤ n, NormBoundedAlong l (u i)) :
    NormBoundedAlong l (fun t => MvPolynomial.eval (fun i => u i t) P) := by
  change P ∈ Algebra.adjoin ℂ (MvPolynomial.X '' Iic n) at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx
      simpa only [MvPolynomial.eval_X] using hu i hi
  | algebraMap c =>
      refine ⟨‖c‖, Eventually.of_forall ?_⟩
      intro t
      simp only [MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, le_refl]
  | add P Q hP hQ ihP ihQ =>
      simpa only [map_add] using ihP.add ihQ
  | mul P Q hP hQ ihP ihQ =>
      simpa only [map_mul] using ihP.mul ihQ

/-- A nonzero limiting coefficient cannot multiply an unbounded jet and be
cancelled by a bounded remainder. -/
theorem coefficient_limit_zero_of_unbounded {α : Type*} {l : Filter α} [NeBot l]
    {S V R : α → ℂ} {s₀ : ℂ}
    (hS : Tendsto S l (𝓝 s₀)) (hV : Tendsto (fun t => ‖V t‖) l atTop)
    (hR : NormBoundedAlong l R)
    (hrel : ∀ᶠ t in l, S t * V t + R t = 0) : s₀ = 0 := by
  by_contra hne
  have hd : 0 < ‖s₀‖/2 := half_pos (norm_pos_iff.mpr hne)
  obtain ⟨C,hC⟩ := hR
  have hSl : ∀ᶠ t in l, ‖s₀‖/2 < ‖S t‖ :=
    hS.norm.eventually (eventually_gt_nhds (by linarith))
  have hVl : ∀ᶠ t in l, (|C|+1)/(‖s₀‖/2) < ‖V t‖ :=
    hV.eventually (eventually_gt_atTop _)
  have hfalse : ∀ᶠ t in l, False := by
    filter_upwards [hSl,hVl,hC,hrel] with t hs hv hr hzero
    have he : ‖S t‖*‖V t‖=‖R t‖ := by
      have hz : S t*V t = -R t := add_eq_zero_iff_eq_neg.mp hzero
      simpa only [norm_mul,norm_neg] using congrArg norm hz
    have hm : |C|+1 < ‖V t‖*(‖s₀‖/2) := (div_lt_iff₀ hd).mp hv
    have hm' : (‖s₀‖/2)*‖V t‖ ≤ ‖S t‖*‖V t‖ :=
      mul_le_mul_of_nonneg_right hs.le (norm_nonneg _)
    have hc : C ≤ |C| := le_abs_self C
    nlinarith
  obtain ⟨t,ht⟩ := hfalse.exists
  exact ht

/-- The actual differentiated relation forces its separant's limit to zero
at every sharp singularity of strictly higher order. -/
theorem separant_limit_zero {α : Type*} {l : Filter α} [NeBot l]
    {D : Set ℂ} {f : ℂ → ℂ} {P : DifferentialPolynomial} {n k : ℕ}
    (hD : IsOpen D) (hf : AnalyticOnNhd ℂ f D)
    (hP : EqOn (evaluateDifferentialPolynomial P f) 0 D)
    (hn : 1 ≤ n) (hPn : VariableBound P n) (hnk : n ≤ k)
    {path : α → ℂ} (hpath : ∀ᶠ t in l, path t ∈ D)
    (hcoord : NormBoundedAlong l path)
    (hlower : ∀ j < k, NormBoundedAlong l (fun t => iteratedDeriv j f (path t)))
    (hsharp : Tendsto (fun t => ‖iteratedDeriv k f (path t)‖) l atTop)
    {S₀ : ℂ}
    (hsep : Tendsto (fun t => evaluateDifferentialPolynomial
      (MvPolynomial.pderiv n P) f (path t)) l (𝓝 S₀)) : S₀ = 0 := by
  obtain ⟨R,hR,hidentity⟩ := iterated_formalDerivative_split P hn hPn (k-n)
  have hnk' : n+(k-n)=k := Nat.add_sub_of_le hnk
  rw [hnk'] at hR hidentity
  apply coefficient_limit_zero_of_unbounded
    (R := fun t => evaluateDifferentialPolynomial R f (path t)) hsep hsharp
  · apply polynomial_boundedAlong (u := fun i t => jetEvaluation f (path t) i) hR
    intro i hi
    cases i with
    | zero => simpa only [jetEvaluation] using hcoord
    | succ j => simpa only [jetEvaluation] using hlower j (by omega)
  · have heq := iterated_formalDerivative_zero_on hD hf hP (k-n+1)
    filter_upwards [hpath] with t ht
    have hz := heq ht
    rw [hidentity] at hz
    simpa only [evaluateDifferentialPolynomial, map_add, map_mul,
      MvPolynomial.eval_X, jetEvaluation, Pi.zero_apply] using hz

end
end IsoProof
