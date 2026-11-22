import IsoProof.RationalGerms
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Flattening polynomial coefficients adds the actual independent variable,
without identifying distinct differential polynomials.  This supplies the
precise denominator-clearing equivalence for analytic function germs. -/
namespace IsoProof
noncomputable section
open Filter MvPolynomial
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def finiteJetIndex (r : ℕ) : Option (Fin (r+1)) → ℕ
  | none => 0
  | some j => j.val+1

theorem finiteJetIndex_injective (r : ℕ) : Function.Injective (finiteJetIndex r) := by
  intro i j h
  cases i <;> cases j <;> simp_all [finiteJetIndex]
  exact Fin.ext h

def flattenDifferentialPolynomial {r : ℕ}
    (Q : MvPolynomial (Fin (r+1)) (Polynomial ℂ)) : DifferentialPolynomial :=
  MvPolynomial.rename (finiteJetIndex r)
    ((MvPolynomial.optionEquivRight ℂ (Fin (r+1))).symm Q)

theorem flattenDifferentialPolynomial_ne_zero {r : ℕ}
    {Q : MvPolynomial (Fin (r+1)) (Polynomial ℂ)} (hQ : Q ≠ 0) :
    flattenDifferentialPolynomial Q ≠ 0 := by
  apply (MvPolynomial.rename_injective _ (finiteJetIndex_injective r)).ne
    ((MvPolynomial.optionEquivRight ℂ (Fin (r+1))).symm.injective.ne hQ)

theorem finiteJetIndex_evaluation {r : ℕ}
    (Q : MvPolynomial (Option (Fin (r+1))) ℂ) (f : ℂ → ℂ) (z : ℂ) :
    MvPolynomial.eval (jetEvaluation f z) (MvPolynomial.rename (finiteJetIndex r) Q) =
      MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin (r+1) => iteratedDeriv j.val f z)
        (MvPolynomial.optionEquivRight ℂ (Fin (r+1)) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, MvPolynomial.eval₂_add, hP, hQ]
  | mul_X P i hP =>
      cases i with
      | none => simp [map_mul, MvPolynomial.eval₂_mul, hP,
          finiteJetIndex, jetEvaluation]
      | some j => simp [map_mul, MvPolynomial.eval₂_mul, hP,
          finiteJetIndex, jetEvaluation]

theorem flattenDifferentialPolynomial_evaluation {r : ℕ}
    (Q : MvPolynomial (Fin (r+1)) (Polynomial ℂ)) (f : ℂ → ℂ) (z : ℂ) :
    evaluateDifferentialPolynomial (flattenDifferentialPolynomial Q) f z =
      MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin (r+1) => iteratedDeriv j.val f z) Q := by
  simpa only [evaluateDifferentialPolynomial, flattenDifferentialPolynomial,
    AlgEquiv.apply_symm_apply] using
    finiteJetIndex_evaluation ((MvPolynomial.optionEquivRight ℂ (Fin (r+1))).symm Q) f z

theorem polynomialDifferentialGerm_eq {r : ℕ} (a : ℂ) (f : ℂ → ℂ)
    (Q : MvPolynomial (Fin (r+1)) (Polynomial ℂ)) :
    polynomialDifferentialGerm a f Q =
      (fun z => MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin (r+1) => iteratedDeriv j.val f z) Q : PuncturedGerm a) := by
  induction Q using MvPolynomial.induction_on with
  | C p =>
      simpa only [polynomialDifferentialGerm, MvPolynomial.eval₂_C,
        polynomialCoefficientGerm, RingHom.coe_comp, Function.comp_apply,
        ] using! rationalGerm_polynomial a p
  | add P Q hP hQ =>
      simpa only [polynomialDifferentialGerm, MvPolynomial.eval₂_add,
        ← Filter.Germ.coe_add] using! congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
      simpa only [polynomialDifferentialGerm, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X, ← Filter.Germ.coe_mul] using!
        congrArg (fun x : PuncturedGerm a => x *
          (iteratedDeriv i.val f : PuncturedGerm a)) hP

theorem polynomialDifferentialGerm_flatten {r : ℕ} (a : ℂ) (f : ℂ → ℂ)
    (Q : MvPolynomial (Fin (r+1)) (Polynomial ℂ)) :
    polynomialDifferentialGerm a f Q =
      (evaluateDifferentialPolynomial (flattenDifferentialPolynomial Q) f :
        PuncturedGerm a) := by
  rw [polynomialDifferentialGerm_eq]
  congr 1
  funext z
  exact (flattenDifferentialPolynomial_evaluation Q f z).symm

/-- Every finite-support differential polynomial is a polynomial-coefficient
finite jet, including the independent coordinate as a coefficient variable. -/
theorem exists_flattenDifferentialPolynomial (P : DifferentialPolynomial) :
    ∃ r : ℕ, ∃ Q : MvPolynomial (Fin (r+1)) (Polynomial ℂ),
      flattenDifferentialPolynomial Q = P := by
  classical
  let r := P.vars.sup id
  have hvars : (P.vars : Set ℕ) ⊆ Set.range (finiteJetIndex r) := by
    intro i hi
    cases i with
    | zero => exact ⟨none, rfl⟩
    | succ j =>
        have hj : j+1 ≤ r := Finset.le_sup (f := id) hi
        exact ⟨some ⟨j, by omega⟩, rfl⟩
  obtain ⟨P₀, hP₀⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    P (finiteJetIndex r) (finiteJetIndex_injective r) hvars
  refine ⟨r, MvPolynomial.optionEquivRight ℂ (Fin (r+1)) P₀, ?_⟩
  simpa only [flattenDifferentialPolynomial, AlgEquiv.symm_apply_apply] using hP₀

theorem polynomial_jet_evaluation_analyticAt (P : DifferentialPolynomial)
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (evaluateDifferentialPolynomial P f) a := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      change AnalyticAt ℂ (fun z => MvPolynomial.eval (jetEvaluation f z) (C c)) a
      simpa only [MvPolynomial.eval_C] using analyticAt_const (v := c)
  | add P Q hP hQ =>
      change AnalyticAt ℂ (fun z => MvPolynomial.eval (jetEvaluation f z) (P+Q)) a
      simpa only [map_add] using! hP.add hQ
  | mul_X P i hP =>
      have hi : AnalyticAt ℂ (fun z => jetEvaluation f z i) a := by
        cases i with
        | zero => simpa [jetEvaluation] using! analyticAt_id (𝕜 := ℂ) (z := a)
        | succ j =>
            simpa only [jetEvaluation, iteratedDeriv_eq_iterate] using hf.iterated_deriv j
      change AnalyticAt ℂ (fun z => MvPolynomial.eval (jetEvaluation f z) (P*X i)) a
      simpa only [map_mul, MvPolynomial.eval_X] using! hP.mul hi

theorem zero_germ_of_punctured_zero {g : ℂ → ℂ} {a : ℂ}
    (hg : ContinuousAt g a) (hz : g =ᶠ[𝓝[≠] a] (fun _ => 0)) :
    g =ᶠ[𝓝 a] (fun _ => 0) := by
  have ha : g a = 0 := tendsto_nhds_unique
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hz.symm)
  rw [← nhdsNE_sup_pure a]
  exact ⟨hz, by simpa using ha⟩

/-- The ordinary analytic-germ definition and the C(z)-coefficient punctured
definition are equivalent, with no assumption that coefficient denominators
avoid the base point. -/
theorem rational_relation_iff_polynomial_relation {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) :
    RationalDifferentialRelationAt f a ↔ PolynomialDifferentialRelationAt f a := by
  rw [rational_relation_iff_polynomial_coefficient_germ]
  constructor
  · rintro ⟨r, Q, hQ, hrel⟩
    refine ⟨flattenDifferentialPolynomial Q, flattenDifferentialPolynomial_ne_zero hQ, ?_⟩
    apply zero_germ_of_punctured_zero (polynomial_jet_evaluation_analyticAt _ hf).continuousAt
    apply Filter.Germ.coe_eq.mp
    change (evaluateDifferentialPolynomial (flattenDifferentialPolynomial Q) f :
      PuncturedGerm a) = 0
    simpa only [← polynomialDifferentialGerm_flatten] using hrel
  · rintro ⟨P, hP, hrel⟩
    obtain ⟨r, Q, hQ⟩ := exists_flattenDifferentialPolynomial P
    refine ⟨r, Q, ?_, ?_⟩
    · intro hz
      apply hP
      rw [← hQ, hz]
      simp [flattenDifferentialPolynomial]
    · rw [polynomialDifferentialGerm_flatten, hQ]
      exact Filter.Germ.coe_eq.mpr (hrel.filter_mono nhdsWithin_le_nhds)

end
end IsoProof
