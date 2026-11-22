import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! Actual differential polynomials and analytic evaluation for §5. Variable
zero is the independent coordinate; variable j+1 is the j-th derivative.
Finite support of an MvPolynomial supplies a finite derivative order. -/
namespace IsoProof
noncomputable section
open scoped BigOperators Topology
open Filter

abbrev DifferentialPolynomial := MvPolynomial ℕ ℂ

/-- Values of the coordinate and the genuine complex derivatives. -/
def jetEvaluation (f : ℂ → ℂ) (z : ℂ) : ℕ → ℂ
  | 0 => z
  | j+1 => iteratedDeriv j f z

def evaluateDifferentialPolynomial (P : DifferentialPolynomial) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  MvPolynomial.eval (jetEvaluation f z) P

/-- Nonzero means nonzero in the polynomial ring, before substitution. -/
def PolynomialDifferentialRelationAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ P : DifferentialPolynomial, P ≠ 0 ∧
    evaluateDifferentialPolynomial P f =ᶠ[𝓝 a] (fun _ => 0)

/-- Exact rational coefficient polynomials in a prescribed finite jet. -/
abbrev RationalDifferentialPolynomial (r : ℕ) :=
  MvPolynomial (Fin (r+1)) (RatFunc ℂ)

/-- Rational evaluation uses normalized numerator/denominator representatives;
it is only consumed away from their poles. -/
def evaluateRationalDifferentialPolynomial {r : ℕ}
    (P : RationalDifferentialPolynomial r) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ m ∈ P.support, RatFunc.eval (RingHom.id ℂ) z (P.coeff m) *
    m.prod (fun j n => (iteratedDeriv j.val f z)^n)

/-- Germ relation in C(z); a punctured neighborhood permits a coefficient pole
at the base point itself, as required for a relation over the meromorphic field. -/
def RationalDifferentialRelationAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ r : ℕ, ∃ P : RationalDifferentialPolynomial r, P ≠ 0 ∧
    evaluateRationalDifferentialPolynomial P f =ᶠ[𝓝[≠] a] (fun _ => 0)

def DifferentiallyTranscendentalAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ¬ RationalDifferentialRelationAt f a

/-- The algebraic derivation realizing d/dz on actual jets. -/
def jetVariableDerivative : ℕ → DifferentialPolynomial
  | 0 => 1
  | j+1 => MvPolynomial.X (j+2)

def formalDerivative : Derivation ℂ DifferentialPolynomial DifferentialPolynomial :=
  MvPolynomial.mkDerivation ℂ jetVariableDerivative

@[simp] theorem formalDerivative_coordinate :
    formalDerivative (MvPolynomial.X 0) = 1 := by
  simp [formalDerivative, MvPolynomial.mkDerivation_X, jetVariableDerivative]

@[simp] theorem formalDerivative_jet (j : ℕ) :
    formalDerivative (MvPolynomial.X (j+1)) = MvPolynomial.X (j+2) := by
  simp [formalDerivative, MvPolynomial.mkDerivation_X, jetVariableDerivative]

/-- A polynomial chain rule proved by polynomial induction. -/
theorem hasDerivAt_polynomial_evaluation
    (P : DifferentialPolynomial) (u : ℕ → ℂ → ℂ) (v : ℕ → DifferentialPolynomial)
    {z : ℂ} (hu : ∀ i, HasDerivAt (u i) (MvPolynomial.eval (fun j => u j z) (v i)) z) :
    HasDerivAt (fun w => MvPolynomial.eval (fun i => u i w) P)
      (MvPolynomial.eval (fun i => u i z) (MvPolynomial.mkDerivation ℂ v P)) z := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using! hasDerivAt_const z a
  | add P Q hP hQ => simpa only [map_add, Pi.add_apply] using! hP.add hQ
  | mul_X P i hP =>
      simpa only [map_mul, MvPolynomial.eval_X, Derivation.leibniz,
        smul_eq_mul, map_add, MvPolynomial.mkDerivation_X, Pi.mul_apply,
        add_comm, mul_comm] using! hP.mul (hu i)

/-- Formal differentiation agrees with the analytic derivative. -/
theorem hasDerivAt_evaluateDifferentialPolynomial
    (P : DifferentialPolynomial) (f : ℂ → ℂ) {z : ℂ}
    (hf : ∀ j : ℕ, DifferentiableAt ℂ (iteratedDeriv j f) z) :
    HasDerivAt (evaluateDifferentialPolynomial P f)
      (evaluateDifferentialPolynomial (formalDerivative P) f z) z := by
  apply hasDerivAt_polynomial_evaluation P (fun j w => jetEvaluation f w j)
    jetVariableDerivative
  intro i
  cases i with
  | zero => simpa [jetEvaluation, jetVariableDerivative] using! hasDerivAt_id z
  | succ j =>
      simpa [jetEvaluation, jetVariableDerivative, iteratedDeriv_succ] using (hf j).hasDerivAt

/-- Germ equality is preserved when taking any actual derivative order. -/
theorem jetEvaluation_eventuallyEq {f g : ℂ → ℂ} {a : ℂ}
    (h : f =ᶠ[𝓝 a] g) (j : ℕ) :
    (fun z => jetEvaluation f z j) =ᶠ[𝓝 a] (fun z => jetEvaluation g z j) := by
  cases j with
  | zero => exact Filter.EventuallyEq.rfl
  | succ j => exact h.iteratedDeriv j

/-- Polynomial substitution is intrinsic to function germs. -/
theorem evaluateDifferentialPolynomial_eventuallyEq (P : DifferentialPolynomial)
    {f g : ℂ → ℂ} {a : ℂ} (h : f =ᶠ[𝓝 a] g) :
    evaluateDifferentialPolynomial P f =ᶠ[𝓝 a] evaluateDifferentialPolynomial P g := by
  change (fun z => MvPolynomial.eval (jetEvaluation f z) P) =ᶠ[𝓝 a]
    (fun z => MvPolynomial.eval (jetEvaluation g z) P)
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval_C]; exact Filter.EventuallyEq.rfl
  | add P Q hP hQ =>
      filter_upwards [hP, hQ] with z hzP hzQ
      simp only [map_add, hzP, hzQ]
  | mul_X P i hP =>
      filter_upwards [hP, jetEvaluation_eventuallyEq h i] with z hzP hzi
      simp only [map_mul, MvPolynomial.eval_X, hzP, hzi]

end
end IsoProof
