import IsoProof.DifferentialAlgebra
import IsoProof.DifferentialCalculus
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Algebra.Polynomial.Roots

/-! Rational coefficients are interpreted in actual punctured function germs.
The denominator exceptions are finite and are removed by a neighborhood
filter, so coefficient poles at the base point are treated correctly. -/
namespace IsoProof
noncomputable section
open Filter
open scoped Topology Polynomial

abbrev PuncturedGerm (a : ℂ) := Filter.Germ (𝓝[≠] a) ℂ

theorem polynomial_eventually_ne_zero (p : Polynomial ℂ) (hp : p ≠ 0) (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, p.eval z ≠ 0 :=
  (Polynomial.eventually_eval_ne_zero_cofinite hp).filter_mono (nhdsNE_le_cofinite a)

theorem rational_denominator_eventually_ne_zero (p : RatFunc ℂ) (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, p.denom.eval z ≠ 0 :=
  polynomial_eventually_ne_zero p.denom (RatFunc.denom_ne_zero p) a

/-- Actual evaluation C(z) -> punctured germs is a ring homomorphism. -/
def rationalGerm (a : ℂ) : RatFunc ℂ →+* PuncturedGerm a where
  toFun p := Filter.Germ.ofFun (fun z => RatFunc.eval (RingHom.id ℂ) z p)
  map_zero' := by
    change ((fun z => RatFunc.eval (RingHom.id ℂ) z 0) : PuncturedGerm a) =
      ((fun _ : ℂ => (0 : ℂ)) : PuncturedGerm a)
    apply Filter.Germ.coe_eq.mpr
    exact Eventually.of_forall (by intro z; simp)
  map_one' := by
    change ((fun z => RatFunc.eval (RingHom.id ℂ) z 1) : PuncturedGerm a) =
      ((fun _ : ℂ => (1 : ℂ)) : PuncturedGerm a)
    apply Filter.Germ.coe_eq.mpr
    exact Eventually.of_forall (by intro z; simp)
  map_add' p q := by
    change ((fun z => RatFunc.eval (RingHom.id ℂ) z (p+q)) : PuncturedGerm a) =
      ((fun z => RatFunc.eval (RingHom.id ℂ) z p + RatFunc.eval (RingHom.id ℂ) z q) : PuncturedGerm a)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [rational_denominator_eventually_ne_zero p a,
      rational_denominator_eventually_ne_zero q a] with z hp hq
    exact RatFunc.eval_add (RingHom.id ℂ) z (by simpa using hp) (by simpa using hq)
  map_mul' p q := by
    change ((fun z => RatFunc.eval (RingHom.id ℂ) z (p*q)) : PuncturedGerm a) =
      ((fun z => RatFunc.eval (RingHom.id ℂ) z p * RatFunc.eval (RingHom.id ℂ) z q) : PuncturedGerm a)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [rational_denominator_eventually_ne_zero p a,
      rational_denominator_eventually_ne_zero q a] with z hp hq
    exact RatFunc.eval_mul (RingHom.id ℂ) z (by simpa using hp) (by simpa using hq)

/-- There are no spurious zero rational functions in this germ model. -/
theorem rationalGerm_injective (a : ℂ) : Function.Injective (rationalGerm a) :=
  (rationalGerm a).injective

@[simp] theorem rationalGerm_polynomial (a : ℂ) (p : Polynomial ℂ) :
    rationalGerm a (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      (fun z => p.eval z : PuncturedGerm a) := by
  apply Filter.Germ.coe_eq.mpr
  exact Eventually.of_forall (by intro z; simp)

/-- The ordinary C[z]-coefficient evaluation is its literal function germ. -/
def polynomialCoefficientGerm (a : ℂ) : Polynomial ℂ →+* PuncturedGerm a :=
  (rationalGerm a).comp (algebraMap (Polynomial ℂ) (RatFunc ℂ))

/-- Evaluating a differential polynomial with C(z) coefficients in germs. -/
def rationalDifferentialGerm {r : ℕ} (a : ℂ) (f : ℂ → ℂ)
    (P : RationalDifferentialPolynomial r) : PuncturedGerm a :=
  MvPolynomial.eval₂ (rationalGerm a)
    (fun j : Fin (r+1) => (iteratedDeriv j.val f : PuncturedGerm a)) P

/-- Evaluation of common-denominator numerators in the same germ ring. -/
def polynomialDifferentialGerm {r : ℕ} (a : ℂ) (f : ℂ → ℂ)
    (P : MvPolynomial (Fin (r+1)) (Polynomial ℂ)) : PuncturedGerm a :=
  MvPolynomial.eval₂ (polynomialCoefficientGerm a)
    (fun j : Fin (r+1) => (iteratedDeriv j.val f : PuncturedGerm a)) P

/-- The concrete finite sum definition of a rational relation agrees with
ring evaluation in punctured germs. -/
theorem rationalDifferentialGerm_eq {r : ℕ} (a : ℂ) (f : ℂ → ℂ)
    (P : RationalDifferentialPolynomial r) :
    rationalDifferentialGerm a f P =
      (evaluateRationalDifferentialPolynomial P f : PuncturedGerm a) := by
  classical
  let c : (Fin (r+1) →₀ ℕ) → ℂ → ℂ :=
    fun d z => RatFunc.eval (RingHom.id ℂ) z (P.coeff d)
  let u : Fin (r+1) → ℂ → ℂ := fun i => iteratedDeriv i.val f
  have he : evaluateRationalDifferentialPolynomial P f =
      ∑ d ∈ P.support, c d * ∏ i ∈ d.support, (u i)^(d i) := by
    funext z
    simp [evaluateRationalDifferentialPolynomial, c, u, Finsupp.prod]
  change rationalDifferentialGerm a f P = Filter.Germ.coeRingHom (𝓝[≠] a) _
  rw [he]
  simp only [rationalDifferentialGerm, MvPolynomial.eval₂_eq,
    map_sum, map_mul, map_prod, map_pow]
  rfl

/-- Rational and polynomial coefficient formulations have exactly the same
nonzero differential relations as punctured function germs. -/
theorem rational_relation_iff_polynomial_coefficient_germ (a : ℂ) (f : ℂ → ℂ) :
    RationalDifferentialRelationAt f a ↔
      ∃ r : ℕ, ∃ Q : MvPolynomial (Fin (r+1)) (Polynomial ℂ), Q ≠ 0 ∧
        polynomialDifferentialGerm a f Q = 0 := by
  constructor
  · rintro ⟨r, P, hP, hrel⟩
    obtain ⟨d, hd, Q, hQ, hclear⟩ := clear_rational_denominators P hP
    refine ⟨r, Q, hQ, ?_⟩
    have he : rationalDifferentialGerm a f P = 0 := by
      rw [rationalDifferentialGerm_eq]
      exact Filter.Germ.coe_eq.mpr hrel
    have hh := congrArg
      (MvPolynomial.eval₂Hom (rationalGerm a)
        (fun j : Fin (r+1) => (iteratedDeriv j.val f : PuncturedGerm a))) hclear
    have he' : MvPolynomial.eval₂ (rationalGerm a)
        (fun j : Fin (r+1) => (iteratedDeriv j.val f : PuncturedGerm a)) P = 0 := he
    simpa only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂_map,
      polynomialDifferentialGerm, polynomialCoefficientGerm, rationalDifferentialGerm,
      MvPolynomial.coe_eval₂Hom, he', mul_zero] using hh
  · rintro ⟨r, Q, hQ, hrel⟩
    let P : RationalDifferentialPolynomial r :=
      MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) Q
    have hP : P ≠ 0 := by
      intro hzero
      apply hQ
      exact MvPolynomial.map_injective
        (algebraMap (Polynomial ℂ) (RatFunc ℂ))
        (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))
        (by simpa only [map_zero] using hzero)
    refine ⟨r, P, hP, ?_⟩
    apply Filter.Germ.coe_eq.mp
    rw [← rationalDifferentialGerm_eq]
    change rationalDifferentialGerm a f P = 0
    simpa only [P, rationalDifferentialGerm, MvPolynomial.eval₂_map,
      polynomialDifferentialGerm, polynomialCoefficientGerm] using hrel

end
end IsoProof
