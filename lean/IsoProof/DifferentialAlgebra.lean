import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Algebraic steps of §5. All theorems below are derived in characteristic
zero; separant nonvanishing is a conclusion, never a supplied field. -/
namespace IsoProof
noncomputable section
open scoped Polynomial nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Every nonzero polynomial in finitely many differential variables over C(z)
has a nonzero common-denominator multiple over C[z]. This is an identity in
the actual polynomial rings, not a formal assertion that coefficients can be
cleared. The index type may be infinite: each polynomial has finite support. -/
theorem clear_rational_denominators {σ : Type*}
    (p : MvPolynomial σ (RatFunc ℂ)) (hp : p ≠ 0) :
    ∃ d : Polynomial ℂ, d ≠ 0 ∧
      ∃ q : MvPolynomial σ (Polynomial ℂ), q ≠ 0 ∧
        MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) q =
          MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d) * p := by
  classical
  let M := (nonZeroDivisors (Polynomial ℂ)).map (MvPolynomial.C (σ := σ))
  obtain ⟨b, q, hq⟩ := IsLocalization.exists_integer_multiple M p
  obtain ⟨d, hd, hdb⟩ := b.property
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hmapd : algebraMap (Polynomial ℂ) (RatFunc ℂ) d ≠ 0 :=
    by simpa only [map_zero] using
      (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)).ne hd0
  have he : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) q =
      MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d) * p := by
    simpa only [Algebra.smul_def, ← hdb, MvPolynomial.algebraMap_def,
      MvPolynomial.map_C] using hq
  refine ⟨d, hd0, q, ?_, he⟩
  intro hq0
  have hprod : MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d) * p = 0 := by
    rw [← he, hq0, map_zero]
  exact hp ((mul_eq_zero.mp hprod).resolve_left (MvPolynomial.C_ne_zero.mpr hmapd))

/-- A least-degree nonzero algebraic relation has a separant that does not
vanish after evaluation. Injectivity of coefficient evaluation rules out a
spurious degree-zero relation. In §5 coefficients are functions of the
coordinate and lower derivatives, after choosing the least differential order. -/
theorem least_degree_separant_nonzero
    {K L : Type*} [Field K] [CharZero K] [Field L]
    (ι : K →+* L) (y : L) (p : Polynomial K)
    (hp : p ≠ 0) (hrel : Polynomial.eval₂ ι y p = 0)
    (hmin : ∀ q : Polynomial K, q ≠ 0 → Polynomial.eval₂ ι y q = 0 →
      p.natDegree ≤ q.natDegree) :
    Polynomial.eval₂ ι y p.derivative ≠ 0 := by
  have hdeg : p.natDegree ≠ 0 := by
    intro hz
    have hconst := Polynomial.eq_C_of_natDegree_eq_zero hz
    rw [hconst, Polynomial.eval₂_C] at hrel
    have hc : p.coeff 0 = 0 := ι.injective (by simpa using hrel)
    exact hp (by rw [hconst, hc, Polynomial.C_0])
  intro hsep
  have hn := hmin p.derivative (Polynomial.derivative_ne_zero.mpr hdeg) hsep
  exact (Nat.not_lt.mpr hn) (Polynomial.natDegree_derivative_lt hdeg)

/-- The least-degree choice exists from any genuine nonzero relation.
This theorem supplies the minimality premise of the preceding lemma. -/
theorem exists_relation_with_nonzero_separant
    {K L : Type*} [Field K] [CharZero K] [Field L]
    (ι : K →+* L) (y : L)
    (hex : ∃ p : Polynomial K, p ≠ 0 ∧ Polynomial.eval₂ ι y p = 0) :
    ∃ p : Polynomial K, p ≠ 0 ∧ Polynomial.eval₂ ι y p = 0 ∧
      Polynomial.eval₂ ι y p.derivative ≠ 0 := by
  classical
  let good : ℕ → Prop := fun n =>
    ∃ p : Polynomial K, p ≠ 0 ∧ Polynomial.eval₂ ι y p = 0 ∧ p.natDegree = n
  have hg : ∃ n, good n := by
    obtain ⟨p, hp, hr⟩ := hex
    exact ⟨p.natDegree, p, hp, hr, rfl⟩
  obtain ⟨p, hp, hr, hd⟩ := Nat.find_spec hg
  refine ⟨p, hp, hr, least_degree_separant_nonzero ι y p hp hr ?_⟩
  intro q hq hqr
  rw [hd]
  exact Nat.find_min' hg ⟨q, hq, hqr, rfl⟩

end
end IsoProof
