import IsoProof.DifferentialOrder
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Basic

/-!
# The separant of a minimal genuine differential relation

The order and the degree of an actual nonzero polynomial relation are minimized
in succession.  A relation containing only the independent coordinate is ruled
out using the finiteness of the roots of a nonzero univariate polynomial.
Consequently the top partial derivative is a nonzero polynomial of smaller top
degree, and cannot itself vanish as a function germ.  Nonvanishing of the
separant is therefore proved, rather than required of the original relation.
-/
namespace IsoProof
noncomputable section
open MvPolynomial Filter Set
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Characteristic zero makes the coefficient multiplier in a partial
polynomial derivative nonzero. -/
theorem pderiv_support_iff (P : DifferentialPolynomial) (n : ℕ) (m : ℕ→₀ℕ) :
    m∈(MvPolynomial.pderiv n P).support ↔ m+Finsupp.single n 1∈P.support := by
  have hn : (m n:ℂ)+1≠0 := by exact_mod_cast (Nat.succ_ne_zero (m n))
  simp only [MvPolynomial.mem_support_iff,MvPolynomial.coeff_pderiv,mul_ne_zero_iff]
  exact and_iff_left hn

theorem pderiv_ne_zero_of_mem_vars {P : DifferentialPolynomial} {n : ℕ}
    (hn : n∈P.vars) : MvPolynomial.pderiv n P≠0 := by
  obtain ⟨m,hm,hmn⟩ := (MvPolynomial.mem_vars_iff_mem_support n).mp hn
  have hmn' : m n≠0 := Finsupp.mem_support_iff.mp hmn
  have hback : m-Finsupp.single n 1+Finsupp.single n 1=m :=
    Finsupp.sub_add_single_one_cancel hmn'
  have hm' : m-Finsupp.single n 1∈(MvPolynomial.pderiv n P).support :=
    (pderiv_support_iff P n _).mpr (by rw [hback]; exact hm)
  intro hz
  simp only [hz,MvPolynomial.support_zero,Finset.notMem_empty] at hm'

theorem degreeOf_pderiv_lt_of_mem_vars {P : DifferentialPolynomial} {n : ℕ}
    (hn : n∈P.vars) :
    (MvPolynomial.pderiv n P).degreeOf n<P.degreeOf n := by
  have hpos : 0<P.degreeOf n := Nat.pos_of_ne_zero
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hn)
  apply (MvPolynomial.degreeOf_lt_iff hpos).mpr
  intro m hm
  have hle := MvPolynomial.monomial_le_degreeOf n ((pderiv_support_iff P n m).mp hm)
  simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hle
  omega

/-- Forgetful polynomial map used only when the original polynomial contains
no variable except the independent coordinate. -/
def coordinatePolynomial : DifferentialPolynomial →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun _=>Polynomial.X)

theorem coordinatePolynomial_reconstruct {P : DifferentialPolynomial}
    (hP : VariableBound P 0) :
    Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (coordinatePolynomial P)=P := by
  have hvars := MvPolynomial.mem_supported.mp hP
  have h := MvPolynomial.hom_congr_vars
    (f₁:=(Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)).comp coordinatePolynomial)
    (f₂:=RingHom.id DifferentialPolynomial) (p₁:=P) (p₂:=P)
    (by ext c; simp [coordinatePolynomial]) (fun i hi _=>by
      have hi0 : i=0 := Nat.eq_zero_of_le_zero (hvars hi)
      subst i
      simp [coordinatePolynomial]) rfl
  exact h

theorem coordinatePolynomial_eval {P : DifferentialPolynomial}
    (hP : VariableBound P 0) (f : ℂ→ℂ) (z : ℂ) :
    (coordinatePolynomial P).eval z=evaluateDifferentialPolynomial P f z := by
  have hvars := MvPolynomial.mem_supported.mp hP
  have h := MvPolynomial.hom_congr_vars
    (f₁:=(Polynomial.evalRingHom z).comp coordinatePolynomial)
    (f₂:=MvPolynomial.eval (jetEvaluation f z)) (p₁:=P) (p₂:=P)
    (by ext c; simp [coordinatePolynomial]) (fun i hi _=>by
      have hi0 : i=0 := Nat.eq_zero_of_le_zero (hvars hi)
      subst i
      simp [coordinatePolynomial,jetEvaluation]) rfl
  exact h

/-- No nonzero polynomial in the coordinate alone vanishes in a complex
neighborhood.  This is independent of all regularity assumptions on f. -/
theorem coordinate_only_relation_impossible {P : DifferentialPolynomial}
    (hP : VariableBound P 0) (hP0 : P≠0) (f : ℂ→ℂ) (a : ℂ) :
    ¬evaluateDifferentialPolynomial P f=ᶠ[𝓝 a](fun _=>0) := by
  intro hrel
  have hq0 : coordinatePolynomial P≠0 := by
    intro hq
    apply hP0
    rw [←coordinatePolynomial_reconstruct hP,hq]
    exact Polynomial.eval₂_zero _ _
  have hroots : {z:ℂ|Polynomial.IsRoot (coordinatePolynomial P) z}∈𝓝 a := by
    filter_upwards [hrel] with z hz
    change (coordinatePolynomial P).eval z=0
    rw [coordinatePolynomial_eval hP f z]
    exact hz
  exact (infinite_of_mem_nhds a hroots) (Polynomial.finite_setOfPred_isRoot hq0)

/-- Finite support gives a concrete finite variable bound. -/
theorem exists_variableBound (P : DifferentialPolynomial) : ∃ n,VariableBound P n := by
  classical
  refine ⟨P.vars.sup id,MvPolynomial.mem_supported.mpr ?_⟩
  intro i hi
  exact Finset.le_sup (f:=id) hi

/-- If the largest allowed variable is absent, the variable bound drops. -/
theorem variableBound_pred_of_not_mem {P : DifferentialPolynomial} {n : ℕ}
    (hP : VariableBound P n) (hn : n∉P.vars) : VariableBound P (n-1) := by
  apply MvPolynomial.mem_supported.mpr
  intro i hi
  have hle : i≤n := MvPolynomial.mem_supported.mp hP hi
  have hne : i≠n := by intro he; exact hn (he ▸hi)
  change i≤n-1
  omega

/-- Every genuine polynomial differential relation admits a minimal order and
minimal top degree representative whose separant is not the zero function
germ.  Variable n is the derivative of order n-1; n is necessarily positive. -/
theorem exists_minimal_relation_nonzero_separant {f : ℂ→ℂ} {a : ℂ}
    (hex : PolynomialDifferentialRelationAt f a) :
    ∃ (n : ℕ) (P : DifferentialPolynomial),1≤n ∧ P≠0 ∧ VariableBound P n ∧
      n∈P.vars ∧ evaluateDifferentialPolynomial P f=ᶠ[𝓝 a](fun _=>0) ∧
      ¬evaluateDifferentialPolynomial (MvPolynomial.pderiv n P) f=ᶠ[𝓝 a](fun _=>0) := by
  classical
  let good : ℕ→Prop := fun n=>∃ P : DifferentialPolynomial,P≠0 ∧ VariableBound P n ∧
    evaluateDifferentialPolynomial P f=ᶠ[𝓝 a](fun _=>0)
  have hg : ∃ n,good n := by
    obtain ⟨P,hP0,hrel⟩ := hex
    obtain ⟨n,hn⟩ := exists_variableBound P
    exact ⟨n,P,hP0,hn,hrel⟩
  let n := Nat.find hg
  have hnmin : ∀ m,good m→n≤m := fun m hm=>Nat.find_min' hg hm
  have hngood : good n := Nat.find_spec hg
  have hn0 : 1≤n := by
    by_contra hn
    have he : n=0 := by omega
    obtain ⟨P,hP0,hP,hrel⟩ := hngood
    rw [he] at hP
    exact coordinate_only_relation_impossible hP hP0 f a hrel
  let deggood : ℕ→Prop := fun d=>∃ P : DifferentialPolynomial,P≠0 ∧ VariableBound P n ∧
    evaluateDifferentialPolynomial P f=ᶠ[𝓝 a](fun _=>0) ∧ P.degreeOf n=d
  have hdg : ∃ d,deggood d := by
    obtain ⟨P,hP0,hP,hrel⟩ := hngood
    exact ⟨P.degreeOf n,P,hP0,hP,hrel,rfl⟩
  obtain ⟨P,hP0,hP,hrel,hdeg⟩ := Nat.find_spec hdg
  have hnvars : n∈P.vars := by
    by_contra hn
    have hsmall : good (n-1) :=
      ⟨P,hP0,variableBound_pred_of_not_mem hP hn,hrel⟩
    have := hnmin (n-1) hsmall
    omega
  refine ⟨n,P,hn0,hP0,hP,hnvars,hrel,?_⟩
  intro hsep
  have hdegmin : P.degreeOf n≤(MvPolynomial.pderiv n P).degreeOf n := by
    rw [hdeg]
    apply Nat.find_min' hdg
    exact ⟨MvPolynomial.pderiv n P,pderiv_ne_zero_of_mem_vars hnvars,
      pderiv_variableBound hP n,hsep,rfl⟩
  exact (Nat.not_lt.mpr hdegmin) (degreeOf_pderiv_lt_of_mem_vars hnvars)

end
end IsoProof
