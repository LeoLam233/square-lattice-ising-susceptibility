import IsoProof.DifferentialCalculus
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Tactic

/-! The leading-jet coefficient in repeated differentiation. This proves the
polynomial remainder assertion used in §5, including its derivative-order
bound, rather than supplying it as an assumption. -/
namespace IsoProof
noncomputable section
open scoped BigOperators
open MvPolynomial

/-- Variables 0,...,n: coordinate and derivatives through n-1. -/
def VariableBound (P : DifferentialPolynomial) (n : ℕ) : Prop :=
  P ∈ MvPolynomial.supported ℂ (Set.Iic n)

theorem VariableBound.mono {P : DifferentialPolynomial} {n m : ℕ}
    (hP : VariableBound P n) (hnm : n ≤ m) : VariableBound P m :=
  MvPolynomial.supported_mono (Set.Iic_subset_Iic.mpr hnm) hP

theorem variableBound_X {i n : ℕ} (h : i ≤ n) :
    VariableBound (MvPolynomial.X i) n := MvPolynomial.X_mem_supported.mpr h

/-- A derivation preserves a polynomial subalgebra if its values on the
generators belong to it. -/
theorem derivation_maps_supported
    (D : Derivation ℂ DifferentialPolynomial DifferentialPolynomial)
    {n m : ℕ} (hnm : n ≤ m)
    (hX : ∀ i : ℕ, i ≤ n → VariableBound (D (MvPolynomial.X i)) m)
    {P : DifferentialPolynomial} (hP : VariableBound P n) :
    VariableBound (D P) m := by
  change P ∈ Algebra.adjoin ℂ (MvPolynomial.X '' Set.Iic n) at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact hX i hi
  | algebraMap c =>
      change VariableBound (D (MvPolynomial.C c)) m
      simp only [MvPolynomial.derivation_C]
      exact (MvPolynomial.supported ℂ (Set.Iic m)).zero_mem
  | add P Q hP hQ ihP ihQ =>
      rw [map_add]
      exact (MvPolynomial.supported ℂ (Set.Iic m)).add_mem ihP ihQ
  | mul P Q hP hQ ihP ihQ =>
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      exact (MvPolynomial.supported ℂ (Set.Iic m)).add_mem
        ((MvPolynomial.supported ℂ (Set.Iic m)).mul_mem
          (VariableBound.mono hP hnm) ihQ)
        ((MvPolynomial.supported ℂ (Set.Iic m)).mul_mem
          (VariableBound.mono hQ hnm) ihP)

theorem formalDerivative_variableBound {P : DifferentialPolynomial} {n : ℕ}
    (hP : VariableBound P n) : VariableBound (formalDerivative P) (n+1) := by
  apply derivation_maps_supported formalDerivative (Nat.le_succ n) ?_ hP
  intro i hi
  cases i with
  | zero =>
      rw [formalDerivative_coordinate]
      exact (MvPolynomial.supported ℂ (Set.Iic (n+1))).one_mem
  | succ j =>
      rw [formalDerivative_jet]
      apply variableBound_X
      omega

theorem pderiv_variableBound {P : DifferentialPolynomial} {n : ℕ}
    (hP : VariableBound P n) (i : ℕ) :
    VariableBound (MvPolynomial.pderiv i P) n := by
  apply derivation_maps_supported (MvPolynomial.pderiv i) le_rfl ?_ hP
  intro j _
  by_cases h : j = i
  · subst j
    rw [MvPolynomial.pderiv_X_self]
    exact (MvPolynomial.supported ℂ (Set.Iic n)).one_mem
  · rw [MvPolynomial.pderiv_X_of_ne h]
    exact (MvPolynomial.supported ℂ (Set.Iic n)).zero_mem

/-- Remove only the highest-jet component of the total derivative. -/
def lowerDerivative (n : ℕ) :
    Derivation ℂ DifferentialPolynomial DifferentialPolynomial :=
  MvPolynomial.mkDerivation ℂ (fun i => if i=n then 0 else jetVariableDerivative i)

theorem lowerDerivative_variableBound {P : DifferentialPolynomial} {n : ℕ}
    (hP : VariableBound P n) : VariableBound (lowerDerivative n P) n := by
  apply derivation_maps_supported (lowerDerivative n) le_rfl ?_ hP
  intro i hi
  simp only [lowerDerivative, MvPolynomial.mkDerivation_X]
  by_cases he : i=n
  · simp only [he, ite_true]
    exact (MvPolynomial.supported ℂ (Set.Iic n)).zero_mem
  · simp only [he, ite_false]
    cases i with
    | zero => exact (MvPolynomial.supported ℂ (Set.Iic n)).one_mem
    | succ j =>
        apply variableBound_X
        omega

theorem formalDerivative_split_identity (P : DifferentialPolynomial) {n : ℕ}
    (hn : 1 ≤ n) :
    formalDerivative P = MvPolynomial.pderiv n P * MvPolynomial.X (n+1) +
      lowerDerivative n P := by
  have hD : formalDerivative =
      (MvPolynomial.X (n+1) : DifferentialPolynomial) •
        (MvPolynomial.pderiv n : Derivation ℂ DifferentialPolynomial DifferentialPolynomial) +
        lowerDerivative n := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [Derivation.add_apply, Derivation.smul_apply, smul_eq_mul,
      lowerDerivative, MvPolynomial.mkDerivation_X]
    by_cases he : i=n
    · subst i
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      simp [formalDerivative_jet]
    · rw [MvPolynomial.pderiv_X_of_ne he]
      simp only [he, ite_false, mul_zero, zero_add]
      exact MvPolynomial.mkDerivation_X ℂ jetVariableDerivative i
  simpa only [Derivation.add_apply, Derivation.smul_apply, smul_eq_mul, mul_comm]
    using congrArg (fun D : Derivation ℂ DifferentialPolynomial DifferentialPolynomial => D P) hD

/-- After m+1 differentiations, the coefficient of the highest new jet is the
original separant; the remaining polynomial has strictly lower order. -/
theorem iterated_formalDerivative_split (P : DifferentialPolynomial) {n : ℕ}
    (hn : 1 ≤ n) (hP : VariableBound P n) (m : ℕ) :
    ∃ R : DifferentialPolynomial, VariableBound R (n+m) ∧
      (formalDerivative^[m+1]) P =
        MvPolynomial.pderiv n P * MvPolynomial.X (n+m+1) + R := by
  induction m with
  | zero =>
      refine ⟨lowerDerivative n P, ?_, ?_⟩
      · simpa using lowerDerivative_variableBound hP
      · simpa using formalDerivative_split_identity P hn
  | succ m ih =>
      obtain ⟨R, hR, he⟩ := ih
      let S := MvPolynomial.pderiv n P
      refine ⟨formalDerivative S * MvPolynomial.X (n+m+1) + formalDerivative R, ?_, ?_⟩
      · apply (MvPolynomial.supported ℂ (Set.Iic (n+(m+1)))).add_mem
        · apply (MvPolynomial.supported ℂ (Set.Iic (n+(m+1)))).mul_mem
          · exact (formalDerivative_variableBound (pderiv_variableBound hP n)).mono (by omega)
          · exact variableBound_X (by omega)
        · simpa only [VariableBound, Nat.add_assoc] using formalDerivative_variableBound hR
      · rw [Function.iterate_succ_apply', he, map_add, formalDerivative.leibniz]
        simp only [smul_eq_mul]
        have hX : formalDerivative (MvPolynomial.X (n+m+1)) =
            MvPolynomial.X (n+(m+1)+1) := by
          simpa only [Nat.add_assoc] using formalDerivative_jet (n+m)
        rw [hX]
        dsimp [S]
        ring

end
end IsoProof
