import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! Exact lattice bookkeeping for equation (6) of the five-page manuscript.
These finite sets are the literal square balls in Z x Z. -/
namespace IsoProof
open scoped BigOperators

/-- The closed lattice square of radius `A`. -/
def latticeSquare (A : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(A : ℤ)) A) ×ˢ (Finset.Icc (-(A : ℤ)) A)

/-- The nonzero shell of radius `A+1`, including all signs and axes. -/
def latticeShell (A : ℕ) : Finset (ℤ × ℤ) :=
  latticeSquare (A+1) \ latticeSquare A

theorem mem_latticeSquare (A : ℕ) (p : ℤ × ℤ) :
    p ∈ latticeSquare A ↔ max |p.1| |p.2| ≤ (A : ℤ) := by
  simp only [latticeSquare, Finset.mem_product, Finset.mem_Icc,
    max_le_iff, abs_le]

theorem latticeSquare_mono {A B : ℕ} (h : A ≤ B) :
    latticeSquare A ⊆ latticeSquare B := by
  intro p hp
  rw [mem_latticeSquare] at hp ⊢
  exact hp.trans (by exact_mod_cast h)

theorem mem_latticeShell (A : ℕ) (p : ℤ × ℤ) :
    p ∈ latticeShell A ↔ max |p.1| |p.2| = (A+1 : ℕ) := by
  simp only [latticeShell, Finset.mem_sdiff, mem_latticeSquare]
  omega

theorem latticeSquare_card (A : ℕ) :
    (latticeSquare A).card = (2*A+1)^2 := by
  have h : ((A : ℤ) + 1 - -(A : ℤ)).toNat = 2*A+1 := by omega
  simp only [latticeSquare, Finset.card_product, Int.card_Icc, h]
  ring

/-- There are exactly `8R` integer sites at square radius `R>0`. -/
theorem latticeShell_card (A : ℕ) :
    (latticeShell A).card = 8*(A+1) := by
  rw [latticeShell, Finset.card_sdiff_of_subset (latticeSquare_mono (by omega))]
  rw [latticeSquare_card, latticeSquare_card]
  have h : (2*(A+1)+1)^2 = (2*A+1)^2 + 8*(A+1) := by ring
  omega

/-- The origin is the unique zero-radius lattice site. -/
theorem latticeSquare_zero : latticeSquare 0 = {(0,0)} := by
  ext p
  simp [latticeSquare]

/-- Summing a constant shell weight produces the exact factor `8R`. -/
theorem sum_latticeShell_const (A : ℕ) (c : ℝ) :
    (∑ _p ∈ latticeShell A, c) = (8*(A+1) : ℕ)*c := by
  simp only [Finset.sum_const, nsmul_eq_mul, latticeShell_card]

end IsoProof
