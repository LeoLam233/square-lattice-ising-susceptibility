import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact critical-order arithmetic of the five-page isotropic proof, §4.
These statements concern the lower, sharp derivative order in the short
paper.  In particular this is not the older HT order (N²-1)/2. -/
namespace IsoProof

/-- For N ≥ 2 this is ceil((N²-3)/2).  Natural subtraction is harmless on
that explicitly stated range. -/
def criticalOrder (N : ℕ) : ℕ := (N^2-2)/2

/-- The signed radial exponent after a pole of order m. -/
def collisionRadialExponent (N m : ℕ) : ℤ := (N:ℤ)^2-2-2*m

/-- This characterizes the ceiling, without casting through a real floor. -/
theorem criticalOrder_le_iff {N k : ℕ} (hN : 2 ≤ N) :
    criticalOrder N ≤ k ↔ N^2-3 ≤ 2*k := by
  have hsq : 4 ≤ N^2 := by nlinarith
  unfold criticalOrder
  omega

theorem odd_square_criticalOrder {N : ℕ} (hN : 2 ≤ N) (hodd : Odd N) :
    N^2 = 2*criticalOrder N+3 := by
  have hsq : 4 ≤ N^2 := by nlinarith
  have hmod : N^2 % 2 = 1 := by
    simp [Nat.pow_mod, Nat.odd_iff.mp hodd]
  unfold criticalOrder
  omega

theorem even_square_criticalOrder {N : ℕ} (hN : 2 ≤ N) (heven : Even N) :
    N^2 = 2*criticalOrder N+2 := by
  have hsq : 4 ≤ N^2 := by nlinarith
  have hmod : N^2 % 2 = 0 := by
    simp [Nat.pow_mod, Nat.even_iff.mp heven]
  unfold criticalOrder
  omega

/-- The square of the Vandermonde has degree N(N-1); radial Lebesgue
measure on the (N-1)-plane contributes N-2. -/
theorem vandermonde_radial_degree (N : ℕ) :
    (N:ℤ)*((N:ℤ)-1)+((N:ℤ)-2) = (N:ℤ)^2-2 := by ring

/-- At the sharp odd derivative the surviving kernel is r^(-1). -/
theorem odd_critical_radial_exponent {N : ℕ} (hN : 2 ≤ N) (hodd : Odd N) :
    collisionRadialExponent N (criticalOrder N+1) = -1 := by
  have hsq : (N:ℤ)^2 = 2*(criticalOrder N:ℤ)+3 := by
    exact_mod_cast odd_square_criticalOrder hN hodd
  unfold collisionRadialExponent
  push_cast
  linarith

/-- At the sharp even derivative the surviving kernel is r^(-2). -/
theorem even_critical_radial_exponent {N : ℕ} (hN : 2 ≤ N) (heven : Even N) :
    collisionRadialExponent N (criticalOrder N+1) = -2 := by
  have hsq : (N:ℤ)^2 = 2*(criticalOrder N:ℤ)+2 := by
    exact_mod_cast even_square_criticalOrder hN heven
  unfold collisionRadialExponent
  push_cast
  linarith

/-- Every lower pole order is locally integrable in the radial variable. -/
theorem lower_pole_radial_exponent {N j : ℕ} (hN : 2 ≤ N)
    (hj : j ≤ criticalOrder N) :
    -1 < collisionRadialExponent N j := by
  rcases Nat.even_or_odd N with heven | hodd
  · have hsq : (N:ℤ)^2 = 2*(criticalOrder N:ℤ)+2 := by
      exact_mod_cast even_square_criticalOrder hN heven
    have hj' : (j:ℤ) ≤ criticalOrder N := by exact_mod_cast hj
    unfold collisionRadialExponent
    linarith
  · have hsq : (N:ℤ)^2 = 2*(criticalOrder N:ℤ)+3 := by
      exact_mod_cast odd_square_criticalOrder hN hodd
    have hj' : (j:ℤ) ≤ criticalOrder N := by exact_mod_cast hj
    unfold collisionRadialExponent
    linarith

/-- Every strictly higher particle order is integrable even at the sharp
critical derivative of N; the same-parity application is a fortiori valid. -/
theorem higher_order_radial_exponent {N M : ℕ} (hN : 2 ≤ N) (hNM : N < M) :
    -1 < collisionRadialExponent M (criticalOrder N+1) := by
  have hlow : 2*criticalOrder N+2 ≤ N^2 := by
    rcases Nat.even_or_odd N with heven | hodd
    · rw [even_square_criticalOrder hN heven]
    · rw [odd_square_criticalOrder hN hodd]; omega
  have hN' : (2:ℤ) ≤ N := by exact_mod_cast hN
  have hNM' : (N:ℤ)+1 ≤ M := by exact_mod_cast hNM
  have hlow' : 2*(criticalOrder N:ℤ)+2 ≤ (N:ℤ)^2 := by exact_mod_cast hlow
  unfold collisionRadialExponent
  push_cast
  nlinarith

/-- The selected critical orders exceed any prescribed fixed order once
particle number does; this is the arithmetic needed in the separant step. -/
theorem criticalOrder_unbounded (r N : ℕ) (hN : 2*r+4 ≤ N) :
    r < criticalOrder N := by
  have hn2 : 2 ≤ N := by omega
  by_contra h
  have hle : criticalOrder N ≤ r := by omega
  have hh := (criticalOrder_le_iff hn2).mp hle
  have hs : 2*r+4 ≤ N^2 := by nlinarith
  omega

end IsoProof
