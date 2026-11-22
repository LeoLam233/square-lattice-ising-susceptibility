import IsoProof.TailLattice
import IsoProof.TailNumerics
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Summability on the complete signed square lattice, using the exact
eight-times-radius shell cardinality, with the origin retained separately. -/
namespace IsoProof
noncomputable section
open Set
open scoped BigOperators

def latticeRadius (p : ℤ × ℤ) : ℕ := max p.1.natAbs p.2.natAbs

theorem latticeRadius_cast (p : ℤ × ℤ) :
    (latticeRadius p : ℤ) = max |p.1| |p.2| := by
  simp only [latticeRadius, Nat.cast_max, Int.natCast_natAbs]

def radiusShell (R : ℕ) : Finset (ℤ × ℤ) :=
  match R with
  | 0 => {(0,0)}
  | n+1 => latticeShell n

theorem mem_radiusShell (R : ℕ) (p : ℤ × ℤ) :
    p ∈ radiusShell R ↔ latticeRadius p=R := by
  cases R with
  | zero =>
      simp only [radiusShell,Finset.mem_singleton,latticeRadius]
      constructor
      · rintro rfl
        simp
      · intro h
        have h1 : p.1.natAbs=0 := by omega
        have h2 : p.2.natAbs=0 := by omega
        exact Prod.ext (Int.natAbs_eq_zero.mp h1) (Int.natAbs_eq_zero.mp h2)
  | succ n =>
      rw [radiusShell,mem_latticeShell,← latticeRadius_cast]
      exact Int.natCast_inj

theorem radiusShell_card (R : ℕ) :
    (radiusShell R).card = if R=0 then 1 else 8*R := by
  cases R with
  | zero => simp [radiusShell]
  | succ n => simp [radiusShell,latticeShell_card]

theorem lattice_radial_summable {w : ℕ → ℝ} (hw : ∀ R, 0 ≤ w R)
    (hs : Summable (fun n : ℕ => (8*(n+1) : ℕ)*w (n+1))) :
    Summable (fun p : ℤ × ℤ => w (latticeRadius p)) := by
  let s : ℕ → Set (ℤ × ℤ) := fun R => {p | latticeRadius p=R}
  have hshell (R : ℕ) : s R = ↑(radiusShell R) := by
    ext p
    exact (mem_radiusShell R p).symm
  have hfinite (R : ℕ) : (s R).Finite := by
    rw [hshell]
    exact Finset.finite_toSet _
  have hsum (R : ℕ) : (∑' p : s R, w (latticeRadius p)) =
      (if R=0 then 1 else (8*R : ℝ))*w R := by
    let := (hfinite R).fintype
    have he : (fun p : s R => w (latticeRadius p)) = fun _ => w R := by
      funext p
      exact congrArg w p.property
    rw [he,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hcard : Fintype.card (s R) = (radiusShell R).card := by
      exact (Fintype.card_congr (Set.equivOfEq (hshell R))).trans (Fintype.card_coe _)
    rw [hcard,radiusShell_card]
    split_ifs <;> norm_cast
  apply (summable_partition (fun p => hw (latticeRadius p))
    (s := s) (fun p => ⟨latticeRadius p,rfl,fun R hR => hR.symm⟩)).mpr
  constructor
  · intro R
    let := (hfinite R).fintype
    exact Summable.of_finite
  · simp_rw [hsum]
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceIte,Nat.cast_mul,
      Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using hs

def spatialTailMajorant (p : ℤ × ℤ) : ℝ :=
  (1+(latticeRadius p : ℝ))^(-(5/2 : ℝ))

theorem spatialTailMajorant_nonneg (p : ℤ × ℤ) : 0 ≤ spatialTailMajorant p := by
  unfold spatialTailMajorant
  positivity

theorem spatialTailMajorant_summable : Summable spatialTailMajorant := by
  apply lattice_radial_summable (w := fun R => (1+(R : ℝ))^(-(5/2 : ℝ)))
    (fun R => by positivity)
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using
    shell_majorant_summable

theorem site_tail_spatial_bound {N j k : ℕ} (hj : j ≤ k) (hN : 2*k+4 < N)
    (p : ℤ × ℤ) :
    (1+(latticeRadius p : ℝ))^((j : ℝ)-(N : ℝ)/2) ≤ spatialTailMajorant p := by
  exact Real.rpow_le_rpow_of_exponent_le (by
    linarith [show 0 ≤ (latticeRadius p : ℝ) from Nat.cast_nonneg _])
    (site_tail_exponent hj hN)

/-- An absolutely summable majorant for all particle orders and all signed
sites; parity and a high-order cutoff only remove terms from this family. -/
theorem joint_tail_majorant_summable {C : ℝ} (hC : 0 ≤ C) :
    Summable (fun p : ℕ × (ℤ × ℤ) => siteOrderEnvelope C p.1*spatialTailMajorant p.2) := by
  exact (siteOrderEnvelope_summable hC).mul_of_nonneg spatialTailMajorant_summable
    (fun N => by unfold siteOrderEnvelope; positivity) spatialTailMajorant_nonneg

end
end IsoProof
