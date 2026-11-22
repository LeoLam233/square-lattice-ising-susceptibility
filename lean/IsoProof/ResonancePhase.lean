import IsoProof.ResonanceArithmetic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp

/-! Direct algebra of the coincident collision-center density in §4.
The displayed phase is independent of the positive sine of the collision
angle.  The statement is a scalar identity, not a substituted assertion about
an unconstructed localized integral. -/
namespace IsoProof
noncomputable section
open Complex

/-- Number of unordered pairs among N particles. -/
def pairCount (N : ℕ) : ℕ := N*(N-1)/2

theorem twice_pairCount (N : ℕ) : 2*pairCount N=N*(N-1) := by
  unfold pairCount
  rw [mul_comm 2, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self N)]

theorem pair_and_body_degree (N : ℕ) : 2*pairCount N+N=N^2 := by
  rw [twice_pairCount]
  cases N with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel]; ring

/-- Product of the center value of every divided squared pair, every
one-body factor, and the affine contour Jacobian.  Positive overall Haar,
factorial and resolvent constants can be multiplied afterwards. -/
def rawCollisionCenter (N : ℕ) (L a : ℂ) : ℂ :=
  (L^2/(4*(Complex.I*a)^2))^(pairCount N) *
    ((Complex.I*a)^N)⁻¹ * L^(N-1)

/-- The common complex phase, before normalization to modulus one. -/
def collisionCenterPhase (N : ℕ) (L : ℂ) : ℂ :=
  L^(N^2-1)/(Complex.I^(N^2))

theorem rawCollisionCenter_factorization {N : ℕ} (hN : 1≤N) (L a : ℂ) :
    rawCollisionCenter N L a =
      collisionCenterPhase N L / ((4:ℂ)^(pairCount N)*a^(N^2)) := by
  have hdeg := pair_and_body_degree N
  have hLdeg : 2*pairCount N+(N-1)=N^2-1 := by omega
  have hform : rawCollisionCenter N L a =
      (L^(2*pairCount N)*L^(N-1)) /
        ((4:ℂ)^(pairCount N)*((Complex.I*a)^(2*pairCount N)*(Complex.I*a)^N)) := by
    unfold rawCollisionCenter
    simp only [mul_pow,←pow_mul,div_eq_mul_inv,mul_inv_rev]
    ring_nf
    norm_num
  rw [hform,←pow_add,←pow_add,hLdeg,hdeg,mul_pow]
  unfold collisionCenterPhase
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The literal i^{-N²} L^{N²-1} phase displayed in the manuscript. -/
theorem collisionCenterPhase_exact (N : ℕ) (L : ℂ) :
    collisionCenterPhase N L=Complex.I^(-((N^2:ℕ):ℤ))*L^(N^2-1) := by
  simp only [collisionCenterPhase,zpow_neg,zpow_natCast,div_eq_mul_inv,mul_comm]

/-- A positive physical sine contributes only a positive real scalar.
This computes the phase uniformly over all collisions of a fixed order. -/
theorem rawCollisionCenter_positive_ray {N : ℕ} (hN : 1≤N) (L : ℂ)
    {a : ℝ} (ha : 0<a) :
    ∃ c : ℝ,0<c ∧
      rawCollisionCenter N L (a:ℂ)=collisionCenterPhase N L*(c:ℂ) := by
  refine ⟨((4:ℝ)^(pairCount N)*a^(N^2))⁻¹,by positivity,?_⟩
  rw [rawCollisionCenter_factorization hN]
  push_cast
  rfl

/-- The common phase does not vanish on the graph L=1+i ε. -/
theorem collisionCenterPhase_ne_zero (N : ℕ) (ε : ℝ) :
    collisionCenterPhase N (1+Complex.I*(ε:ℂ))≠0 := by
  unfold collisionCenterPhase
  apply div_ne_zero
  · apply pow_ne_zero
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  · exact pow_ne_zero _ Complex.I_ne_zero

/-- A finite sum of nonempty same-phase positive contributions cannot cancel. -/
theorem sum_positive_ray_nonzero {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {u : ℂ} (hu : u≠0) (a : ι → ℝ) (ha : ∀ i∈s,0<a i) :
    (∑ i∈s,u*(a i:ℂ))≠0 := by
  rw [←Finset.mul_sum]
  apply mul_ne_zero hu
  have hp : 0<∑ i∈s,a i := Finset.sum_pos ha hs
  exact_mod_cast hp.ne'

/-- Leading differentiated pole on the common ray, with the center amplitude
already split into its common phase and its positive real scalar. -/
def collisionLeadingModel (k : ℕ) (phase L : ℂ) (c d h t Q : ℝ) : ℂ :=
  (-1:ℂ)^k*(k.factorial:ℂ)*(phase*(c:ℂ))*(-Complex.I*(d:ℂ))^k /
    (-Complex.I*L^2*((d*t+h*Q:ℝ):ℂ))^(k+1)

def collisionDerivativePhase (k : ℕ) (phase L : ℂ) : ℂ :=
  (-1:ℂ)^k*(k.factorial:ℂ)*phase*(-Complex.I)^k / (-Complex.I*L^2)^(k+1)

/-- All dependence on the individual positive collision parameters is real
and positive.  The same rotation therefore works for all fixed-order charts. -/
theorem collisionLeadingModel_factorization (k : ℕ) (phase L : ℂ)
    (c d h t Q : ℝ) :
    collisionLeadingModel k phase L c d h t Q =
      collisionDerivativePhase k phase L * ((c*d^k/(d*t+h*Q)^(k+1):ℝ):ℂ) := by
  unfold collisionLeadingModel collisionDerivativePhase
  push_cast
  simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

theorem collisionLeadingModel_positive_ray (k : ℕ) (phase L : ℂ)
    {c d h t Q : ℝ} (hc : 0<c) (hd : 0<d) (hh : 0<h)
    (ht : 0<t) (hQ : 0≤Q) :
    ∃ b : ℝ,0<b ∧ collisionLeadingModel k phase L c d h t Q =
      collisionDerivativePhase k phase L*(b:ℂ) := by
  refine ⟨c*d^k/(d*t+h*Q)^(k+1),?_,collisionLeadingModel_factorization _ _ _ _ _ _ _ _⟩
  exact div_pos (mul_pos hc (pow_pos hd _))
    (pow_pos (add_pos_of_pos_of_nonneg (mul_pos hd ht) (mul_nonneg hh.le hQ)) _)

/-- Stability of the common rotation under a relative error smaller than
one half.  This is the scalar estimate used after the Taylor remainders have
been bounded uniformly on finitely many collision charts. -/
theorem common_rotation_lower_of_relative_error {u w : ℂ} {a : ℝ}
    (hu : u≠0) (_ha : 0<a) (herr : ‖w-u*(a:ℂ)‖≤‖u‖*a/2) :
    a/2≤(u⁻¹*w).re := by
  have huN : ‖u‖≠0 := norm_ne_zero_iff.mpr hu
  have he : u⁻¹*w-(a:ℂ)=u⁻¹*(w-u*(a:ℂ)) := by
    rw [mul_sub,←mul_assoc,inv_mul_cancel₀ hu,one_mul]
  have hb : ‖u⁻¹*w-(a:ℂ)‖≤a/2 := by
    rw [he,norm_mul,norm_inv]
    calc
      ‖u‖⁻¹*‖w-u*(a:ℂ)‖≤‖u‖⁻¹*(‖u‖*a/2) :=
        mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr (norm_nonneg _))
      _=a/2 := by field_simp
  have hr := (neg_abs_le (u⁻¹*w-(a:ℂ)).re).trans
    (le_of_eq (rfl : (u⁻¹*w-(a:ℂ)).re=(u⁻¹*w-(a:ℂ)).re))
  have habs := Complex.abs_re_le_norm (u⁻¹*w-(a:ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re] at hr habs
  linarith

end
end IsoProof
