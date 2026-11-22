import IsoProof.ResonanceFiniteGeometry
import IsoProof.ResonancePaths
import IsoProof.ResonanceEndpoint
import IsingBulk.Preferred22.FiniteEquality

/-! The arithmetic hypotheses needed by the literal finite common contour
are produced at an explicit prime level.  Both signed constraints are
retained.  Choosing p>2M excludes every possible signed finite-order
collision with N≤M, and the endpoint exclusion holds at every N. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open IsingBulk.PrimeFamily IsingBulk.HT22.Arithmetic
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem prime_energy_ne_one {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) : 2*Real.cos (angle p a)≠1 := by
  intro hx
  apply primeRoot_trace_not_rational hp hp5 (primeIndex_of_admissible hp.pos ha) (1:ℚ)
  simpa only [energy,hx,Complex.ofReal_one,Rat.cast_one] using prime_root_energy p a

private theorem exp_nat_real_angle (N : ℕ) (u : ℝ) :
    Complex.exp ((((N:ℝ)*u:ℝ):ℂ)*Complex.I)=(Complex.exp ((u:ℂ)*Complex.I))^N := by
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Both endpoints of the oscillatory arc satisfy the exact arithmetic
nonresonance required for every signed constrained torus. -/
theorem prime_endpoint_phase_exclusion {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) (N : ℕ) (hN : 0<N) (σ : Sign) :
    Complex.exp ((((N:ℝ)*cutHalfWidth (2*Real.cos (angle p a)):ℝ):ℂ)*Complex.I)≠signValue σ ∧
    Complex.exp ((((N:ℝ)*(-cutHalfWidth (2*Real.cos (angle p a))):ℝ):ℂ)*Complex.I)≠signValue σ := by
  have hgeo := admissible_root_geometry hp hp5 ha
  have hw : IsOfFinOrder (IsingBulk.PrimeFamily.angleRoot p a) :=
    (angleRoot_primitive hp ha).isOfFinOrder hp.ne_zero
  have hwtrace := prime_root_energy p a
  change IsingBulk.PrimeFamily.angleRoot p a+(IsingBulk.PrimeFamily.angleRoot p a)⁻¹
    =((2*Real.cos (angle p a):ℝ):ℂ) at hwtrace
  have hc : Real.cos (cutHalfWidth (2*Real.cos (angle p a)))=2*Real.cos (angle p a)-1 :=
    Real.cos_arccos (by linarith [hgeo.2.2.2.2.1]) (by linarith [hgeo.2.2.2.2.2])
  have hex (u : ℝ) (hu : Real.cos u=2*Real.cos (angle p a)-1) :
      Complex.exp ((((N:ℝ)*u:ℝ):ℂ)*Complex.I)≠signValue σ := by
    have ht : Complex.exp ((u:ℂ)*Complex.I)+(Complex.exp ((u:ℂ)*Complex.I))⁻¹=
        2*(((2*Real.cos (angle p a):ℝ):ℂ)-1) := by
      rw [exp_angle_add_inv,hu]
      push_cast
      rfl
    have hn := endpoint_power_ne_signs_of_rootUnity_level hw hwtrace hgeo.2.2.2.2.1
      hgeo.2.2.2.2.2 (prime_energy_ne_one hp hp5 ha) ht N hN
    rw [exp_nat_real_angle]
    cases σ with
    | positive => exact hn.1
    | negative => exact hn.2
  exact ⟨hex _ hc,hex _ (by rwa [Real.cos_neg])⟩

/-- The uniform strict mean bound now has arithmetic-only inputs. -/
theorem prime_constrained_contourCenter_uniform {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) (N : ℕ) (hN : 0<N) (σ : Sign) :
    ∃ d : ℝ,0≤d ∧ d<cutHalfWidth (2*Real.cos (angle p a)) ∧
      ∀r∈constrainedAngularTorus N σ,
      contourCenter (contourDisplacement (cutHalfWidth (2*Real.cos (angle p a)))) r∈Icc (-d) d := by
  have hgeo := admissible_root_geometry hp hp5 ha
  obtain ⟨hb,hbpi⟩ := cutHalfWidth_range hgeo.2.2.2.2.1 hgeo.2.2.2.2.2
  obtain ⟨hplus,hminus⟩ := prime_endpoint_phase_exclusion hp hp5 ha N hN σ
  exact constrained_contourCenter_uniform hN hb hbpi hplus hminus

/-- The complete constrained common graph has a protected actual root
sheet at every prime level and every positive particle number. -/
theorem prime_constrained_common_graph_domain {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) (N : ℕ) (hN : 0<N) (σ : Sign) :
    ∃ ε : ℝ,0<ε ∧ ∀v,0<v → v<ε → ∀r∈constrainedAngularTorus N σ,
      ∀y,0≤y → ∀i : Fin N,
      graphDispersion (2*Real.cos (angle p a)) (cutHalfWidth (2*Real.cos (angle p a)))
        v y (r i) (contourCenter (contourDisplacement (cutHalfWidth (2*Real.cos (angle p a)))) r)
        ∈contourRootDomain := by
  have hgeo := admissible_root_geometry hp hp5 ha
  obtain ⟨hplus,hminus⟩ := prime_endpoint_phase_exclusion hp hp5 ha N hN σ
  exact constrained_common_graph_domain hN hgeo.2.2.2.2.1 hgeo.2.2.2.2.2 hplus hminus

private theorem signed_root_pow_double {z : ℂ} {N : ℕ} {σ : Sign}
    (hz : z^N=signValue σ) : z^(2*N)=1 := by
  rw [Nat.mul_comm 2 N,pow_mul,hz]
  cases σ <;> norm_num [signValue]

/-- Every signed constant collision forces the ordinary Nickel equation at
order 2N.  This permits a single uniform finite-order exclusion for both signs. -/
theorem constant_signed_collision_implies_nickel {N : ℕ} (hN : 0<N)
    {σ : Sign} {ζ z : ℂ} {c : ℝ} (hζ : ‖ζ‖=1)
    (hangle : Complex.exp ((((N:ℝ)*c:ℝ):ℂ)*Complex.I)=signValue σ)
    (hprod : z^N=signValue σ)
    (htrace : z+z⁻¹=2*(energy ζ-(Real.cos c:ℂ))) : NickelAt ζ (2*N) := by
  have hu : (Complex.exp ((c:ℂ)*Complex.I))^N=signValue σ := by
    rwa [←exp_nat_real_angle]
  obtain ⟨l,hl⟩ := IsingBulk.Preferred22.preferred_root_of_unity_angle
    (by omega : 0<2*N) (signed_root_pow_double hu)
  obtain ⟨m,hm⟩ := IsingBulk.Preferred22.preferred_root_of_unity_angle
    (by omega : 0<2*N) (signed_root_pow_double hprod)
  have huc := exp_angle_add_inv c
  rw [hl] at huc
  have hlc := exp_angle_add_inv (angle (2*N) l)
  have hmc := exp_angle_add_inv (angle (2*N) m)
  change IsingBulk.PrimeFamily.angleRoot (2*N) l+(IsingBulk.PrimeFamily.angleRoot (2*N) l)⁻¹=_ at hlc
  change IsingBulk.PrimeFamily.angleRoot (2*N) m+(IsingBulk.PrimeFamily.angleRoot (2*N) m)⁻¹=_ at hmc
  rw [hm,hmc] at htrace
  refine ⟨hζ,l,m,?_⟩
  change energy ζ=_
  linear_combination -htrace/2+(hlc-huc)/2

/-- No signed finite collision is present below p/2.  In particular this
uniformly removes every finite coefficient N≤M after choosing p>2M. -/
theorem prime_no_constant_signed_collision {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) {N : ℕ} (hN : 0<N) (hNp : 2*N<p)
    (σ : Sign) {z : ℂ} {c : ℝ}
    (hangle : Complex.exp ((((N:ℝ)*c:ℝ):ℂ)*Complex.I)=signValue σ)
    (htrace : z+z⁻¹=2*(energy (IsingBulk.PrimeFamily.angleRoot p a)-(Real.cos c:ℂ))) :
    z^N≠signValue σ := by
  intro hz
  exact (primeRoot_first_order hp hp5 (primeIndex_of_admissible hp.pos ha)).2.2
    (2*N) (by omega) hNp
    (constant_signed_collision_implies_nickel hN (angleRoot_unit p a) hangle hz htrace)

end
end IsoProof
