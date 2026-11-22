import IsoProof.ResonanceArithmetic
import IsingBulk.HT22.Arithmetic.PrimeDensity
import IsingBulk.HT22.Arithmetic.EndpointBranch

/-! A sufficient, explicit prime subfamily of the short paper's angular
meshes.  The older prime arithmetic is reused only after exposing its full
range.  Arbitrarily large particle orders are included, as required by the
separant argument; deleting finitely many low orders preserves density. -/
namespace IsoProof
noncomputable section
open IsingBulk.PrimeFamily
open IsingBulk.HT22.Arithmetic

/-- The elementary mesh proof, with a freely prescribed lower prime bound. -/
theorem neighboring_prime_angles_above (P : ℕ) {t ε : ℝ}
    (ht : 0<t) (htπ : t<Real.pi/2) (hε : 0<ε) :
    ∃ p : ℕ, ∃ a b : ℤ, p.Prime ∧ 11≤p ∧ P≤p ∧ a≠b ∧
      Admissible p a ∧ Admissible p b ∧
      |angle p a-t|<ε ∧ |angle p b-t|<ε := by
  let δ := min t (min (Real.pi/2-t) ε)
  have hδ : 0<δ := lt_min ht (lt_min (sub_pos.mpr htπ) hε)
  obtain ⟨M,hM⟩ := exists_nat_gt (2*Real.pi/δ)
  obtain ⟨p,hpM,hp⟩ := Nat.exists_infinite_primes (max M (max P 11))
  have hp11 : 11≤p := (le_max_right P 11).trans
    ((le_max_right M (max P 11)).trans hpM)
  have hpP : P≤p := (le_max_left P 11).trans
    ((le_max_right M (max P 11)).trans hpM)
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hMp : (M:ℝ)≤p := by exact_mod_cast (le_max_left M (max P 11)).trans hpM
  let h : ℝ := 2*Real.pi/p
  have hh : 0<h := div_pos (by positivity) hpR
  have hhδ : h<δ := by
    apply (div_lt_iff₀ hpR).mpr
    have := (div_lt_iff₀ hδ).mp (hM.trans_le hMp)
    nlinarith
  have hht : h<t := hhδ.trans_le (min_le_left _ _)
  have hhπ : h<Real.pi/2-t :=
    hhδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhε : h<ε := hhδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let a : ℤ := ⌊t/h⌋
  let b : ℤ := a+1
  have ha : (a:ℝ)≤t/h := Int.floor_le _
  have hb : t/h<(a:ℝ)+1 := Int.lt_floor_add_one _
  have ha' : h*(a:ℝ)≤t := by nlinarith [(le_div_iff₀ hh).mp ha]
  have hb' : t<h*((a:ℝ)+1) := by nlinarith [(div_lt_iff₀ hh).mp hb]
  have ea : angle p a=h*(a:ℝ) := by unfold angle h; ring
  have eb : angle p b=h*((a:ℝ)+1) := by unfold angle b h; push_cast; ring
  refine ⟨p,a,b,hp,hp11,hpP,by dsimp [b]; omega,?_,?_,?_,?_⟩
  · unfold Admissible
    rw [ea]
    constructor <;> linarith
  · unfold Admissible
    rw [eb]
    constructor <;> linarith
  · rw [ea,abs_lt]
    constructor <;> linarith
  · rw [eb,abs_lt]
    constructor <;> linarith

/-- This contains only actually specified primitive prime roots. -/
def primeRootsAbove (P : ℕ) : Set ℂ :=
  {z | ∃ p : ℕ, ∃ a : ℤ, p.Prime ∧ 5≤p ∧ P≤p ∧ PrimeIndex p a ∧
    z=IsingBulk.PrimeFamily.angleRoot p a}

/-- Removing an arbitrary bounded range of particle numbers leaves a dense
family on each upper unit-circle arc. -/
theorem primeRootsAbove_dense_upper (P : ℕ) {t : ℝ} (ht : 0<t) (htπ : t<Real.pi) :
    Complex.exp ((t:ℂ)*Complex.I) ∈ closure (primeRootsAbove P) := by
  let f : ℝ → ℂ := fun u => Complex.exp ((u:ℂ)*Complex.I)
  have hf : Continuous f := Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul_const Complex.I)
  change f t ∈ closure (primeRootsAbove P)
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
  obtain ⟨p,a,b,hp,hp11,hpP,_hab,ha,_hb,hea,_heb⟩ :=
    neighboring_prime_angles_above P (by linarith : 0<t/2)
      (by linarith : t/2<Real.pi/2) (by linarith : 0<δ/2)
  refine ⟨IsingBulk.PrimeFamily.angleRoot p (2*a),
    ⟨p,2*a,hp,by omega,hpP,primeIndex_double_of_admissible hp.pos ha,rfl⟩,?_⟩
  rw [dist_comm]
  apply hcont
  rw [Real.dist_eq,angle_double_index]
  rw [abs_lt] at hea ⊢
  constructor <;> linarith

/-- Both phase critical orders can be required to exceed the proposed
order of a differential equation without losing density. -/
def primeRootsWithHighCriticalOrder (r : ℕ) : Set ℂ :=
  {z | ∃ p : ℕ, ∃ a : ℤ, p.Prime ∧ 5≤p ∧ PrimeIndex p a ∧
    r<criticalOrder p ∧ r<criticalOrder (2*p) ∧
    z=IsingBulk.PrimeFamily.angleRoot p a}

theorem primeRootsWithHighCriticalOrder_dense (r : ℕ) {t : ℝ}
    (ht : 0<t) (htπ : t<Real.pi) :
    Complex.exp ((t:ℂ)*Complex.I) ∈ closure (primeRootsWithHighCriticalOrder r) := by
  apply (closure_mono (s := primeRootsAbove (2*r+4)) (t := primeRootsWithHighCriticalOrder r) ?_)
    (primeRootsAbove_dense_upper (2*r+4) ht htπ)
  rintro z ⟨p,a,hp,hp5,hpP,ha,rfl⟩
  exact ⟨p,a,hp,hp5,ha,criticalOrder_unbounded r p hpP,
    criticalOrder_unbounded r (2*p) (by omega),rfl⟩

/-- The first-quadrant mesh is simultaneously admissible for both actual
complete-series asymptotic producers. -/
theorem primeIndex_of_admissible {p : ℕ} (hp : 0<p) {a : ℤ}
    (ha : Admissible p a) : PrimeIndex p a := by
  obtain ⟨htwo0,htwo⟩ := primeIndex_double_of_admissible hp ha
  have ha0 := (admissible_integer_bounds hp ha).1
  constructor <;> omega

/-- A common first-quadrant family with a prescribed lower prime bound. -/
def commonPrimeRootsAbove (P : ℕ) : Set ℂ :=
  {z | ∃ p : ℕ,∃ a : ℤ,p.Prime ∧ 5≤p ∧ P≤p ∧ Admissible p a ∧
    z=IsingBulk.PrimeFamily.angleRoot p a}

theorem commonPrimeRootsAbove_dense (P : ℕ) {t : ℝ}
    (ht : 0<t) (htπ : t<Real.pi/2) :
    Complex.exp ((t:ℂ)*Complex.I)∈closure (commonPrimeRootsAbove P) := by
  let f : ℝ→ℂ := fun u => Complex.exp ((u:ℂ)*Complex.I)
  have hf : Continuous f := Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul_const Complex.I)
  change f t∈closure (commonPrimeRootsAbove P)
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hf.continuousAt ε hε
  obtain ⟨p,a,b,hp,hp11,hpP,_hab,ha,_hb,hea,_heb⟩ :=
    neighboring_prime_angles_above P ht htπ hδ
  refine ⟨IsingBulk.PrimeFamily.angleRoot p a,⟨p,a,hp,by omega,hpP,ha,rfl⟩,?_⟩
  rw [dist_comm]
  apply hcont
  simpa only [Real.dist_eq] using hea

/-- In the common family both sharp derivative orders can exceed any fixed
finite differential order. -/
def commonPrimeRootsWithHighCriticalOrder (r : ℕ) : Set ℂ :=
  {z | ∃ p : ℕ,∃ a : ℤ,p.Prime ∧ 5≤p ∧ Admissible p a ∧
    r<criticalOrder p ∧ r<criticalOrder (2*p) ∧
    z=IsingBulk.PrimeFamily.angleRoot p a}

theorem commonPrimeRootsWithHighCriticalOrder_dense (r : ℕ) {t : ℝ}
    (ht : 0<t) (htπ : t<Real.pi/2) :
    Complex.exp ((t:ℂ)*Complex.I)∈closure (commonPrimeRootsWithHighCriticalOrder r) := by
  apply (closure_mono (s:=commonPrimeRootsAbove (2*r+4))
    (t:=commonPrimeRootsWithHighCriticalOrder r) ?_)
    (commonPrimeRootsAbove_dense (2*r+4) ht htπ)
  rintro z ⟨p,a,hp,hp5,hpP,ha,rfl⟩
  exact ⟨p,a,hp,hp5,ha,criticalOrder_unbounded r p hpP,
    criticalOrder_unbounded r (2*p) (by omega),rfl⟩

/-- The same selected family has neither endpoint sign at any positive
particle number.  This is the prime-family specialization of the manuscript's
more general algebraic-integer exclusion. -/
theorem prime_endpoint_all_orders {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (N : ℕ) (hN : 0<N) :
    endpointBranch p a^N≠1 ∧ endpointBranch p a^N≠ -1 :=
  endpointBranch_pow_ne_signs hp hp5 ha N hN

end
end IsoProof
