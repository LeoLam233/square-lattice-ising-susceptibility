import IsoProof.ResonanceRadial
import IsoProof.ResonancePrimes
import IsingBulk.HT22.Final.NaturalBoundary
import IsingBulk.Preferred22.CompleteRadialAsymptotics

/-! Actual complete-series producers.  The older HT asymptotic is used at
its literal order and sharp radial descent is proved in ResonanceRadial.
These are not the terminal paper conclusions: bridges to the new E-coordinate
literal coefficients and the physical normalizations are kept separate.

All premises below are prime/index arithmetic.  No analyticity, convergence,
tail estimate, noncancellation or singularity is supplied as an external input.
-/
namespace IsoProof
noncomputable section
open Complex Filter Set
open IsingBulk.PrimeFamily
open IsingBulk.HT22.Arithmetic
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The older HT order is precisely one above the sharp order in this paper. -/
theorem old_high_order_eq_sharp_add_one {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) :
    IsingBulk.HT.First.derivativeOrder p=criticalOrder p+1 := by
  have ho := hp.odd_of_ne_two (by omega)
  have hnew := odd_square_criticalOrder (by omega : 2≤p) ho
  have hold := IsingBulk.HT.First.odd_square_order ho
  omega

/-- Complete signed high-temperature sum, at the sharp order.  The exact
physical radial path, its complex tangent, both effective signs, and every
strictly lower derivative are retained. -/
theorem high_prime_sharp_full_sum {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    Tendsto (fun t : ℝ =>
      ‖iteratedDeriv (criticalOrder p)
        (IsingBulk.HT22.Physical.signedOddSeries (negativeSide (angle p a)))
        (IsingBulk.Branch.radialParameter (primeBranchData hp hp5 ha).alpha t)‖)
      (𝓝[>] 0) atTop ∧
    ∀ j : ℕ,j<criticalOrder p → ∃ δ C : ℝ,0<δ ∧ 0<C ∧
      ∀ t ∈ Ioc 0 δ,
        ‖iteratedDeriv j
          (IsingBulk.HT22.Physical.signedOddSeries (negativeSide (angle p a)))
          (IsingBulk.Branch.radialParameter (primeBranchData hp hp5 ha).alpha t)‖≤C := by
  obtain ⟨hL,hlim⟩ := IsingBulk.HT22.Final.actual_prime_full_limit hp hp5 ha
  have horder := old_high_order_eq_sharp_add_one hp hp5
  rw [horder] at hlim
  let ζ := Complex.exp (((primeBranchData hp hp5 ha).alpha:ℂ)*Complex.I)
  have hζ : ‖ζ‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hk : 1≤criticalOrder p := by
    have hsq := odd_square_criticalOrder (by omega : 2≤p)
      (hp.odd_of_ne_two (by omega))
    nlinarith
  have h := sharp_radial_jets_of_simple_pole hζ hL (criticalOrder p) hk
    (fun t ht => IsingBulk.HT22.Physical.signedOddSeries_analyticAt _
      (IsingBulk.Preferred22.radialPath_exterior hζ ht)) (by
        simpa only [Complex.real_smul,IsingBulk.Branch.radialParameter,
          Complex.ofReal_add,Complex.ofReal_one,ζ] using hlim)
  simpa only [IsingBulk.Branch.radialParameter,Complex.ofReal_add,
    Complex.ofReal_one,ζ] using h

/-- The even critical order agrees literally with the older LT order. -/
theorem old_low_order_eq_sharp {p : ℕ} (hp : 1≤p) :
    (2*p)^2/2-1=criticalOrder (2*p) := by
  have he : Even (2*p) := ⟨p,by ring⟩
  have hsq := even_square_criticalOrder (by omega : 2≤2*p) he
  omega

/-- Complete positive-even low-temperature sum.  Its nonzero square-root
amplitude is already constructed by the concrete old integral chain; the
new statement exposes sharp derivative divergence and finite lower limits. -/
theorem low_prime_sharp_full_sum {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) :
    Tendsto (fun t : ℝ =>
      ‖iteratedDeriv (criticalOrder (2*p)) IsingBulk.Preferred22.evenSeries
        ((1+(t:ℂ))*IsingBulk.PrimeFamily.angleRoot p a)‖)
      (𝓝[>] 0) atTop ∧
    ∀ j : ℕ,j<criticalOrder (2*p) → ∃ L : ℂ,
      Tendsto (fun t : ℝ => iteratedDeriv j IsingBulk.Preferred22.evenSeries
        ((1+(t:ℂ))*IsingBulk.PrimeFamily.angleRoot p a)) (𝓝[>] 0) (𝓝 L) := by
  have horder := old_low_order_eq_sharp (by omega : 1≤p)
  obtain ⟨hL,hlim⟩ :=
    IsingBulk.Preferred22.preferred_prime_evenSeries_explicit_limit hp hp5 ha
  rw [horder] at hlim
  refine ⟨norm_tendsto_atTop_of_sqrt_scaled_limit hL hlim,?_⟩
  intro j hj
  exact IsingBulk.Preferred22.preferred_prime_evenSeries_lower_derivative_limits
    hp hp5 ha j (by simpa only [horder] using hj)

end
end IsoProof
