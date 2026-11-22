import IsoProof.ResonanceDescent
import IsoProof.ResonanceArithmetic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Actual complex derivatives along an affine radial approach.  This module
proves the sharp lower-order divergence and bounded lower jets from a
one-order-higher simple-pole asymptotic.  The asymptotic is an explicitly
named input only in this generic calculus lemma; the Ising instantiation is
separate in ResonanceFullSeries. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

private theorem analyticAt_complexJet {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (j : ℕ) :
    AnalyticAt ℂ (iteratedDeriv j f) s := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

/-- The tangent ζ is retained in the real derivative of the complex jet. -/
theorem affine_radial_complexJet_hasDerivAt {f : ℂ → ℂ}
    (ζ : ℂ) (t : ℝ) (j : ℕ)
    (hf : AnalyticAt ℂ f ((1+(t:ℂ))*ζ)) :
    HasDerivAt (fun x : ℝ => iteratedDeriv j f ((1+(x:ℂ))*ζ))
      (ζ*iteratedDeriv (j+1) f ((1+(t:ℂ))*ζ)) t := by
  have hd := (analyticAt_complexJet hf j).differentiableAt.hasDerivAt
  have hp : HasDerivAt (fun z : ℂ => (1+z)*ζ) ζ (t:ℂ) := by
    simpa using ((hasDerivAt_id (t:ℂ)).const_add 1).mul_const ζ
  convert! (hd.comp (t:ℂ) hp).comp_ofReal using 1
  simp only [iteratedDeriv_succ,mul_comm]

/-- One higher simple pole implies exactly the short paper's critical-order
norm divergence and boundedness at every strictly lower order. -/
theorem sharp_radial_jets_of_simple_pole {f : ℂ → ℂ} {ζ L : ℂ}
    (hζ : ‖ζ‖=1) (hL : L≠0) (k : ℕ) (hk : 1≤k)
    (hf : ∀ t : ℝ,0<t → AnalyticAt ℂ f ((1+(t:ℂ))*ζ))
    (hlim : Tendsto (fun t : ℝ => (t:ℂ)*iteratedDeriv (k+1) f ((1+(t:ℂ))*ζ))
      (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun t : ℝ => ‖iteratedDeriv k f ((1+(t:ℂ))*ζ)‖)
      (𝓝[>] 0) atTop ∧
    ∀ j : ℕ,j<k → ∃ a C : ℝ,0<a ∧ 0<C ∧
      ∀ t ∈ Ioc 0 a, ‖iteratedDeriv j f ((1+(t:ℂ))*ζ)‖≤C := by
  have hζ0 : ζ≠0 := by intro h; simp [h] at hζ
  have hd (j : ℕ) (t : ℝ) (ht : 0<t) :=
    affine_radial_complexJet_hasDerivAt ζ t j (hf t ht)
  constructor
  · apply norm_tendsto_atTop_of_simple_pole_derivative (mul_ne_zero hζ0 hL)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hd k t ht
    · convert hlim.const_mul ζ using 1
      funext t
      ring
  · have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0,
        ‖iteratedDeriv (k+1) f ((1+(t:ℂ))*ζ)‖≤(‖L‖+1)/t := by
      have he := hlim.norm.eventually (eventually_lt_nhds (lt_add_one ‖L‖))
      filter_upwards [he,self_mem_nhdsWithin] with t ht ht0
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0] at ht
      apply (le_div_iff₀ ht0).mpr
      simpa only [mul_comm] using ht.le
    obtain ⟨d,hd0,hdbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbound
    change 0<d at hd0
    let a := d/2
    have ha : 0<a := by dsimp [a]; positivity
    have hfull := IsingBulk.HT.First.sharp_lower_jets_of_top_inv_bound
      (F := fun j t => iteratedDeriv j f ((1+(t:ℂ))*ζ))
      ha (show 0≤‖L‖+1 by positivity) (show 2≤k+1 by omega) hζ
      (fun j t ht => hd j t ht.1) (by
        intro t ht
        exact hdbound ⟨ht.1,ht.2.trans_lt (by dsimp [a]; linarith)⟩)
    intro j hj
    obtain ⟨C,hC,hCb⟩ := hfull.2 j (by omega)
    exact ⟨a,C,ha,hC,hCb⟩

/-- The even-particle square-root asymptotic immediately gives divergence of
its actual critical derivative. -/
theorem norm_tendsto_atTop_of_sqrt_scaled_limit {F : ℝ → ℂ} {L : ℂ}
    (hL : L≠0)
    (hlim : Tendsto (fun t : ℝ => Real.sqrt t • F t) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun t : ℝ => ‖F t‖) (𝓝[>] 0) atTop := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.sqrt_pos.mpr ht
  have hi := tendsto_inv_nhdsGT_zero.comp hs
  have h := hi.atTop_mul_pos (norm_pos_iff.mpr hL) hlim.norm
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Function.comp_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg t)]
  rw [←mul_assoc,inv_mul_cancel₀ (Real.sqrt_pos.mpr ht).ne',one_mul]

end
end IsoProof
