import IsoProof.ContourSiteEnvelope
import IsoProof.ContourGraphGaussian
import IsoProof.ContourCauchy
import IsoProof.TailNumerics
import IsoProof.IntegralsSiteContinuation
import IsoProof.SiteSymmetry
import IsoProof.SiteBaire

/-! Equation (6) for the actual original site coefficients. The Cauchy
function is the fixed-graph continuation, and its derivatives are identified
with the physical site function by the proved germ identity. -/
namespace IsoProof
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators
set_option maxHeartbeats 600000

def graphIntegrationConstant (b v β C : ℝ) : ℝ :=
  max 1 (‖((2*(Real.pi : ℂ))⁻¹)‖*C*(3*graphJacobianBound b v)*Real.sqrt (Real.pi/β))

theorem graphIntegrationConstant_pos (b v β C : ℝ) : 0 < graphIntegrationConstant b v β C :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem graphSiteCoefficient_gaussian_bound {b β C : ℝ} (hb : 0 < b)
    (hbpi : b < Real.pi) (hβ : 0 < β) (hC : 0 ≤ C) (v c : ℝ)
    (N A B : ℕ) (E : ℂ)
    (hF : ∀ r : Fin N → ℝ, (∀ i, r i ∈ Icc (-Real.pi) Real.pi) →
      ‖continuedSiteDensity A (B : ℤ) E (fun i => scalarGraph b v (r i) c)‖ ≤
        (C*(N : ℝ)^(3/4 : ℝ))^N*centeredGaussian N (β*(1+(A : ℝ))) c r) :
    ‖graphSiteCoefficient b v c N A (B : ℤ) E‖ ≤
      siteOrderEnvelope (graphIntegrationConstant b v β C) N*
        (1+(A : ℝ))^(-(N : ℝ)/2) := by
  have hbase : 0 < 1+(A : ℝ) := by positivity
  have hG := protectedGraphMultiIntegral_gaussian_bound hb hbpi (mul_pos hβ hbase) v c N
    (by positivity : 0 ≤ (C*(N : ℝ)^(3/4 : ℝ))^N)
    (continuedSiteDensity A (B : ℤ) E) hF
  have hfac : ‖(N.factorial : ℂ)⁻¹‖ = (N.factorial : ℝ)⁻¹ := by simp
  unfold graphSiteCoefficient
  rw [norm_mul,norm_mul,norm_pow,hfac]
  have h := mul_le_mul_of_nonneg_left hG
    (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N.factorial))
      (pow_nonneg (norm_nonneg (((2*(Real.pi : ℂ))⁻¹))) N))
  apply h.trans
  simp only [mul_pow]
  rw [gaussian_N_shifted_scaling N hβ (Nat.cast_nonneg A)]
  let T := ‖((2*(Real.pi : ℂ))⁻¹)‖*C*(3*graphJacobianBound b v)*Real.sqrt (Real.pi/β)
  have hT : 0 ≤ T := by
    have hJ := graphJacobianBound_nonneg b v
    dsimp [T]
    positivity
  have hconst : T ≤ graphIntegrationConstant b v β C := le_max_right _ _
  have hp := pow_le_pow_left₀ (mul_nonneg hT (Real.rpow_nonneg (Nat.cast_nonneg N) (3/4 : ℝ)))
    (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (Nat.cast_nonneg N) (3/4 : ℝ))) N
  have h' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg N.factorial)))
    (Real.rpow_nonneg hbase.le (-(N : ℝ)/2))
  convert h' using 1 <;> simp only [siteOrderEnvelope,T,div_eq_mul_inv,mul_pow] <;> ring

/-- Actual sector estimate, with constants uniform in all particle numbers,
all lattice radii including zero, and every upper energy height in a fixed
positive interval. No contour or asymptotic bound is assumed. -/
theorem siteCoefficient_sector_jet_bound {x : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (j : ℕ) :
    ∃ C > 0, ∃ Y > 0, ∀ N : ℕ, 0 < N → ∀ A B : ℕ, B ≤ A →
      ∀ y : ℝ, 0 < y → y ≤ Y →
        ‖iteratedDeriv j (siteCoefficient N A (B : ℤ))
          ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤
          siteOrderEnvelope C N*(1+(A : ℝ))^((j : ℝ)-(N : ℝ)/2) := by
  let d := stationaryHalfWidth x
  obtain ⟨hd,hdb⟩ := stationaryHalfWidth_range hx hx2
  obtain ⟨ε,hε,hbound⟩ := common_graph_density_gaussian hx hx2 hd.le hdb
  obtain ⟨εg,hεg,hgerm⟩ := common_graph_site_germ hx hx2 hd.le hdb
  let v := min ε εg/2
  have hv : 0 < v := by dsimp [v]; positivity
  have hvε : v < ε := by dsimp [v]; linarith [min_le_left ε εg,lt_min hε hεg]
  have hvεg : v < εg := by dsimp [v]; linarith [min_le_right ε εg,lt_min hε hεg]
  obtain ⟨R,hR,Y,hY,C,hC,β,hβ,hDom,hF⟩ := hbound v hv hvε
  let C0 := graphIntegrationConstant (cutHalfWidth x) v β C
  let K := (j.factorial : ℝ)/R^j
  let Cj := max 1 K*C0
  have hC0 : 0 < C0 := graphIntegrationConstant_pos _ _ _ _
  have hCj : 0 < Cj := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) hC0
  refine ⟨Cj,hCj,Y,hY,?_⟩
  intro N hN A B hBA y hy hyY
  have hratio : (B : ℝ)/(A : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · by_cases hA : A=0
      · simp [hA]
      · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hA : (0 : ℝ) < A)).mpr
        exact_mod_cast hBA
  obtain ⟨c,hc,hslope⟩ := stationary_center_exists hx hx2 hratio
  have hc' : c ∈ Icc (-d) d := ⟨hc.1,hc.2.trans hd.le⟩
  let E : ℂ := (x : ℂ)+Complex.I*(y : ℂ)
  let f := graphSiteCoefficient (cutHalfWidth x) v c N A (B : ℤ)
  have ha : AnalyticOnNhd ℂ f (closedBall E (R/(1+(A : ℝ)))) := by
    intro z hz
    apply graphSiteCoefficient_analyticAt (cutHalfWidth_range hx hx2).1
      (cutHalfWidth_range hx hx2).2 v c N A (B : ℤ) z
    intro r hr
    have he : ‖z-E‖ ≤ R := (show ‖z-E‖ ≤ R/(1+(A : ℝ)) by
      simpa only [mem_closedBall,dist_eq_norm] using hz).trans
        (div_le_self hR.le (by linarith [show 0 ≤ (A : ℝ) from Nat.cast_nonneg A]))
    have h := hDom y ⟨hy.le,hyY⟩ c hc' (z-E) he r hr
    convert h using 1
    dsimp [E]
    ring
  have hf : DiffContOnCl ℂ f (ball E (R/(1+(A : ℝ)))) :=
    DiffContOnCl.mk_ball (ha.differentiableOn.mono ball_subset_closedBall) ha.continuousOn
  have hsphere : ∀ z ∈ sphere E (R/(1+(A : ℝ))),
      ‖f z‖ ≤ siteOrderEnvelope C0 N*(1+(A : ℝ))^(-(N : ℝ)/2) := by
    intro z hz
    have he : ‖z-E‖ ≤ R/(1+(A : ℝ)) := by
      simpa only [mem_sphere,dist_eq_norm] using le_of_eq hz
    have hb := graphSiteCoefficient_gaussian_bound (cutHalfWidth_range hx hx2).1
      (cutHalfWidth_range hx hx2).2 hβ hC.le v c N A B z (by
        intro r hr
        have h := hF N hN A B hBA c hc' hslope y ⟨hy.le,hyY⟩ (z-E) he r hr
        convert h using 1
        dsimp [E]
        ring)
    exact hb
  have hjet := cauchy_site_exponent f E A N j hR hf hsphere
  have hsame := (hgerm v hv hvεg c hc' y hy N A (B : ℤ)).iteratedDeriv_eq j
  rw [hsame]
  apply hjet.trans
  have hnum := fixed_factor_absorbed K C0 ((N : ℝ)^(3/4 : ℝ)) hC0.le
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) hN
  have hd' := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg N.factorial)
  have h := mul_le_mul_of_nonneg_right hd'
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1+(A : ℝ)) ((j : ℝ)-(N : ℝ)/2))
  convert h using 1 <;> simp only [siteOrderEnvelope,Cj,K,div_eq_mul_inv]
  ring

/-- Equation (6) for every signed lattice site. The maximum radius and all
axes are supplied by the actual two-axis symmetry theorem. -/
theorem siteCoefficient_lattice_jet_bound {x : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (j : ℕ) :
    ∃ C > 0, ∃ Y > 0, ∀ y : ℝ, 0 < y → y ≤ Y →
      ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ,
        ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2)
          ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤ siteOrderEnvelope C N*siteSpatialWeight j N p := by
  obtain ⟨C,hC,Y,hY,hb⟩ := siteCoefficient_sector_jet_bound hx hx2 j
  refine ⟨C,hC,Y,hY,?_⟩
  intro y hy hyY N hN p
  have hE : (x : ℂ)+Complex.I*(y : ℂ) ∈ energyDomain := Or.inl (by simpa using hy.ne')
  rw [siteCoefficient_square_sector_jet N hN p j hE]
  exact hb N hN (max p.1.natAbs p.2.natAbs) (min p.1.natAbs p.2.natAbs)
    (min_le_left _ _ |>.trans (le_max_left _ _)) y hy hyY

/-- A nondegenerate interval with the actual simultaneous finite-jet site
bound. This closes the local quantitative input of the Baire argument. -/
theorem siteCoefficient_uniform_jet_interval (n : ℕ) {l u : ℝ}
    (hl : 0 < l) (hlu : l < u) (hu : u < 2) :
    ∃ a b C R : ℝ, l < a ∧ a < b ∧ b < u ∧ 0 < C ∧ 0 < R ∧
      ∀ x ∈ Icc a b, ∀ j < n, ∀ y : ℝ, 0 < y → y ≤ R →
        ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ,
          ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2)
            ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤ siteOrderEnvelope C N*siteSpatialWeight j N p :=
  site_jet_uniform_interval n hl hlu hu
    (fun j _hj _x hx hx2 => siteCoefficient_lattice_jet_bound hx hx2 j)

end
end IsoProof
