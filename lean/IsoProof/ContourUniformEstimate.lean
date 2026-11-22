import IsoProof.ContourUniformEnvelope
import IsoProof.ContourSiteEstimate
import IsoProof.IntegralsSiteIdentity

/-! Locally uniform form of equation (6), with one actual fixed graph and
one constant for a neighborhood of the real energy. -/
namespace IsoProof
noncomputable section
open Set Metric Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem stationary_centers_locally_uniform {x₀ : ℝ} (hx : 0 < x₀) (hx2 : x₀ < 2) :
    ∃ d > 0, d < cutHalfWidth x₀ ∧ ∃ ρ > 0,
      ∀ x : ℝ, |x-x₀| < ρ → 0 < x ∧ x < 2 ∧ stationaryHalfWidth x < d := by
  obtain ⟨hs,hsb⟩ := stationaryHalfWidth_range hx hx2
  let d := (stationaryHalfWidth x₀+cutHalfWidth x₀)/2
  have hd : 0 < d := by dsimp [d]; linarith
  have hdb : d < cutHalfWidth x₀ := by dsimp [d]; linarith
  have hsd : stationaryHalfWidth x₀ < d := by dsimp [d]; linarith
  have hopen : IsOpen {x : ℝ | 0 < x ∧ x < 2 ∧ stationaryHalfWidth x < d} := by
    have h1 : IsOpen {x : ℝ | 0 < x} := isOpen_lt continuous_const continuous_id
    have h2 : IsOpen {x : ℝ | x < 2} := isOpen_lt continuous_id continuous_const
    have h3 : IsOpen {x : ℝ | stationaryHalfWidth x < d} :=
      isOpen_lt (by unfold stationaryHalfWidth; fun_prop) continuous_const
    exact h1.inter (h2.inter h3)
  obtain ⟨ρ,hρ,hprop⟩ := Metric.eventually_nhds_iff.mp (hopen.mem_nhds ⟨hx,hx2,hsd⟩)
  exact ⟨d,hd,hdb,ρ,hρ,fun x hxx => hprop (y := x) (by simpa only [Real.dist_eq] using hxx)⟩

theorem siteCoefficient_sector_jet_bound_locally_uniform {x₀ : ℝ}
    (hx : 0 < x₀) (hx2 : x₀ < 2) (j : ℕ) :
    ∃ ρ > 0, ∃ C > 0, ∃ Y > 0, ∀ x : ℝ, |x-x₀| < ρ →
      ∀ N : ℕ, 0 < N → ∀ A B : ℕ, B ≤ A →
      ∀ y : ℝ, 0 < y → y ≤ Y →
        ‖iteratedDeriv j (siteCoefficient N A (B : ℤ)) ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤
          siteOrderEnvelope C N*(1+(A : ℝ))^((j : ℝ)-(N : ℝ)/2) := by
  obtain ⟨d,hd,hdb,ρc,hρc,hcenter⟩ := stationary_centers_locally_uniform hx hx2
  obtain ⟨ε,hε,hbound⟩ := common_fixed_graph_density_gaussian hx hx2 hd.le hdb
  obtain ⟨εg,hεg,hidentity⟩ := common_graph_site_identity_on_upper_rectangle hx hx2 hd.le hdb
  let v := min ε εg/2
  have hv : 0 < v := by dsimp [v]; positivity
  have hvε : v < ε := by dsimp [v]; linarith [min_le_left ε εg,lt_min hε hεg]
  have hvεg : v < εg := by dsimp [v]; linarith [min_le_right ε εg,lt_min hε hεg]
  obtain ⟨ρ,hρ,R,hR,Y,hY,C,hC,β,hβ,hDom,hF⟩ := hbound v hv hvε
  let C0 := graphIntegrationConstant (cutHalfWidth x₀) v β C
  let K := (j.factorial : ℝ)/R^j
  let Cj := max 1 K*C0
  have hC0 : 0 < C0 := graphIntegrationConstant_pos _ _ _ _
  have hCj : 0 < Cj := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) hC0
  have hId (c : ℝ) (hc : c∈Icc (-d) d) (N A B : ℕ) :
      EqOn (graphSiteCoefficient (cutHalfWidth x₀) v c N A (B : ℤ))
        (siteCoefficient N A (B : ℤ)) (siteUpperRectangle x₀ ρ Y) := by
    apply hidentity v hv hvεg c hc ρ Y hρ hY _ N A (B : ℤ)
    intro E hE r hr
    have hleft : x₀-ρ < E.re := hE.1.1.1
    have hright : E.re < x₀+ρ := hE.1.1.2
    have hxx : |E.re-x₀| < ρ := abs_lt.mpr ⟨by linarith,by linarith⟩
    have h := hDom E.re hxx E.im ⟨hE.1.2.le,hE.2.le⟩ c hc 0
      (by simpa using hR.le) r hr
    simpa only [add_zero,mul_comm Complex.I,Complex.re_add_im] using h
  refine ⟨min ρ ρc,lt_min hρ hρc,Cj,hCj,Y/2,half_pos hY,?_⟩
  intro x hxx N hN A B hBA y hy hyY
  have hxρ : |x-x₀| < ρ := hxx.trans_le (min_le_left _ _)
  obtain ⟨hx',hx2',hsd⟩ := hcenter x (hxx.trans_le (min_le_right _ _))
  have hyY' : y ≤ Y := hyY.trans (half_le_self hY.le)
  have hyYlt : y < Y := hyY.trans_lt (half_lt_self hY)
  have hratio : (B : ℝ)/(A : ℝ)∈Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · by_cases hA : A=0
      · simp [hA]
      · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hA : (0 : ℝ) < A)).mpr
        exact_mod_cast hBA
  obtain ⟨c,hc,hslope⟩ := stationary_center_exists hx' hx2' hratio
  have hc' : c∈Icc (-d) d := ⟨by linarith [hc.1],hc.2.trans hd.le⟩
  let E : ℂ := (x : ℂ)+Complex.I*(y : ℂ)
  let f := graphSiteCoefficient (cutHalfWidth x₀) v c N A (B : ℤ)
  have ha : AnalyticOnNhd ℂ f (closedBall E (R/(1+(A : ℝ)))) := by
    intro z hz
    apply graphSiteCoefficient_analyticAt (cutHalfWidth_range hx hx2).1
      (cutHalfWidth_range hx hx2).2 v c N A (B : ℤ) z
    intro r hr
    have he : ‖z-E‖ ≤ R := (show ‖z-E‖ ≤ R/(1+(A : ℝ)) by
      simpa only [mem_closedBall,dist_eq_norm] using hz).trans
        (div_le_self hR.le (by linarith [show 0 ≤ (A : ℝ) from Nat.cast_nonneg A]))
    have h := hDom x hxρ y ⟨hy.le,hyY'⟩ c hc' (z-E) he r hr
    convert h using 1
    dsimp [E]
    ring
  have hf : DiffContOnCl ℂ f (ball E (R/(1+(A : ℝ)))) :=
    DiffContOnCl.mk_ball (ha.differentiableOn.mono ball_subset_closedBall) ha.continuousOn
  have hsphere : ∀ z∈sphere E (R/(1+(A : ℝ))),
      ‖f z‖ ≤ siteOrderEnvelope C0 N*(1+(A : ℝ))^(-(N : ℝ)/2) := by
    intro z hz
    have he : ‖z-E‖ ≤ R/(1+(A : ℝ)) := by
      simpa only [mem_sphere,dist_eq_norm] using le_of_eq hz
    exact graphSiteCoefficient_gaussian_bound (cutHalfWidth_range hx hx2).1
      (cutHalfWidth_range hx hx2).2 hβ hC.le v c N A B z (by
        intro r hr
        have h := hF x hxρ N hN A B hBA c hc' hslope y ⟨hy.le,hyY'⟩ (z-E) he r hr
        convert h using 1
        dsimp [E]
        ring)
  have hjet := cauchy_site_exponent f E A N j hR hf hsphere
  have hE : E∈siteUpperRectangle x₀ ρ Y := by
    have hEre : E.re=x := by simp [E]
    have hEim : E.im=y := by simp [E]
    exact ⟨⟨⟨by change x₀-ρ < E.re; rw [hEre]; linarith [(abs_lt.mp hxρ).1],
      by change E.re < x₀+ρ; rw [hEre]; linarith [(abs_lt.mp hxρ).2]⟩,
      by change 0 < E.im; rwa [hEim]⟩,by change E.im < Y; rwa [hEim]⟩
  have hgerm : siteCoefficient N A (B : ℤ) =ᶠ[𝓝 E] f := by
    filter_upwards [(siteUpperRectangle_isOpen x₀ ρ Y).mem_nhds hE] with z hz
    exact (hId c hc' N A B hz).symm
  rw [hgerm.iteratedDeriv_eq j]
  apply hjet.trans
  have hnum := fixed_factor_absorbed K C0 ((N : ℝ)^(3/4 : ℝ)) hC0.le
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) hN
  have hd' := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg N.factorial)
  have h := mul_le_mul_of_nonneg_right hd'
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1+(A : ℝ)) ((j : ℝ)-(N : ℝ)/2))
  convert h using 1 <;> simp only [siteOrderEnvelope,Cj,K,div_eq_mul_inv]
  ring

theorem siteCoefficient_lattice_jet_bound_locally_uniform {x₀ : ℝ}
    (hx : 0 < x₀) (hx2 : x₀ < 2) (j : ℕ) :
    ∃ ρ > 0, ∃ C > 0, ∃ Y > 0, ∀ x : ℝ, |x-x₀| < ρ →
      ∀ y : ℝ, 0 < y → y ≤ Y → ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ,
        ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤
          siteOrderEnvelope C N*siteSpatialWeight j N p := by
  obtain ⟨ρ,hρ,C,hC,Y,hY,hb⟩ := siteCoefficient_sector_jet_bound_locally_uniform hx hx2 j
  refine ⟨ρ,hρ,C,hC,Y,hY,?_⟩
  intro x hxx y hy hyY N hN p
  have hE : (x : ℂ)+Complex.I*(y : ℂ)∈energyDomain := Or.inl (by simpa using hy.ne')
  rw [siteCoefficient_square_sector_jet N hN p j hE]
  exact hb x hxx N hN (max p.1.natAbs p.2.natAbs) (min p.1.natAbs p.2.natAbs)
    (min_le_left _ _ |>.trans (le_max_left _ _)) y hy hyY

end
end IsoProof
