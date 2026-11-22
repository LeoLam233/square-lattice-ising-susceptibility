import IsoProof.ContourUniform
import IsoProof.ContourEnergyPair
import IsoProof.ContourSiteEnvelope

/-! The literal coupled-density bound locally uniformly in the real cut
point, on a single fixed geometric contour. -/
namespace IsoProof
noncomputable section
open Set
open scoped Topology BigOperators
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem site_exponential_bound_of_gain {A B : ℕ} (hBA : B ≤ A)
    {a v y r c lam : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) {W q : ℂ}
    (hslope : lam=(B : ℝ)/(A : ℝ))
    (hgain : a*(y+v*(r-c)^2) ≤ (((lam : ℂ)*q-continuedPhase W).im)) :
    ‖continuedTransferRoot W^A*(Complex.exp (Complex.I*q))^B‖ ≤
      Real.exp (-(a*v)*(A : ℝ)*(r-c)^2) := by
  rw [site_exponential_norm]
  apply Real.exp_le_exp.mpr
  have hAn : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
  have h := mul_le_mul_of_nonneg_left hgain hAn
  have hAB : (A : ℝ)*((B : ℝ)/(A : ℝ))=(B : ℝ) := by
    by_cases hA : A=0
    · have hB : B=0 := by omega
      simp [hA,hB]
    · have hAn0 : (A : ℝ) ≠ 0 := by exact_mod_cast hA
      field_simp
  simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero,hslope,mul_sub,← mul_assoc,hAB] at h
  nlinarith [mul_nonneg hAn (mul_nonneg ha hy)]

theorem site_exponential_disk_bound_of_gain {A B : ℕ} (hBA : B ≤ A)
    {a v y r c lam D R d : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) (hy : 0 ≤ y)
    (hD : 0 ≤ D) (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hr : r∈Icc (-Real.pi) Real.pi) (hc : c∈Icc (-d) d) {W q e : ℂ}
    (hslope : lam=(B : ℝ)/(A : ℝ))
    (hgain : a*(y+v*(r-c)^2) ≤ (((lam : ℂ)*q-continuedPhase W).im))
    (he : ‖e‖ ≤ R/(1+(A : ℝ)))
    (henergy : ‖continuedPhase (W+e)-continuedPhase W‖ ≤ D*‖e‖) :
    ‖continuedTransferRoot (W+e)^A*(Complex.exp (Complex.I*q))^B‖ ≤
      Real.exp (D+(a*v)*(Real.pi+d)^2/2)*
        Real.exp (-(a*v/2)*(1+(A : ℝ))*(r-c)^2) := by
  have hb := site_exponential_bound_of_gain hBA ha hy hslope hgain
  rw [site_exponential_norm,Real.exp_le_exp] at hb
  have he' := phase_shrinking_disk_bound hD hR hR1 he henergy
  have ht : |r-c| ≤ Real.pi+d := by
    have ht : |r-c| ≤ |r|+|c| := by simpa using abs_sub_le r 0 c
    exact ht.trans (add_le_add (abs_le.mpr hr) (abs_le.mpr hc))
  have hs := shifted_gaussian_exponent (mul_nonneg ha hv) ht A
  rw [site_exponential_norm,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Real-energy local uniformity of the genuine density estimate. The
reference point x₀ determines the one fixed piecewise graph; x is allowed
to vary throughout a fixed interval independently of A and N. -/
theorem common_fixed_graph_density_gaussian {x₀ d : ℝ} (hx : 0 < x₀) (hx2 : x₀ < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x₀) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε →
      ∃ ρ > 0, ∃ R > 0, ∃ Y > 0, ∃ C > 0, ∃ β > 0,
      (∀ x : ℝ, |x-x₀| < ρ → ∀ y∈Icc (0 : ℝ) Y, ∀ c∈Icc (-d) d,
        ∀ e : ℂ, ‖e‖ ≤ R → ∀ r∈Icc (-Real.pi) Real.pi,
          (x : ℂ)+Complex.I*(y : ℂ)+e-
            Complex.cos (scalarGraph (cutHalfWidth x₀) v r c)∈contourRootDomain) ∧
      (∀ x : ℝ, |x-x₀| < ρ → ∀ N : ℕ, 0 < N → ∀ A B : ℕ, B ≤ A →
        ∀ c∈Icc (-d) d, deriv (cutPhase x) c=(B : ℝ)/(A : ℝ) →
        ∀ y∈Icc (0 : ℝ) Y, ∀ e : ℂ, ‖e‖ ≤ R/(1+(A : ℝ)) →
        ∀ r : Fin N → ℝ, (∀ i, r i∈Icc (-Real.pi) Real.pi) →
        ‖continuedSiteDensity A (B : ℤ) ((x : ℂ)+Complex.I*(y : ℂ)+e)
          (fun i => scalarGraph (cutHalfWidth x₀) v (r i) c)‖ ≤
          (C*(N : ℝ)^(3/4 : ℝ))^N*centeredGaussian N (β*(1+(A : ℝ))) c r) := by
  obtain ⟨εp,hεp,hphase⟩ := common_phase_gain_locally_uniform hx hx2 hd hdb
  obtain ⟨εs,hεs,hscalar⟩ := common_graph_scalar_bounds hx hx2 hd hdb
  refine ⟨min εp εs,lt_min hεp hεs,?_⟩
  intro v hv hvε
  obtain ⟨ρp,hρp,a,ha,hgain⟩ := hphase v hv (hvε.trans_le (min_le_left _ _))
  obtain ⟨Rs,hRs,M,hM,δ,hδ,hDom,hy0,hy,hz,hgap⟩ :=
    hscalar v hv (hvε.trans_le (min_le_right _ _))
  let W := fun p : ℝ × (ℝ × ℝ) => graphDispersion x₀ (cutHalfWidth x₀) v p.1 p.2.1 p.2.2
  have hf := contourDisplacement_continuous (cutHalfWidth_range hx hx2).1.le
    (cutHalfWidth_range hx hx2).2
  have hW : Continuous W := by unfold W graphDispersion scalarGraph; fun_prop
  obtain ⟨D,hD,hLip⟩ := compact_phase_energy_pair_lipschitz
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) W hW Rs (by
      intro p hp e he
      have h := hDom (e,p) ⟨by simpa using he,hp⟩
      convert h using 1
      dsimp [W,commonGraphEnergy,commonGraphAngle,graphDispersion]
      ring)
  let ρ := min ρp (Rs/2)
  let R := min 1 (Rs/2)
  let Y := min 1 (ρp/2)
  have hρ : 0 < ρ := lt_min hρp (half_pos hRs)
  have hR : 0 < R := lt_min zero_lt_one (half_pos hRs)
  have hY : 0 < Y := lt_min zero_lt_one (half_pos hρp)
  let L := Real.exp (D+(a*v)*(Real.pi+d)^2/2)
  let C := (4*(pairEntryEnvelope M δ)^2)*(L*(2*M/δ))
  let β := a*v/2
  have hL : 0 < L := Real.exp_pos _
  have hentry : 0 < pairEntryEnvelope M δ := zero_lt_one.trans_le (le_max_left _ _)
  have hC : 0 < C := by dsimp [C]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have herr (x : ℝ) (hxx : |x-x₀| < ρ) (e : ℂ) (he : ‖e‖ ≤ R) :
      ‖((x-x₀ : ℝ) : ℂ)+e‖ ≤ Rs := by
    have hxR := hxx.trans_le (min_le_right ρp (Rs/2))
    have heR := he.trans (min_le_right 1 (Rs/2))
    have hn := norm_add_le (((x-x₀ : ℝ) : ℂ)) e
    rw [Complex.norm_real,Real.norm_eq_abs] at hn
    linarith
  have hyp (y : ℝ) (hyY : y∈Icc (0 : ℝ) Y) : y < ρp :=
    (hyY.2.trans (min_le_right _ _)).trans_lt (half_lt_self hρp)
  have hyone (y : ℝ) (hyY : y∈Icc (0 : ℝ) Y) : y∈Icc (0 : ℝ) 1 :=
    ⟨hyY.1,hyY.2.trans (min_le_left _ _)⟩
  refine ⟨ρ,hρ,R,hR,Y,hY,C,hC,β,hβ,?_,?_⟩
  · intro x hxx y hyY c hc e he r hr
    have ht : (((x-x₀ : ℝ) : ℂ)+e,(y,(r,c)))∈Metric.closedBall (0 : ℂ) Rs ×ˢ commonGraphBox d :=
      ⟨by simpa using herr x hxx e he,hyone y hyY,hr,hc⟩
    have h := hDom _ ht
    convert h using 1
    dsimp [commonGraphEnergy,commonGraphAngle]
    push_cast
    ring
  · intro x hxx N hN A B hBA c hc hslope y hyY e he r hr
    have heR : ‖e‖ ≤ R := he.trans (div_le_self hR.le (by
      linarith [show 0 ≤ (A : ℝ) from Nat.cast_nonneg A]))
    let e₀ : ℂ := ((x-x₀ : ℝ) : ℂ)
    let e₁ : ℂ := e₀+e
    let E : ℂ := (x : ℂ)+Complex.I*(y : ℂ)+e
    let q : Fin N → ℂ := fun i => scalarGraph (cutHalfWidth x₀) v (r i) c
    have he₀ : ‖e₀‖ ≤ Rs := by
      simpa only [e₀,add_zero] using herr x hxx (0 : ℂ) (by simpa using hR.le)
    have he₁ : ‖e₁‖ ≤ Rs := herr x hxx e heR
    have ht (i : Fin N) : (e₁,(y,(r i,c)))∈Metric.closedBall (0 : ℂ) Rs ×ˢ commonGraphBox d :=
      ⟨by simpa using he₁,hyone y hyY,hr i,hc⟩
    have hEq (i : Fin N) : commonGraphEnergy x₀ e₁ (y,(r i,c))=E := by
      dsimp [commonGraphEnergy,E,e₁,e₀]
      push_cast
      ring
    have hDom' (i : Fin N) : E-Complex.cos (q i)∈contourRootDomain := by
      simpa only [hEq,q,commonGraphAngle] using hDom _ (ht i)
    have hy0' (i : Fin N) : δ ≤ ‖continuedAnglePoint (q i)‖ := hy0 _ (ht i)
    have hy' (i : Fin N) : ‖continuedAnglePoint (q i)‖ ≤ M := hy _ (ht i)
    have hz' (i : Fin N) : ‖continuedAngleRoot E (q i)‖ ≤ M := by
      simpa only [hEq,q,continuedAngleRoot,commonGraphAngle] using hz _ (ht i)
    have hgap' (i j : Fin N) : δ ≤ ‖1-continuedAngleRoot E (q i)*continuedAngleRoot E (q j)‖ := by
      simpa only [hEq,q,continuedAngleRoot,commonGraphAngle] using hgap _ (ht i) _ (ht j)
    have hexp (i : Fin N) : ‖continuedAngleRoot E (q i)^A*continuedAnglePoint (q i)^B‖ ≤
        L*Real.exp (-(β*(1+(A : ℝ)))*(r i-c)^2) := by
      let W₁ := graphDispersion x (cutHalfWidth x₀) v y (r i) c
      have hLip' : ‖continuedPhase (W₁+e)-continuedPhase W₁‖ ≤ D*‖e‖ := by
        have h := hLip (y,(r i,c)) ⟨hyone y hyY,hr i,hc⟩ e₀ e₁ he₀ he₁
        have hW₀ : W (y,(r i,c))+e₀=W₁ := by
          dsimp [W,W₁,e₀,graphDispersion]
          push_cast
          ring
        have hW₁ : W (y,(r i,c))+e₁=W₁+e := by
          dsimp only [e₁]
          rw [← add_assoc,hW₀]
        simpa only [hW₀,hW₁,e₁,add_sub_cancel_left] using h
      have hi := site_exponential_disk_bound_of_gain hBA ha.le hv.le hyY.1 hD.le hR.le
        (min_le_left _ _) (hr i) hc hslope
        (hgain x y (r i) c (hxx.trans_le (min_le_left _ _)) hyY.1 (hyp y hyY) (hr i) hc)
        he hLip'
      have heq : E-Complex.cos (q i)=W₁+e := by dsimp [E,W₁,q,graphDispersion]; ring
      simpa only [continuedAngleRoot,continuedAnglePoint,heq,β,L,neg_mul,q] using hi
    exact continuedSiteDensity_gaussian_bound (A := A) (B := B) hN E q r c
      (β*(1+(A : ℝ))) L M δ hL.le hM.le hδ hDom' hy0' hy' hz' hgap' hexp

end
end IsoProof
