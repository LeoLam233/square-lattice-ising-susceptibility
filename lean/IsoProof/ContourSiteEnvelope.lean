import IsoProof.ContourStationary
import IsoProof.ContourEnergy
import IsoProof.ContourGaussian
import IsoProof.IntegralsDeterminant
import IsoProof.IntegralsGraphDensity

/-! Quantitative bounds for the literal coupled site density on the actual
common graph. All geometric hypotheses in the intermediate estimate are
produced below from the real cut point. -/
namespace IsoProof
noncomputable section
open Set
open scoped BigOperators
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

theorem continued_oneBody_norm_bound {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    {z : ℂ} (hz : ‖z‖ ≤ M) (hgap : δ ≤ ‖1-z*z‖) :
    ‖IsingBulk.HT22.Physical.oneBody z‖ ≤ 2*M/δ := by
  rw [IsingBulk.HT22.Physical.oneBody_eq_rational,norm_div,norm_mul]
  norm_num only [Complex.norm_ofNat]
  have hden : δ ≤ ‖1-z^2‖ := by simpa only [pow_two] using hgap
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz (by norm_num))
    (norm_nonneg _)).trans (div_le_div_of_nonneg_left (by positivity) hδ hden)

/-- The origin and all other sites have the same shifted Gaussian bound;
the loss from replacing A by 1+A is a fixed one-coordinate constant. -/
theorem shifted_gaussian_exponent {β R t : ℝ} (hβ : 0 ≤ β) (ht : |t| ≤ R)
    (A : ℕ) :
    -β*(A : ℝ)*t^2 ≤ β*R^2/2-(β/2)*(1+(A : ℝ))*t^2 := by
  have hR : 0 ≤ R := (abs_nonneg t).trans ht
  have ht2 : t^2 ≤ R^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) hR).mpr ht
  have hA : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr ht2),mul_nonneg hβ (mul_nonneg hA (sq_nonneg t))]

theorem common_graph_site_exponential_disk_bound {x d a ε D δ : ℝ}
    (_hd : 0 ≤ d) (ha : 0 ≤ a) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hphase : ∀ v, 0 < v → v ≤ ε → ∀ y ∈ Icc (0 : ℝ) ε,
      ∀ r ∈ Icc (-Real.pi) Real.pi, ∀ c ∈ Icc (-d) d,
      a*(y+v*(r-c)^2) ≤ commonPhaseGain x v y r c)
    {A B : ℕ} (hBA : B ≤ A) {c : ℝ} (hc : c ∈ Icc (-d) d)
    (hslope : deriv (cutPhase x) c=(B : ℝ)/(A : ℝ))
    {v y r : ℝ} (hv : 0 < v) (hvε : v ≤ ε) (hy : y ∈ Icc (0 : ℝ) ε)
    (hr : r ∈ Icc (-Real.pi) Real.pi) {e : ℂ}
    (he : ‖e‖ ≤ δ/(1+(A : ℝ)))
    (henergy : ‖continuedPhase (graphDispersion x (cutHalfWidth x) v y r c+e)-
      continuedPhase (graphDispersion x (cutHalfWidth x) v y r c)‖ ≤ D*‖e‖) :
    ‖(continuedTransferRoot (graphDispersion x (cutHalfWidth x) v y r c+e))^A*
      (Complex.exp (Complex.I*scalarGraph (cutHalfWidth x) v r c))^B‖ ≤
      Real.exp (D+(a*v)*(Real.pi+d)^2/2)*
        Real.exp (-(a*v/2)*(1+(A : ℝ))*(r-c)^2) := by
  have hb := common_graph_site_exponential_bound ha hphase hBA hc hslope hv hvε hy hr
  rw [site_exponential_norm,Real.exp_le_exp] at hb
  have he' := phase_shrinking_disk_bound hD hδ hδ1 he henergy
  have ht : |r-c| ≤ Real.pi+d := by
    have hr' : |r| ≤ Real.pi := abs_le.mpr hr
    have hc' : |c| ≤ d := abs_le.mpr hc
    have ht : |r-c| ≤ |r|+|c| := by simpa using abs_sub_le r 0 c
    exact ht.trans (add_le_add hr' hc')
  have hs := shifted_gaussian_exponent (mul_nonneg ha hv.le) ht A
  rw [site_exponential_norm,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Multiplication of the exact pair determinant bound, the true one-body
factors, and the actual Gaussian site factors. -/
theorem continuedSiteDensity_gaussian_bound {N A B : ℕ} (hN : 0 < N)
    (E : ℂ) (q : Fin N → ℂ) (r : Fin N → ℝ) (c β L M δ : ℝ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hδ : 0 < δ)
    (_hdom : ∀ i, E-Complex.cos (q i) ∈ contourRootDomain)
    (hy0 : ∀ i, δ ≤ ‖continuedAnglePoint (q i)‖)
    (hy : ∀ i, ‖continuedAnglePoint (q i)‖ ≤ M)
    (hz : ∀ i, ‖continuedAngleRoot E (q i)‖ ≤ M)
    (hgap : ∀ i j, δ ≤ ‖1-continuedAngleRoot E (q i)*continuedAngleRoot E (q j)‖)
    (hexp : ∀ i, ‖(continuedAngleRoot E (q i))^A*(continuedAnglePoint (q i))^B‖ ≤
      L*Real.exp (-β*(r i-c)^2)) :
    ‖continuedSiteDensity A (B : ℤ) E q‖ ≤
      (((4*(pairEntryEnvelope M δ)^2)*(L*(2*M/δ)))*(N : ℝ)^(3/4 : ℝ))^N*
        centeredGaussian N β c r := by
  have hpair := complex_pairProduct_three_quarters N hN E
    (fun i => continuedAnglePoint (q i)) (fun i => continuedAngleRoot E (q i))
    hM hδ hy0 hy (fun i => continuedTransferRoot_ne_zero (E-Complex.cos (q i))) hz
    (fun i => exponential_dispersion (q i) E) hgap
  have hbody (i : Fin N) := continued_oneBody_norm_bound hM hδ (hz i) (hgap i i)
  have hone (i : Fin N) :
      ‖(continuedAngleRoot E (q i))^A*(continuedAnglePoint (q i))^(B : ℤ)*
        IsingBulk.HT22.Physical.oneBody (continuedAngleRoot E (q i))‖ ≤
      (L*(2*M/δ))*Real.exp (-β*(r i-c)^2) := by
    rw [zpow_natCast,norm_mul]
    exact (mul_le_mul (hexp i) (hbody i) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  unfold continuedSiteDensity
  rw [norm_mul,norm_prod]
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => norm_nonneg _) (fun i _ => hone i)
  have h := mul_le_mul hpair hprod (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (by positivity)
  convert h using 1
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    centeredGaussian,mul_pow]
  ring

/-- The complete geometric-to-integrand producer. Its constants depend
only on the fixed cut point, center interval and graph height; they are
independent of particle number, site radius and angular coordinates. -/
theorem common_graph_density_gaussian {x d : ℝ} (hx : 0 < x) (hx2 : x < 2)
    (hd : 0 ≤ d) (hdb : d < cutHalfWidth x) :
    ∃ ε > 0, ∀ v, 0 < v → v < ε →
      ∃ R > 0, ∃ Y > 0, ∃ C > 0, ∃ β > 0,
      (∀ y ∈ Icc (0 : ℝ) Y, ∀ c ∈ Icc (-d) d,
        ∀ e : ℂ, ‖e‖ ≤ R → ∀ r ∈ Icc (-Real.pi) Real.pi,
          (x : ℂ)+Complex.I*(y : ℂ)+e-
            Complex.cos (scalarGraph (cutHalfWidth x) v r c) ∈ contourRootDomain) ∧
      (∀ N : ℕ, 0 < N → ∀ A B : ℕ, B ≤ A → ∀ c ∈ Icc (-d) d,
        deriv (cutPhase x) c=(B : ℝ)/(A : ℝ) →
        ∀ y ∈ Icc (0 : ℝ) Y, ∀ e : ℂ, ‖e‖ ≤ R/(1+(A : ℝ)) →
        ∀ r : Fin N → ℝ, (∀ i, r i ∈ Icc (-Real.pi) Real.pi) →
        ‖continuedSiteDensity A (B : ℤ) ((x : ℂ)+Complex.I*(y : ℂ)+e)
          (fun i => scalarGraph (cutHalfWidth x) v (r i) c)‖ ≤
          (C*(N : ℝ)^(3/4 : ℝ))^N*
            centeredGaussian N (β*(1+(A : ℝ))) c r) := by
  obtain ⟨a,ha,εp,hεp,hphase⟩ := common_phase_gain hx hx2 hd hdb
  obtain ⟨εs,hεs,hscalar⟩ := common_graph_scalar_bounds hx hx2 hd hdb
  obtain ⟨εe,hεe,henergy⟩ := common_graph_phase_energy_lipschitz hx hx2 hd hdb
  refine ⟨min εp (min εs εe),lt_min hεp (lt_min hεs hεe),?_⟩
  intro v hv hvε
  have hvp : v ≤ εp := (hvε.trans_le (min_le_left _ _)).le
  have hvs : v < εs := hvε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hve : v < εe := hvε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨ρ,hρ,M,hM,δ,hδ,hDom,hy0,hy,hz,hgap⟩ := hscalar v hv hvs
  obtain ⟨ρe,hρe,D,hD,hLip⟩ := henergy v hv hve
  let R := min 1 (min ρ ρe)
  have hR : 0 < R := lt_min zero_lt_one (lt_min hρ hρe)
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRρ : R ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hRρe : R ≤ ρe := (min_le_right _ _).trans (min_le_right _ _)
  let Y := min 1 εp
  have hY : 0 < Y := lt_min zero_lt_one hεp
  let L := Real.exp (D+(a*v)*(Real.pi+d)^2/2)
  let C := (4*(pairEntryEnvelope M δ)^2)*(L*(2*M/δ))
  let β := a*v/2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hL : 0 < L := Real.exp_pos _
  have hentry : 0 < pairEntryEnvelope M δ :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨R,hR,Y,hY,C,hC,β,hβ,?_,?_⟩
  · intro y hyY c hc e he r hr
    have ht : (e,(y,(r,c))) ∈ Metric.closedBall (0 : ℂ) ρ ×ˢ commonGraphBox d :=
      ⟨by simpa using he.trans hRρ,⟨hyY.1,hyY.2.trans (min_le_left _ _)⟩,hr,hc⟩
    exact hDom (e,(y,(r,c))) ht
  · intro N hN A B hBA c hc hslope y hyY e he r hr
    have hy1 : y ∈ Icc (0 : ℝ) 1 := ⟨hyY.1,hyY.2.trans (min_le_left _ _)⟩
    have hyp : y ∈ Icc (0 : ℝ) εp := ⟨hyY.1,hyY.2.trans (min_le_right _ _)⟩
    have hA1 : (1 : ℝ) ≤ 1+(A : ℝ) := by linarith [show 0 ≤ (A : ℝ) from Nat.cast_nonneg A]
    have heR : ‖e‖ ≤ R := he.trans (div_le_self hR.le hA1)
    have ht (i : Fin N) : (e,(y,(r i,c))) ∈
        Metric.closedBall (0 : ℂ) ρ ×ˢ commonGraphBox d :=
      ⟨by simpa using heR.trans hRρ,hy1,hr i,hc⟩
    let E : ℂ := (x : ℂ)+Complex.I*(y : ℂ)+e
    let q : Fin N → ℂ := fun i => scalarGraph (cutHalfWidth x) v (r i) c
    have hDom' (i : Fin N) : E-Complex.cos (q i) ∈ contourRootDomain :=
      hDom (e,(y,(r i,c))) (ht i)
    have hy0' (i : Fin N) : δ ≤ ‖continuedAnglePoint (q i)‖ :=
      hy0 (e,(y,(r i,c))) (ht i)
    have hy' (i : Fin N) : ‖continuedAnglePoint (q i)‖ ≤ M :=
      hy (e,(y,(r i,c))) (ht i)
    have hz' (i : Fin N) : ‖continuedAngleRoot E (q i)‖ ≤ M :=
      hz (e,(y,(r i,c))) (ht i)
    have hgap' (i j : Fin N) :
        δ ≤ ‖1-continuedAngleRoot E (q i)*continuedAngleRoot E (q j)‖ :=
      hgap (e,(y,(r i,c))) (ht i) (e,(y,(r j,c))) (ht j)
    have hexp (i : Fin N) : ‖continuedAngleRoot E (q i)^A*continuedAnglePoint (q i)^B‖ ≤
        L*Real.exp (-(β*(1+(A : ℝ)))*(r i-c)^2) := by
      have hi := common_graph_site_exponential_disk_bound hd ha.le hD.le hR.le hR1
        hphase hBA hc hslope hv hvp hyp (hr i) he
        (hLip y hy1 (r i) (hr i) c hc e (heR.trans hRρe))
      have hW : E-Complex.cos (q i) =
          graphDispersion x (cutHalfWidth x) v y (r i) c+e := by
        dsimp [E,q,graphDispersion]
        ring
      simpa only [continuedAngleRoot,continuedAnglePoint,hW,β,L,neg_mul,q] using hi
    exact continuedSiteDensity_gaussian_bound (A := A) (B := B) hN E q r c
      (β*(1+(A : ℝ))) L M δ hL.le hM.le hδ hDom' hy0' hy' hz' hgap' hexp

end
end IsoProof
