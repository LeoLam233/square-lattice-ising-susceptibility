import IsoProof.TailBaire
import IsoProof.TailNumerics
import IsoProof.SiteAnalytic

/-! Finite-jet specialization of the Baire uniformization.  The local site
estimate is an explicit intermediate premise here, supplied by the actual
common-graph/Cauchy producer in the final tail construction. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology BigOperators
set_option maxHeartbeats 800000

theorem finite_positive_common_bounds {ι : Type*} [Fintype ι]
    (C R : ι → ℝ) (hC : ∀ i, 0 < C i) (hR : ∀ i, 0 < R i) :
    ∃ M r : ℝ, 0 < M ∧ 0 < r ∧ ∀ i, C i ≤ M ∧ r ≤ R i := by
  classical
  let M : ℝ := 1+∑ i, C i
  let S : ℝ := 1+∑ i, (R i)⁻¹
  have hM : 0 < M := by
    have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    dsimp [M]
    linarith
  have hS : 0 < S := by
    have hsum : 0 ≤ ∑ i, (R i)⁻¹ := Finset.sum_nonneg (fun i _ => (inv_pos.mpr (hR i)).le)
    dsimp [S]
    linarith
  refine ⟨M,S⁻¹,hM,inv_pos.mpr hS,?_⟩
  intro i
  constructor
  · have hi := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    change C i ≤ 1+∑ j, C j
    linarith
  · have hi := Finset.single_le_sum (fun j _ => (inv_pos.mpr (hR j)).le) (Finset.mem_univ i)
    have hb : (R i)⁻¹ ≤ S := by dsimp [S]; linarith
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (hR i)) hb

theorem siteOrderEnvelope_mono {C D : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D) (N : ℕ) :
    siteOrderEnvelope C N ≤ siteOrderEnvelope D N := by
  unfold siteOrderEnvelope
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg (Nat.cast_nonneg N) _)) N)
    (Nat.cast_nonneg N.factorial)

theorem siteOrderEnvelope_factor (C : ℝ) (N : ℕ) :
    siteOrderEnvelope C N = C^N*siteOrderEnvelope 1 N := by
  simp only [siteOrderEnvelope,one_mul,mul_pow]
  ring

def siteSpatialWeight (j N : ℕ) (p : ℤ × ℤ) : ℝ :=
  ((1 : ℝ)+(max p.1.natAbs p.2.natAbs : ℕ))^((j : ℝ)-(N : ℝ)/2)

theorem siteSpatialWeight_nonneg (j N : ℕ) (p : ℤ × ℤ) :
    0 ≤ siteSpatialWeight j N p := by
  unfold siteSpatialWeight
  positivity

/-- Simultaneous uniformization for every derivative below n, every positive
particle number and every lattice site, on a nondegenerate closed interval
inside any prescribed interval (l,u) in the positive energy cut. -/
theorem site_jet_uniform_interval (n : ℕ) {l u : ℝ}
    (hl : 0 < l) (hlu : l < u) (hu : u < 2)
    (hlocal : ∀ j < n, ∀ x : ℝ, 0 < x → x < 2 →
      ∃ C > 0, ∃ R > 0, ∀ y : ℝ, 0 < y → y ≤ R →
        ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ,
          ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2)
            ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤ siteOrderEnvelope C N*siteSpatialWeight j N p) :
    ∃ a b C R : ℝ, l < a ∧ a < b ∧ b < u ∧ 0 < C ∧ 0 < R ∧
      ∀ x ∈ Icc a b, ∀ j < n, ∀ y : ℝ, 0 < y → y ≤ R →
        ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ,
          ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2)
            ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤ siteOrderEnvelope C N*siteSpatialWeight j N p := by
  classical
  let I := Fin n × ({N : ℕ // 0 < N} × (ℤ × ℤ))
  let f : I → ℂ → ℂ := fun i => iteratedDeriv i.1.1
    (siteCoefficient i.2.1.1 i.2.2.1.natAbs i.2.2.2)
  let w : I → ℝ := fun i => siteOrderEnvelope 1 i.2.1.1*
    siteSpatialWeight i.1.1 i.2.1.1 i.2.2
  have hw (i : I) : 0 ≤ w i := by
    dsimp [w]
    apply mul_nonneg
    · unfold siteOrderEnvelope
      positivity
    · exact siteSpatialWeight_nonneg _ _ _
  have hc (i : I) (y : ℝ) (hy : 0 < y) :
      ContinuousOn (fun x : ℝ => ‖f i ((x : ℂ)+Complex.I*(y : ℂ))‖) (Ioo l u) := by
    intro x _hx
    have hD : (x : ℂ)+Complex.I*(y : ℂ) ∈ energyDomain := Or.inl (by simpa using hy.ne')
    have ha := (siteCoefficient_analyticAt i.2.1.1 i.2.2.1.natAbs i.2.2.2 hD).iterated_deriv i.1.1
    have hreal : Continuous (fun x : ℝ => (x : ℂ)+Complex.I*(y : ℂ)) := by fun_prop
    simpa only [f,iteratedDeriv_eq_iterate,Function.comp_def] using
      (ha.continuousAt.comp (f := fun x : ℝ => (x : ℂ)+Complex.I*(y : ℂ))
        hreal.continuousAt).norm.continuousWithinAt
  have hp (x : ℝ) (hx : x ∈ Ioo l u) :
      ∃ C > 0, ∃ R > 0, ∀ i : I, ∀ y : ℝ, 0 < y → y ≤ R →
        ‖f i ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤ C^i.2.1.1*w i := by
    choose C hC R hR hb using fun j : Fin n => hlocal j.1 j.2 x (hl.trans hx.1) (hx.2.trans hu)
    obtain ⟨M,r,hM,hr,hboth⟩ := finite_positive_common_bounds C R hC hR
    refine ⟨M,hM,r,hr,?_⟩
    intro i y hy hyr
    have h := hb i.1 y hy (hyr.trans (hboth i.1).2) i.2.1.1 i.2.1.2 i.2.2
    have hm := mul_le_mul_of_nonneg_right
      (siteOrderEnvelope_mono (hC i.1).le (hboth i.1).1 i.2.1.1)
      (siteSpatialWeight_nonneg i.1.1 i.2.1.1 i.2.2)
    exact (h.trans hm).trans_eq (by rw [siteOrderEnvelope_factor]; dsimp [w]; ring)
  obtain ⟨a,b,C,R,ha,hab,hb,hC,hR,hbound⟩ :=
    exists_uniform_vertical_bound hlu f (fun i => i.2.1.1) w hw hc hp
  refine ⟨a,b,C,R,ha,hab,hb,hC,hR,?_⟩
  intro x hx j hj y hy hyr N hN p
  have h := hbound x hx (⟨j,hj⟩,(⟨N,hN⟩,p)) y hy hyr
  simpa only [f,w,← mul_assoc,← siteOrderEnvelope_factor] using h

end
end IsoProof
