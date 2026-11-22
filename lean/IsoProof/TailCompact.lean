import IsoProof.ContourUniformEstimate
import IsoProof.TailSigned

/-! Compact-subinterval uniformity in (6), obtained by an actual finite
cover of the real-energy local estimates. This strengthens the earlier
Baire extraction to every prescribed compact subset of the positive cut. -/
namespace IsoProof
noncomputable section
open Set Filter Metric
open scoped Topology
set_option maxHeartbeats 800000

theorem siteCoefficient_compact_jet_bound {K : Set ℝ} (hK : IsCompact K)
    (hcut : K ⊆ Ioo (0 : ℝ) 2) (j : ℕ) :
    ∃ C > 0, ∃ Y > 0, ∀ x∈K, ∀ y : ℝ, 0 < y → y ≤ Y →
      ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ,
        ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤
          siteOrderEnvelope C N*siteSpatialWeight j N p := by
  classical
  choose ρ hρ C hC Y hY hbound using fun x : K =>
    siteCoefficient_lattice_jet_bound_locally_uniform (hcut x.property).1 (hcut x.property).2 j
  obtain ⟨s,hcover⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℝ) (ρ x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hρ ⟨x,hx⟩)⟩)
  obtain ⟨M,R,hM,hR,hboth⟩ := finite_positive_common_bounds
    (fun i : s => C i.1) (fun i : s => Y i.1) (fun i => hC i.1) (fun i => hY i.1)
  refine ⟨M,hM,R,hR,?_⟩
  intro x hx y hy hyR N hN p
  obtain ⟨i,hi,hball⟩ := mem_iUnion₂.mp (hcover hx)
  have hb := hbound i x (by simpa only [mem_ball,Real.dist_eq] using hball)
    y hy (hyR.trans (hboth ⟨i,hi⟩).2) N hN p
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (siteOrderEnvelope_mono (hC i).le (hboth ⟨i,hi⟩).1 N) (siteSpatialWeight_nonneg j N p)

/-- All derivatives through k have the same genuine compact-interval
constants, simultaneously over particle number and the full lattice. -/
theorem siteCoefficient_compact_jets_bound {K : Set ℝ} (hK : IsCompact K)
    (hcut : K ⊆ Ioo (0 : ℝ) 2) (k : ℕ) :
    ∃ C > 0, ∃ Y > 0, ∀ x∈K, ∀ j ≤ k, ∀ y : ℝ, 0 < y → y ≤ Y →
      ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ,
        ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) ((x : ℂ)+Complex.I*(y : ℂ))‖ ≤
          siteOrderEnvelope C N*siteSpatialWeight j N p := by
  classical
  choose C hC Y hY hbound using fun j : Fin (k+1) => siteCoefficient_compact_jet_bound hK hcut j.1
  obtain ⟨M,R,hM,hR,hboth⟩ := finite_positive_common_bounds C Y hC hY
  refine ⟨M,hM,R,hR,?_⟩
  intro x hx j hj y hy hyR N hN p
  let i : Fin (k+1) := ⟨j,by omega⟩
  have hb := hbound i x hx y hy (hyR.trans (hboth i).2) N hN p
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (siteOrderEnvelope_mono (hC i).le (hboth i).1 N) (siteSpatialWeight_nonneg j N p)

theorem compact_interval_site_jet_bound {a b : ℝ} (ha : 0 < a) (hb : b < 2) (k : ℕ) :
    ∃ C > 0, ∃ R > 0, ∀ j ≤ k, ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ,
      ∀ E∈upperCollar a b R,
        ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) E‖ ≤
          siteOrderEnvelope C N*siteSpatialWeight j N p := by
  obtain ⟨C,hC,R,hR,hbound⟩ := siteCoefficient_compact_jets_bound
    (K := Icc a b) isCompact_Icc (fun x hx => ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩) k
  refine ⟨C,hC,R,hR,?_⟩
  intro j hj N hN p E hE
  have h := hbound E.re ⟨hE.1.1.1.le,hE.1.1.2.le⟩ j hj E.im hE.2 hE.1.2.2.le N hN p
  simpa only [mul_comm Complex.I,Complex.re_add_im] using h

/-- The manuscript's full strength: both signs and both parities on every
prescribed interval strictly inside (0,2), with all jets through k. -/
theorem signed_energyTail_continuous_jets_on_interval (ν : Phase) (σ : Sign) (k : ℕ)
    {a b : ℝ} (ha : 0 < a) (hb : b < 2) :
    ∃ R > 0,
      (∀ j ≤ k, ContinuousOn (signedTailUpperJet ν σ k j) (closedUpperCollar a b R)) ∧
      (∀ E∈upperCollar a b R, ∀ j ≤ k,
        signedTailUpperJet ν σ k j E = iteratedDeriv j (energyTail ν σ (2*k+4)) E) := by
  obtain ⟨C,hC,R,hR,hbound⟩ := compact_interval_site_jet_bound ha hb k
  refine ⟨R,hR,?_,?_⟩
  · intro j hj
    exact signedTailUpperJet_continuousOn ha hb hC.le ν σ k j hj (hbound j hj)
  · intro E hE j _hj
    exact signedTailUpperJet_agrees hC.le ν σ k j (hbound 0 (Nat.zero_le _)) hE

theorem energyTail_continuous_jets_on_interval (ν : Phase) (k : ℕ)
    {a b : ℝ} (ha : 0 < a) (hb : b < 2) :
    ∃ R > 0,
      (∀ j ≤ k, ContinuousOn (tailUpperJet ν k j) (closedUpperCollar a b R)) ∧
      (∀ E∈upperCollar a b R, ∀ j ≤ k,
        tailUpperJet ν k j E = iteratedDeriv j (energyTail ν .positive (2*k+4)) E) := by
  obtain ⟨C,hC,R,hR,hbound⟩ := compact_interval_site_jet_bound ha hb k
  refine ⟨R,hR,?_,?_⟩
  · intro j hj
    exact tailUpperJet_continuousOn ha hb hC.le ν k j hj (hbound j hj)
  · intro E hE j _hj
    exact tailUpperJet_agrees hC.le ν k j (hbound 0 (Nat.zero_le _)) hE

/-- Exact closed real endpoints are included after choosing a slightly
larger interval. This states compact-subinterval continuity literally. -/
theorem signed_energyTail_continuous_jets_on_compact_interval (ν : Phase) (σ : Sign) (k : ℕ)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hb : b < 2) :
    ∃ R > 0,
      (∀ j ≤ k, ContinuousOn (signedTailUpperJet ν σ k j)
        {E : ℂ | E.re∈Icc a b ∧ E.im∈Icc 0 R}) ∧
      (∀ E : ℂ, E.re∈Icc a b → 0 < E.im → E.im ≤ R → ∀ j ≤ k,
        signedTailUpperJet ν σ k j E = iteratedDeriv j (energyTail ν σ (2*k+4)) E) := by
  obtain ⟨R,hR,hcont,heq⟩ := signed_energyTail_continuous_jets_on_interval ν σ k
    (a := a/2) (b := (b+2)/2) (half_pos ha) (by linarith)
  have hclosed {E : ℂ} (hE : E.re∈Icc a b ∧ E.im∈Icc (0 : ℝ) (R/2)) :
      E∈closedUpperCollar (a/2) ((b+2)/2) R := by
    exact ⟨⟨⟨by linarith [hE.1.1],by linarith [hE.1.2]⟩,
      ⟨by linarith [hE.2.1],by linarith [hE.2.2]⟩⟩,hE.2.1⟩
  refine ⟨R/2,half_pos hR,?_,?_⟩
  · intro j hj
    exact (hcont j hj).mono (fun _ hE => hclosed hE)
  · intro E hreal him himR j hj
    exact heq E ⟨(hclosed ⟨hreal,him.le,himR⟩).1,him⟩ j hj

/-- Compatibility wrapper for the terminal assembly, now proved using the
strong compact estimate rather than Baire extraction. -/
theorem energyTail_continuous_jet_interval_uniform (ν : Phase) (k : ℕ) {l u : ℝ}
    (hl : 0 < l) (hlu : l < u) (hu : u < 2) :
    ∃ a b R : ℝ, l < a ∧ a < b ∧ b < u ∧ 0 < R ∧
      (∀ j ≤ k, ContinuousOn (tailUpperJet ν k j) (closedUpperCollar a b R)) ∧
      (∀ E∈upperCollar a b R, ∀ j ≤ k,
        tailUpperJet ν k j E = iteratedDeriv j (energyTail ν .positive (2*k+4)) E) := by
  let a := (2*l+u)/3
  let b := (l+2*u)/3
  have hla : l < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hbu : b < u := by dsimp [b]; linarith
  obtain ⟨R,hR,hcont,heq⟩ := energyTail_continuous_jets_on_interval ν k
    (hl.trans hla) (hbu.trans hu)
  exact ⟨a,b,R,hla,hab,hbu,hR,hcont,heq⟩

end
end IsoProof
