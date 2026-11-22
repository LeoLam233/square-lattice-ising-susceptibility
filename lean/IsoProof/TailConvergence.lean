import IsoProof.ContourSiteEstimate
import IsoProof.TailSpatial
import IsoProof.UpperTraceExtension
import IsoProof.NormalJetSummation
import IsoProof.PhysicalIdentification
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! The complete positive-sign, both-parity high-particle tail. The uniform
majorant is summable over particle number times the full signed lattice.
The continuous boundary sum is then identified with every actual energy
derivative of the literal tail on the open upper collar. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology BigOperators
set_option maxHeartbeats 800000

theorem particleOrder_injective (ν : Phase) : Function.Injective (particleOrder ν) := by
  intro n m h
  cases ν <;> dsimp [particleOrder] at h <;> omega

def phaseTailMajorant (C : ℝ) (ν : Phase) (i : ℕ × (ℤ × ℤ)) : ℝ :=
  siteOrderEnvelope C (particleOrder ν i.1)*spatialTailMajorant i.2

theorem phaseTailMajorant_nonneg {C : ℝ} (hC : 0 ≤ C) (ν : Phase) (i : ℕ × (ℤ × ℤ)) :
    0 ≤ phaseTailMajorant C ν i := by
  exact mul_nonneg (by unfold siteOrderEnvelope; positivity) (spatialTailMajorant_nonneg i.2)

theorem phaseTailMajorant_summable {C : ℝ} (hC : 0 ≤ C) (ν : Phase) :
    Summable (phaseTailMajorant C ν) := by
  exact ((siteOrderEnvelope_summable hC).comp_injective (particleOrder_injective ν)).mul_of_nonneg
    spatialTailMajorant_summable (fun n => by
      change 0 ≤ siteOrderEnvelope C (particleOrder ν n)
      unfold siteOrderEnvelope
      positivity)
    spatialTailMajorant_nonneg

def tailSiteTerm (ν : Phase) (k : ℕ) (i : ℕ × (ℤ × ℤ)) (E : ℂ) : ℂ :=
  if 2*k+4 < particleOrder ν i.1 then
    siteCoefficient (particleOrder ν i.1) i.2.1.natAbs i.2.2 E else 0

def tailUpperJetTerm (ν : Phase) (k j : ℕ) (i : ℕ × (ℤ × ℤ)) (E : ℂ) : ℂ :=
  if 2*k+4 < particleOrder ν i.1 then
    upperJetExtension (siteCoefficient (particleOrder ν i.1) i.2.1.natAbs i.2.2) j E else 0

def tailUpperJet (ν : Phase) (k j : ℕ) (E : ℂ) : ℂ :=
  ∑' i : ℕ × (ℤ × ℤ), tailUpperJetTerm ν k j i E

theorem tailSiteTerm_analyticOn (ν : Phase) (k : ℕ) (i : ℕ × (ℤ × ℤ))
    (a b R : ℝ) : AnalyticOnNhd ℂ (tailSiteTerm ν k i) (upperCollar a b R) := by
  intro E hE
  by_cases ht : 2*k+4 < particleOrder ν i.1
  · have he : tailSiteTerm ν k i = siteCoefficient (particleOrder ν i.1) i.2.1.natAbs i.2.2 := by
      funext z
      simp only [tailSiteTerm,ht,↓reduceIte]
    rw [he]
    exact siteCoefficient_analyticAt _ _ _ (Or.inl hE.2.ne')
  · have he : tailSiteTerm ν k i = fun _ => (0 : ℂ) := by
      funext z
      simp only [tailSiteTerm,ht,↓reduceIte]
    rw [he]
    exact analyticAt_const

theorem tailSiteTerm_jet (ν : Phase) (k j : ℕ) (i : ℕ × (ℤ × ℤ)) (E : ℂ) :
    iteratedDeriv j (tailSiteTerm ν k i) E =
      if 2*k+4 < particleOrder ν i.1 then
        iteratedDeriv j (siteCoefficient (particleOrder ν i.1) i.2.1.natAbs i.2.2) E else 0 := by
  by_cases ht : 2*k+4 < particleOrder ν i.1
  · have he : tailSiteTerm ν k i = siteCoefficient (particleOrder ν i.1) i.2.1.natAbs i.2.2 := by
      funext z
      simp only [tailSiteTerm,ht,↓reduceIte]
    simp only [he,ht,↓reduceIte]
  · have he : tailSiteTerm ν k i = fun _ => (0 : ℂ) := by
      funext z
      simp only [tailSiteTerm,ht,↓reduceIte]
    simp [he,ht]

theorem tailUpperJetTerm_eq_jet (ν : Phase) (k j : ℕ) (i : ℕ × (ℤ × ℤ))
    {E : ℂ} (hE : 0 < E.im) :
    tailUpperJetTerm ν k j i E = iteratedDeriv j (tailSiteTerm ν k i) E := by
  rw [tailSiteTerm_jet]
  by_cases ht : 2*k+4 < particleOrder ν i.1
  · simp only [tailUpperJetTerm,ht,↓reduceIte]
    exact upperJetExtension_eq j
      (fun _ h => siteCoefficient_analyticAt _ _ _ (Or.inl h.ne')) hE
  · simp only [tailUpperJetTerm,ht,↓reduceIte]

theorem tailSiteTerm_jet_bound {a b R C : ℝ} (hC : 0 ≤ C) (ν : Phase) (k j : ℕ)
    (hj : j ≤ k)
    (hbound : ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ, ∀ E ∈ upperCollar a b R,
      ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) E‖ ≤
        siteOrderEnvelope C N*siteSpatialWeight j N p)
    (i : ℕ × (ℤ × ℤ)) {E : ℂ} (hE : E ∈ upperCollar a b R) :
    ‖iteratedDeriv j (tailSiteTerm ν k i) E‖ ≤ phaseTailMajorant C ν i := by
  rw [tailSiteTerm_jet]
  by_cases ht : 2*k+4 < particleOrder ν i.1
  · simp only [ht,↓reduceIte]
    apply (hbound _ (particleOrder_positive ν i.1) i.2 E hE).trans
    exact mul_le_mul_of_nonneg_left (site_tail_spatial_bound hj ht i.2)
      (by unfold siteOrderEnvelope; positivity)
  · simpa only [ht,↓reduceIte,norm_zero] using phaseTailMajorant_nonneg hC ν i

theorem tailUpperJetTerm_bound {a b R C : ℝ} (ha : 0 < a) (hb : b < 2) (hC : 0 ≤ C)
    (ν : Phase) (k j : ℕ) (hj : j ≤ k)
    (hbound : ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ, ∀ E ∈ upperCollar a b R,
      ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) E‖ ≤
        siteOrderEnvelope C N*siteSpatialWeight j N p)
    (i : ℕ × (ℤ × ℤ)) {E : ℂ} (hE : E ∈ closedUpperCollar a b R) :
    ‖tailUpperJetTerm ν k j i E‖ ≤ phaseTailMajorant C ν i := by
  by_cases ht : 2*k+4 < particleOrder ν i.1
  · simp only [tailUpperJetTerm,ht,↓reduceIte]
    apply site_upperJetExtension_bound _ _ _ j ha hb _ hE
    intro z hz
    have h := tailSiteTerm_jet_bound hC ν k j hj hbound i hz
    simpa only [tailSiteTerm_jet,ht,↓reduceIte] using h
  · simpa only [tailUpperJetTerm,ht,↓reduceIte,norm_zero] using phaseTailMajorant_nonneg hC ν i

theorem tailUpperJet_continuousOn {a b R C : ℝ} (ha : 0 < a) (hb : b < 2) (hC : 0 ≤ C)
    (ν : Phase) (k j : ℕ) (hj : j ≤ k)
    (hbound : ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ, ∀ E ∈ upperCollar a b R,
      ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) E‖ ≤
        siteOrderEnvelope C N*siteSpatialWeight j N p) :
    ContinuousOn (tailUpperJet ν k j) (closedUpperCollar a b R) := by
  apply continuousOn_tsum _ (phaseTailMajorant_summable hC ν)
    (fun i E hE => tailUpperJetTerm_bound ha hb hC ν k j hj hbound i hE)
  intro i
  by_cases ht : 2*k+4 < particleOrder ν i.1
  · simpa only [tailUpperJetTerm,ht,↓reduceIte] using
      site_upperJetExtension_continuousOn (particleOrder ν i.1) i.2.1.natAbs i.2.2 j ha hb
  · simpa only [tailUpperJetTerm,ht,↓reduceIte] using
      (continuousOn_const (s := closedUpperCollar a b R) (c := (0 : ℂ)))

theorem tailSiteTerm_tsum_eq_energyTail {a b R C : ℝ} (hC : 0 ≤ C)
    (ν : Phase) (k : ℕ)
    (hbound : ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ, ∀ E ∈ upperCollar a b R,
      ‖siteCoefficient N p.1.natAbs p.2 E‖ ≤ siteOrderEnvelope C N*siteSpatialWeight 0 N p)
    {E : ℂ} (hE : E ∈ upperCollar a b R) :
    (∑' i : ℕ × (ℤ × ℤ), tailSiteTerm ν k i E) = energyTail ν .positive (2*k+4) E := by
  have hs : Summable (fun i : ℕ × (ℤ × ℤ) => tailSiteTerm ν k i E) :=
    (phaseTailMajorant_summable hC ν).of_norm_bounded
      (fun i => tailSiteTerm_jet_bound hC ν k 0 (Nat.zero_le _) hbound i hE)
  rw [hs.tsum_prod]
  unfold energyTail
  apply tsum_congr
  intro n
  by_cases ht : 2*k+4 < particleOrder ν n
  · simp only [tailSiteTerm,ht,↓reduceIte]
    exact (particleCoefficient_eq_site_tsum_complex _ (particleOrder_positive ν n)
      (Or.inl hE.2.ne')).symm
  · simp only [tailSiteTerm,ht,↓reduceIte,tsum_zero]

/-- The continuous boundary series agrees with the actual derivative of
the original particle tail. Cauchy normal convergence justifies every
interchange of a derivative and either infinite sum. -/
theorem tailUpperJet_agrees {a b R C : ℝ} (hC : 0 ≤ C) (ν : Phase) (k j : ℕ)
    (hbound0 : ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ, ∀ E ∈ upperCollar a b R,
      ‖siteCoefficient N p.1.natAbs p.2 E‖ ≤ siteOrderEnvelope C N*siteSpatialWeight 0 N p)
    {E : ℂ} (hE : E ∈ upperCollar a b R) :
    tailUpperJet ν k j E = iteratedDeriv j (energyTail ν .positive (2*k+4)) E := by
  have hnormal : LocalSummableBound (tailSiteTerm ν k) (upperCollar a b R) :=
    localSummableBound_of_uniform (upperCollar_isOpen _ _ _) (phaseTailMajorant_summable hC ν)
      (fun i z hz => tailSiteTerm_jet_bound hC ν k 0 (Nat.zero_le _) hbound0 i hz)
  have heq : (fun z => ∑' i, tailSiteTerm ν k i z) =ᶠ[𝓝 E]
      energyTail ν .positive (2*k+4) := by
    filter_upwards [(upperCollar_isOpen a b R).mem_nhds hE] with z hz
    exact tailSiteTerm_tsum_eq_energyTail hC ν k hbound0 hz
  rw [← heq.iteratedDeriv_eq j,
    iteratedDeriv_tsum_of_local_bound (upperCollar_isOpen _ _ _)
      (fun i => tailSiteTerm_analyticOn ν k i a b R) hnormal j hE]
  apply tsum_congr
  intro i
  exact tailUpperJetTerm_eq_jet ν k j i hE.2

/-- The actual full high-particle tail has all upper jets through order k
continuous on a nondegenerate collar inside any prescribed positive-cut
interval. The only premise is the requested location of that interval. -/
theorem energyTail_continuous_jet_interval (ν : Phase) (k : ℕ) {l u : ℝ}
    (hl : 0 < l) (hlu : l < u) (hu : u < 2) :
    ∃ a b R : ℝ, l < a ∧ a < b ∧ b < u ∧ 0 < R ∧
      (∀ j ≤ k, ContinuousOn (tailUpperJet ν k j) (closedUpperCollar a b R)) ∧
      (∀ E ∈ upperCollar a b R, ∀ j ≤ k,
        tailUpperJet ν k j E = iteratedDeriv j (energyTail ν .positive (2*k+4)) E) := by
  obtain ⟨a,b,C,R,hla,hab,hbu,hC,hR,hbound⟩ :=
    siteCoefficient_uniform_jet_interval (k+1) hl hlu hu
  have ha : 0 < a := hl.trans hla
  have hb : b < 2 := hbu.trans hu
  have hbd (j : ℕ) (hj : j ≤ k) (N : ℕ) (hN : 0 < N) (p : ℤ × ℤ)
      (E : ℂ) (hE : E ∈ upperCollar a b R) :
      ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) E‖ ≤
        siteOrderEnvelope C N*siteSpatialWeight j N p := by
    have h := hbound E.re ⟨hE.1.1.1.le,hE.1.1.2.le⟩ j (by omega) E.im hE.2 hE.1.2.2.le N hN p
    simpa only [mul_comm Complex.I,Complex.re_add_im] using h
  refine ⟨a,b,R,hla,hab,hbu,hR,?_,?_⟩
  · intro j hj
    exact tailUpperJet_continuousOn ha hb hC.le ν k j hj (hbd j hj)
  · intro E hE j _hj
    exact tailUpperJet_agrees hC.le ν k j (hbd 0 (Nat.zero_le _)) hE

end
end IsoProof
