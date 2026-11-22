import IsoProof.TailConvergence
import IsoProof.IntegralsSignedLattice

/-! Both signs of equation (3). The character is retained inside every
lattice sum and derivative; its proved unit norm makes the same majorant
valid for the reflected odd sector. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology BigOperators
set_option maxHeartbeats 800000

def signedTailSiteTerm (ν : Phase) (σ : Sign) (k : ℕ)
    (i : ℕ × (ℤ × ℤ)) (E : ℂ) : ℂ := latticeSign σ i.2*tailSiteTerm ν k i E

def signedTailUpperJet (ν : Phase) (σ : Sign) (k j : ℕ) (E : ℂ) : ℂ :=
  ∑' i : ℕ × (ℤ × ℤ), latticeSign σ i.2*tailUpperJetTerm ν k j i E

theorem signedTailSiteTerm_jet (ν : Phase) (σ : Sign) (k j : ℕ)
    (i : ℕ × (ℤ × ℤ)) (E : ℂ) :
    iteratedDeriv j (signedTailSiteTerm ν σ k i) E =
      latticeSign σ i.2*iteratedDeriv j (tailSiteTerm ν k i) E := by
  exact iteratedDeriv_const_mul_field (latticeSign σ i.2) (tailSiteTerm ν k i)

theorem signedTailSiteTerm_jet_norm (ν : Phase) (σ : Sign) (k j : ℕ)
    (i : ℕ × (ℤ × ℤ)) (E : ℂ) :
    ‖iteratedDeriv j (signedTailSiteTerm ν σ k i) E‖ =
      ‖iteratedDeriv j (tailSiteTerm ν k i) E‖ := by
  rw [signedTailSiteTerm_jet,norm_mul,latticeSign_norm,one_mul]

theorem signedTailUpperJet_continuousOn {a b R C : ℝ}
    (ha : 0 < a) (hb : b < 2) (hC : 0 ≤ C) (ν : Phase) (σ : Sign) (k j : ℕ)
    (hj : j ≤ k)
    (hbound : ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ, ∀ E ∈ upperCollar a b R,
      ‖iteratedDeriv j (siteCoefficient N p.1.natAbs p.2) E‖ ≤
        siteOrderEnvelope C N*siteSpatialWeight j N p) :
    ContinuousOn (signedTailUpperJet ν σ k j) (closedUpperCollar a b R) := by
  refine continuousOn_tsum ?_ (phaseTailMajorant_summable hC ν) ?_
  · intro i
    apply continuousOn_const.mul
    change ContinuousOn (fun E => tailUpperJetTerm ν k j i E) (closedUpperCollar a b R)
    by_cases ht : 2*k+4 < particleOrder ν i.1
    · simpa only [tailUpperJetTerm,ht,↓reduceIte] using
        site_upperJetExtension_continuousOn (particleOrder ν i.1) i.2.1.natAbs i.2.2 j ha hb
    · simpa only [tailUpperJetTerm,ht,↓reduceIte] using
        (continuousOn_const (s := closedUpperCollar a b R) (c := (0 : ℂ)))
  · intro i E hE
    rw [norm_mul,latticeSign_norm,one_mul]
    exact tailUpperJetTerm_bound ha hb hC ν k j hj hbound i hE

theorem signedTailSiteTerm_tsum_eq_energyTail {a b R C : ℝ} (hC : 0 ≤ C)
    (ν : Phase) (σ : Sign) (k : ℕ)
    (hbound : ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ, ∀ E ∈ upperCollar a b R,
      ‖siteCoefficient N p.1.natAbs p.2 E‖ ≤ siteOrderEnvelope C N*siteSpatialWeight 0 N p)
    {E : ℂ} (hE : E ∈ upperCollar a b R) :
    (∑' i : ℕ × (ℤ × ℤ), signedTailSiteTerm ν σ k i E) = energyTail ν σ (2*k+4) E := by
  have hs : Summable (fun i : ℕ × (ℤ × ℤ) => signedTailSiteTerm ν σ k i E) := by
    apply (phaseTailMajorant_summable hC ν).of_norm_bounded
    intro i
    rw [show signedTailSiteTerm ν σ k i E = iteratedDeriv 0 (signedTailSiteTerm ν σ k i) E from rfl,
      signedTailSiteTerm_jet_norm]
    exact tailSiteTerm_jet_bound hC ν k 0 (Nat.zero_le _) hbound i hE
  rw [hs.tsum_prod]
  unfold energyTail
  apply tsum_congr
  intro n
  by_cases ht : 2*k+4 < particleOrder ν n
  · simp only [signedTailSiteTerm,tailSiteTerm,ht,↓reduceIte]
    exact (particleCoefficient_eq_signed_site_tsum_complex σ _ (particleOrder_positive ν n)
      (Or.inl hE.2.ne')).symm
  · simp only [signedTailSiteTerm,tailSiteTerm,ht,↓reduceIte,mul_zero,tsum_zero]

theorem signedTailUpperJet_agrees {a b R C : ℝ} (hC : 0 ≤ C)
    (ν : Phase) (σ : Sign) (k j : ℕ)
    (hbound0 : ∀ N : ℕ, 0 < N → ∀ p : ℤ × ℤ, ∀ E ∈ upperCollar a b R,
      ‖siteCoefficient N p.1.natAbs p.2 E‖ ≤ siteOrderEnvelope C N*siteSpatialWeight 0 N p)
    {E : ℂ} (hE : E ∈ upperCollar a b R) :
    signedTailUpperJet ν σ k j E = iteratedDeriv j (energyTail ν σ (2*k+4)) E := by
  have hnormal : LocalSummableBound (signedTailSiteTerm ν σ k) (upperCollar a b R) := by
    apply localSummableBound_of_uniform (upperCollar_isOpen _ _ _) (phaseTailMajorant_summable hC ν)
    intro i z hz
    rw [show signedTailSiteTerm ν σ k i z = iteratedDeriv 0 (signedTailSiteTerm ν σ k i) z from rfl,
      signedTailSiteTerm_jet_norm]
    exact tailSiteTerm_jet_bound hC ν k 0 (Nat.zero_le _) hbound0 i hz
  have ha (i : ℕ × (ℤ × ℤ)) :
      AnalyticOnNhd ℂ (signedTailSiteTerm ν σ k i) (upperCollar a b R) := by
    intro z hz
    exact analyticAt_const.mul (tailSiteTerm_analyticOn ν k i a b R z hz)
  have heq : (fun z => ∑' i, signedTailSiteTerm ν σ k i z) =ᶠ[𝓝 E]
      energyTail ν σ (2*k+4) := by
    filter_upwards [(upperCollar_isOpen a b R).mem_nhds hE] with z hz
    exact signedTailSiteTerm_tsum_eq_energyTail hC ν σ k hbound0 hz
  rw [← heq.iteratedDeriv_eq j,
    iteratedDeriv_tsum_of_local_bound (upperCollar_isOpen _ _ _) ha hnormal j hE]
  apply tsum_congr
  intro i
  rw [signedTailSiteTerm_jet,tailUpperJetTerm_eq_jet ν k j i hE.2]

/-- Both parities and both signs, including the reflected odd-particle
sector. Each infinite derivative sum is the actual literal particle tail. -/
theorem signed_energyTail_continuous_jet_interval (ν : Phase) (σ : Sign) (k : ℕ)
    {l u : ℝ} (hl : 0 < l) (hlu : l < u) (hu : u < 2) :
    ∃ a b R : ℝ, l < a ∧ a < b ∧ b < u ∧ 0 < R ∧
      (∀ j ≤ k, ContinuousOn (signedTailUpperJet ν σ k j) (closedUpperCollar a b R)) ∧
      (∀ E ∈ upperCollar a b R, ∀ j ≤ k,
        signedTailUpperJet ν σ k j E = iteratedDeriv j (energyTail ν σ (2*k+4)) E) := by
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
    exact signedTailUpperJet_continuousOn ha hb hC.le ν σ k j hj (hbd j hj)
  · intro E hE j _hj
    exact signedTailUpperJet_agrees hC.le ν σ k j (hbd 0 (Nat.zero_le _)) hE

end
end IsoProof
