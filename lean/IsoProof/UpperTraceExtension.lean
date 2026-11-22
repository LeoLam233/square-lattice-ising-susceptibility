import IsoProof.IntegralsSiteBoundary
import IsoProof.JetTrace
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.Complex.ReImTopology

/-! Canonical continuous upper traces.  The extension is the actual limit
of the actual derivative from the entire upper half-plane.  Its continuity
uses existence of the full one-sided limit at every boundary point, not
merely a limit along selected prime rays. -/
namespace IsoProof
noncomputable section
open Set Filter
open scoped Topology

def upperJetExtension (f : ℂ → ℂ) (j : ℕ) : ℂ → ℂ :=
  extendFrom {z : ℂ | 0 < z.im} (iteratedDeriv j f)

theorem upperJetExtension_eq {f : ℂ → ℂ} (j : ℕ)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im}) {z : ℂ} (hz : 0 < z.im) :
    upperJetExtension f j z = iteratedDeriv j f z := by
  apply extendFrom_extends _ z hz
  intro w hw
  exact (IsingBulk.First.analyticAt_iteratedDeriv (hf w hw) j).continuousAt.continuousWithinAt

theorem upper_jet_limit_exists {f : ℂ → ℂ} (j : ℕ) {a b R : ℝ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im})
    (hboundary : ∀ x ∈ Ioo a b, ∃ L, UpperJetTrace f j x L)
    {z : ℂ} (hz : z ∈ closedUpperCollar a b R) :
    ∃ L, Tendsto (iteratedDeriv j f) (𝓝[{z : ℂ | 0 < z.im}] z) (𝓝 L) := by
  by_cases hi : 0 < z.im
  · exact ⟨_,(IsingBulk.First.analyticAt_iteratedDeriv (hf z hi) j).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds⟩
  · have him : z.im=0 := le_antisymm (le_of_not_gt hi) hz.2
    have he : (z.re : ℂ)=z := Complex.ext rfl (by simpa only [Complex.ofReal_im] using him.symm)
    obtain ⟨L,hL⟩ := hboundary z.re hz.1.1
    refine ⟨L,?_⟩
    simpa only [UpperJetTrace,complexJet,he] using hL

theorem upperJetExtension_continuousOn {f : ℂ → ℂ} (j : ℕ) {a b R : ℝ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im})
    (hboundary : ∀ x ∈ Ioo a b, ∃ L, UpperJetTrace f j x L) :
    ContinuousOn (upperJetExtension f j) (closedUpperCollar a b R) := by
  apply continuousOn_extendFrom
  · intro z hz
    rw [Complex.closure_setOfPred_lt_im]
    exact hz.2
  · intro z hz
    exact upper_jet_limit_exists j hf hboundary hz

theorem upperJetExtension_bound {f : ℂ → ℂ} (j : ℕ) {a b R M : ℝ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im})
    (hboundary : ∀ x ∈ Ioo a b, ∃ L, UpperJetTrace f j x L)
    (hbound : ∀ z ∈ upperCollar a b R, ‖iteratedDeriv j f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedUpperCollar a b R) :
    ‖upperJetExtension f j z‖ ≤ M := by
  have hclosure : z ∈ closure {w : ℂ | 0 < w.im} := by
    rw [Complex.closure_setOfPred_lt_im]
    exact hz.2
  have : NeBot (𝓝[{w : ℂ | 0 < w.im}] z) := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hlim := tendsto_extendFrom (upper_jet_limit_exists j hf hboundary hz)
  apply le_of_tendsto hlim.norm
  have hreal : realCollar a b R ∈ 𝓝 z := (show IsOpen (realCollar a b R) from isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hz.1
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hreal] with w hw hr
  exact hbound w ⟨hr,hw⟩

/-- Every literal site's canonical upper jet is continuous on every closed
upper collar strictly inside (0,2). No boundary trace is an external input. -/
theorem site_upperJetExtension_continuousOn (N A : ℕ) (B : ℤ) (j : ℕ)
    {a b R : ℝ} (ha : 0 < a) (hb : b < 2) :
    ContinuousOn (upperJetExtension (siteCoefficient N A B) j) (closedUpperCollar a b R) :=
  upperJetExtension_continuousOn j
    (fun _ h => siteCoefficient_analyticAt N A B (Or.inl h.ne'))
    (fun _x hx => site_upperJetTrace_exists (ha.trans hx.1) (hx.2.trans hb) N A B j)

theorem site_upperJetExtension_bound (N A : ℕ) (B : ℤ) (j : ℕ)
    {a b R M : ℝ} (ha : 0 < a) (hb : b < 2)
    (hbound : ∀ z ∈ upperCollar a b R, ‖iteratedDeriv j (siteCoefficient N A B) z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedUpperCollar a b R) :
    ‖upperJetExtension (siteCoefficient N A B) j z‖ ≤ M :=
  upperJetExtension_bound j
    (fun _ h => siteCoefficient_analyticAt N A B (Or.inl h.ne'))
    (fun _x hx => site_upperJetTrace_exists (ha.trans hx.1) (hx.2.trans hb) N A B j)
    hbound hz

end
end IsoProof
