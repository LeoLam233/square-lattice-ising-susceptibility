import IsoProof.EnergyTailSplit
import IsoProof.EnergyJetInterval
import IsoProof.TailCompact

/-! Assembly of the actual continuous high-particle tail and finitely many
actual analytic low-particle extensions.  This generic assembly exposes the finite-particle producer explicitly;
EnergyJetRegularity discharges it with the constrained common-contour theorem. -/
namespace IsoProof
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
set_option maxHeartbeats 800000

def HasUpperAnalyticExtensionAt (f : ℂ → ℂ) (x : ℝ) : Prop :=
  ∃ r > 0, ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball (x : ℂ) r) ∧
    EqOn f G (ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im})

theorem finite_sum_upper_extension {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (x : ℝ)
    (h : ∀ i ∈ s, HasUpperAnalyticExtensionAt (f i) x) :
    HasUpperAnalyticExtensionAt (fun E => ∑ i ∈ s, f i E) x := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _h
    refine ⟨1,zero_lt_one,(fun _ => 0),(fun _ _ => analyticAt_const),?_⟩
    intro E _hE
    simp
  | @insert i s hi ih =>
    intro h
    obtain ⟨r,hr,F,hF,heF⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨R,hR,G,hG,heG⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have hsub1 : ball (x : ℂ) (min r R) ⊆ ball (x : ℂ) r := ball_subset_ball (min_le_left _ _)
    have hsub2 : ball (x : ℂ) (min r R) ⊆ ball (x : ℂ) R := ball_subset_ball (min_le_right _ _)
    refine ⟨min r R,lt_min hr hR,(fun E => F E+G E),
      (hF.mono hsub1).add (hG.mono hsub2),?_⟩
    intro E hE
    change (∑ j ∈ insert i s, f j E) = F E + G E
    rw [Finset.sum_insert hi,heF ⟨hsub1 hE.1,hE.2⟩]
    exact congrArg (fun z => F E + z) (heG ⟨hsub2 hE.1,hE.2⟩)

theorem finiteEnergyPart_upper_extension (ν : Phase) (σ : Sign) (K : ℕ) (x : ℝ)
    (h : ∀ N : ℕ, 0 < N → N ≤ K → HasUpperAnalyticExtensionAt (particleCoefficient σ N) x) :
    HasUpperAnalyticExtensionAt (finiteEnergyPart ν σ K) x := by
  apply finite_sum_upper_extension
  intro n _hn
  by_cases hn : particleOrder ν n ≤ K
  · simpa only [hn,↓reduceIte] using h (particleOrder ν n) (particleOrder_positive ν n) hn
  · refine ⟨1,zero_lt_one,(fun _ => 0),(fun _ _ => analyticAt_const),?_⟩
    intro E _hE
    simp only [hn,↓reduceIte]

/-- A genuine nondegenerate rectangular upper collar can be chosen within
both an existing collar and a disk centered at one of its boundary points. -/
theorem exists_subcollar_in_ball {a b R x ρ : ℝ} (hx : x ∈ Ioo a b)
    (hR : 0 < R) (hρ : 0 < ρ) :
    ∃ l u h : ℝ, a < l ∧ l < u ∧ u < b ∧ 0 < h ∧
      closedUpperCollar l u h ⊆ closedUpperCollar a b R ∧
      closedUpperCollar l u h ⊆ ball (x : ℂ) ρ := by
  let h : ℝ := min ((x-a)/2) (min ((b-x)/2) (min (R/2) (ρ/4)))
  have hh : 0 < h := lt_min (by linarith [hx.1]) (lt_min (by linarith [hx.2])
    (lt_min (half_pos hR) (by positivity)))
  have hleft : h ≤ (x-a)/2 := min_le_left _ _
  have hright : h ≤ (b-x)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hheight : h ≤ R/2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hball : h ≤ ρ/4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨x-h,x+h,h,by linarith [hx.1],by linarith,by linarith [hx.2],hh,?_,?_⟩
  · intro z hz
    refine ⟨⟨⟨by linarith [hz.1.1.1,hx.1],by linarith [hz.1.1.2,hx.2]⟩,
      ⟨by linarith [hz.1.2.1],by linarith [hz.1.2.2]⟩⟩,hz.2⟩
  · intro z hz
    rw [mem_ball,dist_eq_norm]
    have hre : |z.re-x| < h := abs_lt.mpr ⟨by linarith [hz.1.1.1],by linarith [hz.1.1.2]⟩
    have him : |z.im| < h := abs_lt.mpr hz.1.2
    have hn := Complex.norm_le_abs_re_add_abs_im (z-(x : ℂ))
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,sub_zero] at hn
    linarith

/-- All requirements of the full-energy interval are assembled here. The
finite-particle continuation input to this generic consumer is discharged
in EnergyJetRegularity; the high-particle tail is the proved actual one. -/
theorem regularEnergyJetInterval_of_finite_extensions (ν : Phase) (n : ℕ)
    (hfinite : ∀ a b : ℝ, 0 < a → a < b → b < 2 →
      ∃ x ∈ Ioo a b, ∀ N : ℕ, 0 < N → N ≤ 2*n+4 →
        HasUpperAnalyticExtensionAt (particleCoefficient .positive N) x) :
    Nonempty (RegularEnergyJetInterval ν n) := by
  obtain ⟨a,b,R,hla,hab,hbu,hR,hcont,heq⟩ :=
    energyTail_continuous_jet_interval_uniform ν n
      (l := 1/2) (u := 3/2) (by norm_num) (by norm_num) (by norm_num)
  have ha : 0 < a := by linarith
  have hb : b < 2 := by linarith
  obtain ⟨x,hx,hN⟩ := hfinite a b ha hab hb
  obtain ⟨ρ,hρ,G,hG,heG⟩ := finiteEnergyPart_upper_extension ν .positive (2*n+4) x hN
  obtain ⟨l,u,h,hal,hlu,hub,hh,hsub,hball⟩ := exists_subcollar_in_ball hx hR hρ
  have hupper : upperCollar l u h ⊆ upperCollar a b R :=
    fun z hz => ⟨(hsub (upperCollar_subset_closed _ _ _ hz)).1,hz.2⟩
  have hjet (j : ℕ) (E : ℂ) (hE : E ∈ upperCollar l u h) :
      iteratedDeriv j G E = iteratedDeriv j (finiteEnergyPart ν .positive (2*n+4)) E := by
    have hnb : ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im} ∈ 𝓝 E :=
      (isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)).mem_nhds
        ⟨hball (upperCollar_subset_closed _ _ _ hE),hE.2⟩
    have he : G =ᶠ[𝓝 E] finiteEnergyPart ν .positive (2*n+4) := by
      filter_upwards [hnb] with z hz
      exact (heG hz).symm
    exact he.iteratedDeriv_eq j
  refine ⟨{
    left := l
    right := u
    height := h
    left_pos := ha.trans hal
    left_lt_right := hlu
    right_lt_two := hub.trans hb
    height_pos := hh
    jet := fun j E => iteratedDeriv j G E + tailUpperJet ν n j E
    continuous := ?_
    agrees := ?_ }⟩
  · intro j hj
    have hg : ContinuousOn (iteratedDeriv j G) (closedUpperCollar l u h) :=
      fun E hE => (IsingBulk.First.analyticAt_iteratedDeriv (hG E (hball hE)) j).continuousAt.continuousWithinAt
    exact hg.add ((hcont j (by omega)).mono hsub)
  · intro E hE j hj
    rw [hjet j E hE,heq E (hupper hE) j (by omega)]
    exact (fullEnergySum_jet_eq_finite_add_tail ν (2*n+4) j (Or.inl hE.2.ne')).symm

end
end IsoProof
