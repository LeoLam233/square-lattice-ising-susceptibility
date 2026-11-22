import IsoProof.ResonanceFullSeries
import IsoProof.ResonanceEnergy
import IsoProof.ResonancePaths
import IsoProof.PhysicalFactors
import IsoProof.PhysicalBoundary
import IsoProof.SeparantCriterion

/-! Actual sharp singularities of the literal full sums and susceptibilities.
The only arithmetic inputs to the prime-family producers are primality and
the explicit admissible integer angle.  Full-series asymptotics, identities,
coordinate factors and normalizations are supplied by proved theorems. -/
namespace IsoProof
noncomputable section
open Complex Filter Set Asymptotics
open IsingBulk.PrimeFamily IsingBulk.HT22.Arithmetic
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def exteriorTemperatureSum (ν : Phase) (s : ℂ) : ℂ :=
  fullEnergySum ν .positive (energy s)

def phaseCriticalOrder (ν : Phase) (p : ℕ) : ℕ :=
  match ν with
  | .high => criticalOrder p
  | .low => criticalOrder (2*p)

/-- Exact sharp jets, with actual iterated complex derivatives. -/
def SharpJetsAlong (f : ℂ→ℂ) (path : ℝ→ℂ) (k : ℕ) : Prop :=
  Tendsto (fun t=>‖iteratedDeriv k f (path t)‖) (𝓝[>] 0) atTop ∧
    ∀ j<k,(fun t=>iteratedDeriv j f (path t))=O[𝓝[>] 0](fun _=>(1:ℂ))

private theorem radial_bound_isBigO {F : ℝ→ℂ}
    (h : ∃ δ C : ℝ,0<δ ∧ 0<C ∧ ∀ t∈Ioc 0 δ,‖F t‖≤C) :
    F=O[𝓝[>] 0](fun _=>(1:ℂ)) := by
  obtain ⟨δ,C,hδ,_hC,hb⟩ := h
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C,?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
  simpa only [norm_one,mul_one] using hb t ⟨ht,htδ.le⟩

private theorem exteriorTemperatureSum_low_eventuallyEq {s : ℂ} (hs : 1<‖s‖) :
    exteriorTemperatureSum .low=ᶠ[𝓝 s] IsingBulk.Preferred22.evenSeries := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hs] with u hu
  exact fullEnergySum_low_energy hu

theorem exteriorTemperatureSum_high_eq :
    exteriorTemperatureSum .high=IsingBulk.HT22.Physical.signedOddSeries false :=
  funext fullEnergySum_high_positive_signed_energy

/-- Both complete sums at the same explicit first-quadrant prime root. -/
theorem exterior_prime_sharp (ν : Phase) {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) :
    SharpJetsAlong (exteriorTemperatureSum ν)
      (radialTemperature (IsingBulk.PrimeFamily.angleRoot p a)) (phaseCriticalOrder ν p) := by
  cases ν with
  | high =>
      have hindex := primeIndex_of_admissible hp.pos ha
      have hn : ¬Real.pi/2<angle p a := not_lt.mpr ha.2.le
      have hsign : negativeSide (angle p a)=false := by simp [negativeSide,hn]
      have hα : (primeBranchData hp hp5 hindex).alpha=angle p a := by
        simp [primeBranchData,positiveTraceBranchData,effectiveAngle,hn]
      have hh := high_prime_sharp_full_sum hp hp5 hindex
      rw [hsign,hα] at hh
      rw [exteriorTemperatureSum_high_eq]
      constructor
      · simpa only [phaseCriticalOrder,radialTemperature,IsingBulk.PrimeFamily.angleRoot,
          IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one] using hh.1
      · intro j hj
        apply radial_bound_isBigO
        simpa only [radialTemperature,IsingBulk.PrimeFamily.angleRoot,
          IsingBulk.Branch.radialParameter,Complex.ofReal_add,Complex.ofReal_one]
          using hh.2 j hj
  | low =>
      have hh := low_prime_sharp_full_sum hp hp5 ha
      have heq (j : ℕ) :
          (fun t=>iteratedDeriv j (exteriorTemperatureSum .low)
            (radialTemperature (IsingBulk.PrimeFamily.angleRoot p a) t))=ᶠ[𝓝[>] 0]
          (fun t=>iteratedDeriv j IsingBulk.Preferred22.evenSeries
            (radialTemperature (IsingBulk.PrimeFamily.angleRoot p a) t)) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact (exteriorTemperatureSum_low_eventuallyEq
          (radialTemperature_exterior (angleRoot_unit p a) ht)).iteratedDeriv_eq j
      constructor
      · exact hh.1.congr' ((heq _).symm.fun_comp norm)
      · intro j hj
        obtain ⟨L,hL⟩ := hh.2 j hj
        exact (hL.isBigO_one ℂ).congr' (heq j).symm Filter.EventuallyEq.rfl

theorem exteriorTemperatureSum_analyticAt {s : ℂ} (ν : Phase) (hs : 1<‖s‖) :
    AnalyticAt ℂ (exteriorTemperatureSum ν) s := by
  have hs0 : s≠0 := by intro h; norm_num [h] at hs
  cases ν with
  | high =>
      exact (fullEnergySum_high_analyticAt_energy .positive hs).comp (energy_analyticAt hs0)
  | low =>
      exact (fullEnergySum_low_analyticAt_energy hs).comp (energy_analyticAt hs0)

/-- The temperature full sum is exactly invariant under inversion because
its literal definition is a function of E=s+s⁻¹. -/
theorem exteriorTemperatureSum_inv (ν : Phase) (s : ℂ) :
    exteriorTemperatureSum ν s⁻¹=exteriorTemperatureSum ν s := by
  simp only [exteriorTemperatureSum,energy_inv]

def physicalRadialPath (ν : Phase) (ζ : ℂ) (t : ℝ) : ℂ :=
  match ν with
  | .high => (radialTemperature ζ t)⁻¹
  | .low => radialTemperature ζ t

def physicalBoundaryPoint (ν : Phase) (ζ : ℂ) : ℂ :=
  match ν with
  | .high => ζ⁻¹
  | .low => ζ

theorem physicalRadialPath_tendsto (ν : Phase) {ζ : ℂ} (hζ : ζ≠0) :
    Tendsto (physicalRadialPath ν ζ) (𝓝[>] 0) (𝓝 (physicalBoundaryPoint ν ζ)) := by
  cases ν with
  | high => exact (continuousAt_inv₀ hζ).tendsto.comp (radialTemperature_tendsto ζ)
  | low => exact radialTemperature_tendsto ζ

theorem physicalRadialPath_mem (ν : Phase) {ζ : ℂ} (hζ : ‖ζ‖=1) {t : ℝ} (ht : 0<t) :
    physicalRadialPath ν ζ t∈physicalDomain ν ∧ physicalRadialPath ν ζ t≠0 := by
  have hr := radialTemperature_exterior hζ ht
  have hr0 : radialTemperature ζ t≠0 := by intro h; norm_num [h] at hr
  cases ν with
  | high =>
      refine ⟨?_,inv_ne_zero hr0⟩
      change ‖(radialTemperature ζ t)⁻¹‖<1
      rw [norm_inv]
      exact (inv_lt_one₀ (norm_pos_iff.mpr hr0)).mpr hr
  | low => exact ⟨hr,hr0⟩

/-- Genuine interior HT and exterior LT sharp jets before the analytic
physical prefactors are applied. -/
theorem physical_source_prime_sharp (ν : Phase) {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) :
    SharpJetsAlong (exteriorTemperatureSum ν)
      (physicalRadialPath ν (IsingBulk.PrimeFamily.angleRoot p a)) (phaseCriticalOrder ν p) := by
  have hζ := angleRoot_unit p a
  have hζ0 : IsingBulk.PrimeFamily.angleRoot p a≠0 := by intro h; norm_num [h] at hζ
  have hh := exterior_prime_sharp ν hp hp5 ha
  cases ν with
  | low => exact hh
  | high =>
      have hginv : AnalyticAt ℂ (fun z : ℂ=>z⁻¹) (IsingBulk.PrimeFamily.angleRoot p a)⁻¹ :=
        analyticAt_id.inv (inv_ne_zero hζ0)
      have hg' : deriv (fun z : ℂ=>z⁻¹) (IsingBulk.PrimeFamily.angleRoot p a)⁻¹≠0 := by
        rw [deriv_inv]
        exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 (inv_ne_zero hζ0)))
      have han : ∀ᶠ t in 𝓝[>] (0:ℝ),AnalyticAt ℂ (exteriorTemperatureSum .high)
          ((physicalRadialPath .high (IsingBulk.PrimeFamily.angleRoot p a) t)⁻¹) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [physicalRadialPath,inv_inv]
        exact exteriorTemperatureSum_analyticAt .high (radialTemperature_exterior hζ ht)
      have ht : Tendsto (fun t=>‖iteratedDeriv (phaseCriticalOrder .high p)
          (exteriorTemperatureSum .high)
          ((physicalRadialPath .high (IsingBulk.PrimeFamily.angleRoot p a) t)⁻¹)‖)
          (𝓝[>] 0) atTop := by simpa only [physicalRadialPath,inv_inv] using hh.1
      have hb : ∀ j<phaseCriticalOrder .high p,
          (fun t=>iteratedDeriv j (exteriorTemperatureSum .high)
            ((physicalRadialPath .high (IsingBulk.PrimeFamily.angleRoot p a) t)⁻¹))
            =O[𝓝[>] 0](fun _=>(1:ℂ)) := by
        simpa only [physicalRadialPath,inv_inv] using hh.2
      have h := sharp_jets_comp (physicalRadialPath_tendsto .high hζ0) hginv hg'
        (phaseCriticalOrder .high p) han ht hb
      have he : exteriorTemperatureSum .high∘(fun z : ℂ=>z⁻¹)=exteriorTemperatureSum .high :=
        funext (exteriorTemperatureSum_inv .high)
      rw [he] at h
      exact h

/-- Sharp jets depend only on the actual analytic germ at each approach point. -/
theorem SharpJetsAlong.congr {f g : ℂ→ℂ} {path : ℝ→ℂ} {k : ℕ}
    (hf : SharpJetsAlong f path k)
    (he : ∀ᶠ t in 𝓝[>] (0:ℝ),f=ᶠ[𝓝 (path t)]g) : SharpJetsAlong g path k := by
  have hj (j : ℕ) : (fun t=>iteratedDeriv j f (path t))=ᶠ[𝓝[>] 0]
      (fun t=>iteratedDeriv j g (path t)) := he.mono (fun _ h=>h.iteratedDeriv_eq j)
  exact ⟨hf.1.congr' ((hj k).fun_comp norm),fun j hlt=>
    (hf.2 j hlt).congr' (hj j) Filter.EventuallyEq.rfl⟩

private theorem physical_source_analyticAt (ν : Phase) {ζ : ℂ}
    (hζ : ‖ζ‖=1) {t : ℝ} (ht : 0<t) :
    AnalyticAt ℂ (exteriorTemperatureSum ν) (physicalRadialPath ν ζ t) := by
  have hr := radialTemperature_exterior hζ ht
  have hr0 : radialTemperature ζ t≠0 := by intro h; norm_num [h] at hr
  cases ν with
  | low => exact exteriorTemperatureSum_analyticAt .low hr
  | high =>
      have ha := exteriorTemperatureSum_analyticAt .high hr
      have hi : AnalyticAt ℂ (fun s : ℂ=>s⁻¹) (radialTemperature ζ t)⁻¹ :=
        analyticAt_id.inv (inv_ne_zero hr0)
      have hcomp : AnalyticAt ℂ (exteriorTemperatureSum .high∘(fun s : ℂ=>s⁻¹))
          (radialTemperature ζ t)⁻¹ := by
        apply AnalyticAt.comp _ hi
        simpa only [inv_inv] using ha
      exact hcomp.congr (Filter.Eventually.of_forall (exteriorTemperatureSum_inv .high))

private theorem physicalBoundaryPoint_geometry (ν : Phase) {p : ℕ}
    (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : Admissible p a) :
    ‖physicalBoundaryPoint ν (IsingBulk.PrimeFamily.angleRoot p a)‖=1 ∧
    (physicalBoundaryPoint ν (IsingBulk.PrimeFamily.angleRoot p a))^4≠1 ∧
    (physicalBoundaryPoint ν (IsingBulk.PrimeFamily.angleRoot p a)).re≠0 := by
  obtain ⟨hz,hre,_him,hfour,_hlevel⟩ := admissible_root_geometry hp hp5 ha
  cases ν with
  | low => exact ⟨hz,hfour,hre.ne'⟩
  | high =>
      refine ⟨by simp only [physicalBoundaryPoint,norm_inv,hz,inv_one],?_,?_⟩
      · intro h
        apply hfour
        have h' := congrArg Inv.inv h
        simpa only [physicalBoundaryPoint,inv_pow,inv_inv,inv_one] using h'
      · simpa only [physicalBoundaryPoint,Complex.inv_eq_conj hz,Complex.conj_re] using hre.ne'

private theorem reduced_local_eq_product (ν : Phase) {s : ℂ} (hs0 : s≠0) :
    reducedSusceptibility ν=ᶠ[𝓝 s](exteriorTemperatureSum ν*normalization ν) := by
  filter_upwards [eventually_ne_nhds hs0] with u hu
  simp only [reducedSusceptibility,hu,and_false,ite_false,Pi.mul_apply,
    exteriorTemperatureSum,mul_comm]

private theorem physical_local_eq_product (ν : Phase) (J : ℝ) {s : ℂ} (hs0 : s≠0) :
    physicalSusceptibility ν J=ᶠ[𝓝 s](exteriorTemperatureSum ν*physicalPrefactor ν J) := by
  filter_upwards [reduced_local_eq_product ν hs0] with u hu
  simp only [physicalSusceptibility,physicalPrefactor,Pi.mul_apply] at hu ⊢
  rw [hu]
  ring

/-- The reduced susceptibilities themselves have the stated sharp jets at
arbitrarily high prime orders, in their correct physical domains. -/
theorem reduced_prime_sharp (ν : Phase) {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) :
    SharpJetsAlong (reducedSusceptibility ν)
      (physicalRadialPath ν (IsingBulk.PrimeFamily.angleRoot p a)) (phaseCriticalOrder ν p) := by
  have hζ := angleRoot_unit p a
  have hζ0 : IsingBulk.PrimeFamily.angleRoot p a≠0 := by intro h; norm_num [h] at hζ
  have hh := physical_source_prime_sharp ν hp hp5 ha
  obtain ⟨hz,hfour,_hre⟩ := physicalBoundaryPoint_geometry ν hp hp5 ha
  obtain ⟨hA,hA0⟩ := normalization_regular_at_unit_nonaxis ν hz hfour
  have hm : SharpJetsAlong (exteriorTemperatureSum ν*normalization ν)
      (physicalRadialPath ν (IsingBulk.PrimeFamily.angleRoot p a)) (phaseCriticalOrder ν p) :=
    sharp_jets_mul (physicalRadialPath_tendsto ν hζ0) hA hA0 (phaseCriticalOrder ν p)
      ((show ∀ᶠ t in 𝓝[>] (0:ℝ), 0<t from self_mem_nhdsWithin).mono
        (fun _ ht=>physical_source_analyticAt ν hζ ht)) hh.1 hh.2
  apply hm.congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (reduced_local_eq_product ν (physicalRadialPath_mem ν hζ ht).2).symm

/-- The canonical physical susceptibility, including beta, has the same
sharp derivative order.  beta's nonzero value is supplied by PhysicalFactors. -/
theorem physical_prime_sharp (ν : Phase) {J : ℝ} (hJ : 0<J)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : Admissible p a) :
    SharpJetsAlong (physicalSusceptibility ν J)
      (physicalRadialPath ν (IsingBulk.PrimeFamily.angleRoot p a)) (phaseCriticalOrder ν p) := by
  have hζ := angleRoot_unit p a
  have hζ0 : IsingBulk.PrimeFamily.angleRoot p a≠0 := by intro h; norm_num [h] at hζ
  have hh := physical_source_prime_sharp ν hp hp5 ha
  obtain ⟨hz,hfour,hre⟩ := physicalBoundaryPoint_geometry ν hp hp5 ha
  obtain ⟨hA,hA0⟩ := physicalPrefactor_regular_at_unit_nonaxis ν hJ hz hfour hre
  have hm : SharpJetsAlong (exteriorTemperatureSum ν*physicalPrefactor ν J)
      (physicalRadialPath ν (IsingBulk.PrimeFamily.angleRoot p a)) (phaseCriticalOrder ν p) :=
    sharp_jets_mul (physicalRadialPath_tendsto ν hζ0) hA hA0 (phaseCriticalOrder ν p)
      ((show ∀ᶠ t in 𝓝[>] (0:ℝ), 0<t from self_mem_nhdsWithin).mono
        (fun _ ht=>physical_source_analyticAt ν hζ ht)) hh.1 hh.2
  apply hm.congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (physical_local_eq_product ν J (physicalRadialPath_mem ν hζ ht).2).symm

/-- The actual chart from the upper energy half plane to the corresponding
physical temperature domain. -/
def physicalEnergyChart (ν : Phase) (E : ℂ) : ℂ :=
  match ν with
  | .high => (exteriorEnergyInverse E)⁻¹
  | .low => exteriorEnergyInverse E

theorem physicalEnergyChart_radialEnergy (ν : Phase) {ζ : ℂ} (hζ : ‖ζ‖=1)
    {t : ℝ} (ht : 0<t) :
    physicalEnergyChart ν (radialEnergy ζ t)=physicalRadialPath ν ζ t := by
  cases ν <;> simp only [physicalEnergyChart,physicalRadialPath,
    exteriorEnergyInverse_radialEnergy hζ ht]

theorem admissible_radialEnergy_tendsto_collar {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) {L U R : ℝ} (hR : 0<R)
    (hx : 2*Real.cos (angle p a)∈Ioo L U) :
    Tendsto (radialEnergy (IsingBulk.PrimeFamily.angleRoot p a)) (𝓝[>] (0:ℝ))
      (𝓝[upperCollar L U R] ((2*Real.cos (angle p a):ℝ):ℂ)) := by
  have hpE := admissible_radialEnergy_tendsto_upper hp hp5 ha
  have hp0 := hpE.mono_right nhdsWithin_le_nhds
  have hmem : ((2*Real.cos (angle p a):ℝ):ℂ)∈realCollar L U R :=
    (ofReal_mem_closedUpperCollar hR hx).1
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hp0,?_⟩
  filter_upwards [eventually_mem_of_tendsto_nhdsWithin hpE,
    hp0.eventually ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hmem)] with t ht htC
  exact ⟨htC,ht⟩

private theorem sharpBoundaryApproach_of_prime_sharp {f : ℂ→ℂ} (ν : Phase)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : Admissible p a)
    {L U R : ℝ} (hR : 0<R) (hx : 2*Real.cos (angle p a)∈Ioo L U) {k : ℕ}
    (hsharp : SharpJetsAlong f
      (physicalRadialPath ν (IsingBulk.PrimeFamily.angleRoot p a)) k) :
    SharpBoundaryApproach f (physicalEnergyChart ν) L U R (2*Real.cos (angle p a)) k := by
  have he (j : ℕ) :
      (fun t=>iteratedDeriv j f (physicalRadialPath ν (IsingBulk.PrimeFamily.angleRoot p a) t))
        =ᶠ[𝓝[>] 0] (fun t=>iteratedDeriv j f
          (physicalEnergyChart ν (radialEnergy (IsingBulk.PrimeFamily.angleRoot p a) t))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [physicalEnergyChart_radialEnergy ν (angleRoot_unit p a) ht]
  refine ⟨radialEnergy (IsingBulk.PrimeFamily.angleRoot p a),
    admissible_radialEnergy_tendsto_collar hp hp5 ha hR hx,
    hsharp.1.congr' ((he k).fun_comp norm),?_⟩
  intro j hj
  have hb := (hsharp.2 j hj).congr' (he j) Filter.EventuallyEq.rfl
  simpa only [NormBoundedAlong,Asymptotics.isBigO_iff,norm_one,mul_one] using hb

theorem reduced_prime_sharp_boundary (ν : Phase) {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) {L U R : ℝ} (hR : 0<R)
    (hx : 2*Real.cos (angle p a)∈Ioo L U) :
    SharpBoundaryApproach (reducedSusceptibility ν) (physicalEnergyChart ν)
      L U R (2*Real.cos (angle p a)) (phaseCriticalOrder ν p) :=
  sharpBoundaryApproach_of_prime_sharp ν hp hp5 ha hR hx (reduced_prime_sharp ν hp hp5 ha)

theorem physical_prime_sharp_boundary (ν : Phase) {J : ℝ} (hJ : 0<J)
    {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ} (ha : Admissible p a)
    {L U R : ℝ} (hR : 0<R) (hx : 2*Real.cos (angle p a)∈Ioo L U) :
    SharpBoundaryApproach (physicalSusceptibility ν J) (physicalEnergyChart ν)
      L U R (2*Real.cos (angle p a)) (phaseCriticalOrder ν p) :=
  sharpBoundaryApproach_of_prime_sharp ν hp hp5 ha hR hx (physical_prime_sharp ν hJ hp hp5 ha)

end
end IsoProof
