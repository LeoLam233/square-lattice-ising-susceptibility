import IsoProof.ResonanceCoordinate
import IsoProof.ResonancePrimes
import IsoProof.IntegralsReflection

/-! The actual common radial approach and its energy image.  The concrete
exterior energy inverse is shown to return exactly the same temperature
point.  The prime mesh remains dense in every positive real energy interval,
with both critical orders arbitrarily large. -/
namespace IsoProof
noncomputable section
open Complex Filter Set
open IsingBulk.PrimeFamily
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def radialTemperature (ζ : ℂ) (t : ℝ) : ℂ := (1+(t:ℂ))*ζ

def radialEnergy (ζ : ℂ) (t : ℝ) : ℂ := energy (radialTemperature ζ t)

theorem radialTemperature_tendsto (ζ : ℂ) :
    Tendsto (radialTemperature ζ) (𝓝[>] (0:ℝ)) (𝓝 ζ) := by
  have hc : Continuous (radialTemperature ζ) := by unfold radialTemperature; fun_prop
  simpa only [radialTemperature,Complex.ofReal_zero,add_zero,one_mul] using
    (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

theorem radialTemperature_exterior {ζ : ℂ} (hζ : ‖ζ‖=1) {t : ℝ} (ht : 0<t) :
    1<‖radialTemperature ζ t‖ := by
  simp only [radialTemperature,norm_mul,hζ,mul_one,←Complex.ofReal_one,
    ←Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos (by linarith : 0<1+t)]
  linarith

theorem energy_injective_exterior {u s : ℂ} (hu : 1<‖u‖) (hs : 1<‖s‖)
    (he : energy u=energy s) : u=s := by
  have hu0 : u≠0 := by intro h; norm_num [h] at hu
  have hs0 : s≠0 := by intro h; norm_num [h] at hs
  have hmul := congrArg (fun w : ℂ=>w*u*s) he
  dsimp only [energy] at hmul
  have hfactor : (u-s)*(u*s-1)=0 := by
    field_simp [hu0,hs0] at hmul
    linear_combination hmul
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have hprod : u*s=1 := sub_eq_zero.mp h
    have hn : ‖u‖*‖s‖=1 := by rw [←norm_mul,hprod,norm_one]
    nlinarith

theorem exteriorEnergyInverse_energy {s : ℂ} (hs : 1<‖s‖) :
    exteriorEnergyInverse (energy s)=s := by
  obtain ⟨hu,he⟩ := exteriorEnergyInverse_spec (energy_mem_domain_of_exterior hs)
  exact energy_injective_exterior hu hs he

theorem exteriorEnergyInverse_radialEnergy {ζ : ℂ} (hζ : ‖ζ‖=1)
    {t : ℝ} (ht : 0<t) :
    exteriorEnergyInverse (radialEnergy ζ t)=radialTemperature ζ t :=
  exteriorEnergyInverse_energy (radialTemperature_exterior hζ ht)

theorem radialEnergy_tendsto {ζ : ℂ} (hζ : ζ≠0) :
    Tendsto (radialEnergy ζ) (𝓝[>] (0:ℝ)) (𝓝 (energy ζ)) :=
  (energy_analyticAt hζ).continuousAt.tendsto.comp (radialTemperature_tendsto ζ)

theorem radialEnergy_im {ζ : ℂ} (hζ : ‖ζ‖=1) (t : ℝ) :
    (radialEnergy ζ t).im=((1+t)-(1+t)⁻¹)*ζ.im := by
  have hreal : 1+(t:ℂ)=((1+t:ℝ):ℂ) := by push_cast; rfl
  simp only [radialEnergy,radialTemperature,energy,hreal,mul_inv_rev,
    Complex.inv_eq_conj hζ,←Complex.ofReal_inv,Complex.add_im,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_im,mul_zero,zero_mul,add_zero,zero_add]
  ring

theorem radialEnergy_upper {ζ : ℂ} (hζ : ‖ζ‖=1) (him : 0<ζ.im)
    {t : ℝ} (ht : 0<t) : 0<(radialEnergy ζ t).im := by
  rw [radialEnergy_im hζ]
  have hinv : (1+t)⁻¹<1 := (inv_lt_one₀ (by linarith : 0<1+t)).mpr (by linarith)
  exact mul_pos (by linarith) him

theorem angleRoot_unit (p : ℕ) (a : ℤ) :
    ‖IsingBulk.PrimeFamily.angleRoot p a‖=1 := Complex.norm_exp_ofReal_mul_I _

theorem prime_root_energy (p : ℕ) (a : ℤ) :
    energy (IsingBulk.PrimeFamily.angleRoot p a)=((2*Real.cos (angle p a):ℝ):ℂ) := by
  simpa only [energy,IsingBulk.PrimeFamily.angleRoot,Complex.ofReal_mul,Complex.ofReal_ofNat]
    using exp_angle_add_inv (angle p a)

theorem admissible_root_geometry {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) {a : ℤ}
    (ha : Admissible p a) :
    ‖IsingBulk.PrimeFamily.angleRoot p a‖=1 ∧
    0<(IsingBulk.PrimeFamily.angleRoot p a).re ∧
    0<(IsingBulk.PrimeFamily.angleRoot p a).im ∧
    (IsingBulk.PrimeFamily.angleRoot p a)^4≠1 ∧
    0<2*Real.cos (angle p a) ∧ 2*Real.cos (angle p a)<2 := by
  have hcos : 0<Real.cos (angle p a) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ha.1,Real.pi_pos],ha.2⟩
  have hcos1 : Real.cos (angle p a)<1 := by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by norm_num : (0:ℝ)≤0) (by linarith [ha.2,Real.pi_pos] : angle p a≤Real.pi) ha.1
  have hsin : 0<Real.sin (angle p a) := Real.sin_pos_of_pos_of_lt_pi ha.1
    (by linarith [ha.2,Real.pi_pos])
  have hre : (IsingBulk.PrimeFamily.angleRoot p a).re=Real.cos (angle p a) := by
    simp [IsingBulk.PrimeFamily.angleRoot,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  have him : (IsingBulk.PrimeFamily.angleRoot p a).im=Real.sin (angle p a) := by
    simp [IsingBulk.PrimeFamily.angleRoot,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  refine ⟨angleRoot_unit p a,by rwa [hre],by rwa [him],?_,by linarith,by linarith⟩
  intro hfour
  have hdiv := (angleRoot_primitive hp ha).dvd_of_pow_eq_one 4 hfour
  have hle := Nat.le_of_dvd (by norm_num : 0<4) hdiv
  omega

/-- The radial energy path reaches the real cut strictly from above. -/
theorem admissible_radialEnergy_tendsto_upper {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : Admissible p a) :
    Tendsto (radialEnergy (IsingBulk.PrimeFamily.angleRoot p a)) (𝓝[>] (0:ℝ))
      (𝓝[{E:ℂ|0<E.im}] ((2*Real.cos (angle p a):ℝ):ℂ)) := by
  have hgeo := admissible_root_geometry hp hp5 ha
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · rw [←prime_root_energy]
    exact radialEnergy_tendsto (by intro hz; norm_num [hz] at hgeo)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact radialEnergy_upper hgeo.1 hgeo.2.2.1 ht

/-- Every positive energy interval contains a simultaneous HT/LT singular
level whose sharp derivative orders exceed any prescribed r. -/
theorem exists_common_prime_energy_in_interval (r : ℕ) {a b : ℝ}
    (ha : 0<a) (hab : a<b) (hb : b<2) :
    ∃ p : ℕ,∃ j : ℤ,p.Prime ∧ 5≤p ∧ Admissible p j ∧
      r<criticalOrder p ∧ r<criticalOrder (2*p) ∧
      2*Real.cos (angle p j)∈Ioo a b := by
  let x := (a+b)/2
  let θ := Real.arccos (x/2)
  have hx : x∈Ioo a b := by dsimp [x]; constructor <;> linarith
  have hx0 : 0<x := ha.trans hx.1
  have hx2 : x<2 := hx.2.trans hb
  have hθ0 : 0<θ := Real.arccos_pos.mpr (by linarith)
  have hθπ : θ<Real.pi/2 := Real.arccos_lt_pi_div_two.mpr (by linarith)
  have hcos : 2*Real.cos θ=x := by
    dsimp only [θ]
    rw [Real.cos_arccos (by linarith) (by linarith)]
    ring
  have hneigh : {t:ℝ|2*Real.cos t∈Ioo a b}∈𝓝 θ :=
    (continuous_const.mul Real.continuous_cos).continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds (by change 2*Real.cos θ∈Ioo a b; rw [hcos]; exact hx))
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hneigh
  obtain ⟨p,j,k,hp,hp11,hpP,_hjk,hj,_hk,hclose,_hclosek⟩ :=
    neighboring_prime_angles_above (2*r+4) hθ0 hθπ hδ
  refine ⟨p,j,hp,by omega,hj,criticalOrder_unbounded r p hpP,
    criticalOrder_unbounded r (2*p) (by omega),?_⟩
  apply hδsub
  simpa only [Metric.mem_ball,Real.dist_eq] using hclose

end
end IsoProof
