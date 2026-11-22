import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Zero boundary trace uniqueness on an upper rectangular collar

This proves the zero-trace case of Schwarz reflection used in §5.  The proof
is Morera's theorem: clamping the imaginary endpoints of a rectangle to zero
does not change its boundary integral when the function is zero below the real
axis.  The clipped rectangle lies in the closed upper half plane, where
Cauchy--Goursat applies.  There is no assumption of analytic continuation across
the real interval in the statement.
-/
namespace IsoProof
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Interval

set_option maxHeartbeats 1000000

/-- The open rectangular collar around a real interval. -/
def realCollar (a b R : ℝ) : Set ℂ := Ioo a b ×ℂ Ioo (-R) R

/-- Projection of the lower half plane onto the real line. -/
def upperClamp (z : ℂ) : ℂ := (z.re:ℂ)+(max z.im 0:ℝ)*Complex.I

@[simp] theorem upperClamp_re (z : ℂ) : (upperClamp z).re=z.re := by
  simp [upperClamp]
@[simp] theorem upperClamp_im (z : ℂ) : (upperClamp z).im=max z.im 0 := by
  simp [upperClamp]

theorem continuous_upperClamp : Continuous upperClamp := by
  unfold upperClamp
  fun_prop

theorem upperClamp_eq_self {z : ℂ} (hz : 0≤z.im) : upperClamp z=z := by
  simp [upperClamp,max_eq_left hz]

theorem upperClamp_mem_collar {a b R : ℝ} (hR : 0<R) {z : ℂ}
    (hz : z∈realCollar a b R) : upperClamp z∈realCollar a b R := by
  rcases hz with ⟨hx,hy⟩
  refine ⟨by simpa using hx,?_⟩
  simpa only [mem_preimage,upperClamp_im,mem_Ioo] using
    And.intro (lt_of_lt_of_le (neg_lt_zero.mpr hR) (le_max_right z.im 0))
      (max_lt hy.2 hR)

private theorem intervalIntegral_eq_clamp {g : ℝ→ℂ} {R u v : ℝ} (hR : 0<R)
    (hg : ContinuousOn g (Ioo (-R) R))
    (hzero : ∀ y∈Ioo (-R) R,y≤0→g y=0)
    (hu : u∈Ioo (-R) R) (hv : v∈Ioo (-R) R) :
    (∫ y in u..v,g y)=∫ y in max u 0..max v 0,g y := by
  have h0 : (0:ℝ)∈Ioo (-R) R := ⟨neg_lt_zero.mpr hR,hR⟩
  have hmax {y : ℝ} (hy : y∈Ioo (-R) R) : max y 0∈Ioo (-R) R :=
    ⟨lt_of_lt_of_le h0.1 (le_max_right _ _),max_lt hy.2 hR⟩
  have hi {x y : ℝ} (hx : x∈Ioo (-R) R) (hy : y∈Ioo (-R) R) :
      IntervalIntegrable g volume x y :=
    (hg.mono (ordConnected_Ioo.uIcc_subset hx hy)).intervalIntegrable
  have hbase {y : ℝ} (hy : y∈Ioo (-R) R) :
      (∫ t in 0..y,g t)=∫ t in 0..max y 0,g t := by
    by_cases hy0 : 0≤y
    · rw [max_eq_left hy0]
    · have hy0' : y≤0 := le_of_lt (lt_of_not_ge hy0)
      rw [max_eq_right hy0',intervalIntegral.integral_same]
      calc
        (∫ t in 0..y,g t)=(∫ t in 0..y,(0:ℂ)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact hzero t (ordConnected_Ioo.uIcc_subset h0 hy ht)
            (by
              have ht' : t∈Icc y 0 := by simpa only [uIcc_of_ge hy0'] using ht
              exact ht'.2)
        _=0 := intervalIntegral.integral_zero
  have huv := intervalIntegral.integral_add_adjacent_intervals (hi h0 hu) (hi hu hv)
  have hm := intervalIntegral.integral_add_adjacent_intervals
    (hi h0 (hmax hu)) (hi (hmax hu) (hmax hv))
  rw [hbase hu,hbase hv] at huv
  exact add_left_cancel (huv.trans hm.symm)

private theorem collar_rectangle_subset {a b R : ℝ} {z w : ℂ}
    (hz : z∈realCollar a b R) (hw : w∈realCollar a b R) :
    Rectangle z w ⊆realCollar a b R := by
  intro t ht
  exact ⟨ordConnected_Ioo.uIcc_subset hz.1 hw.1 ht.1,
    ordConnected_Ioo.uIcc_subset hz.2 hw.2 ht.2⟩

/-- A continuous function which is holomorphic above the real axis and zero
on and below it is holomorphic across the real axis. -/
theorem differentiableOn_collar_of_zero_below {f : ℂ→ℂ} {a b R : ℝ}
    (hR : 0<R) (hc : ContinuousOn f (realCollar a b R))
    (hd : DifferentiableOn ℂ f (realCollar a b R∩{z:ℂ|0<z.im}))
    (hz : ∀ z∈realCollar a b R,z.im≤0→f z=0) :
    DifferentiableOn ℂ f (realCollar a b R) := by
  have hopen : IsOpen (realCollar a b R) := isOpen_Ioo.reProdIm isOpen_Ioo
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hopen).mp
  refine ⟨?_,hc⟩
  intro z w hrect
  have hzm : z∈realCollar a b R := hrect ⟨left_mem_uIcc,left_mem_uIcc⟩
  have hwm : w∈realCollar a b R := hrect ⟨right_mem_uIcc,right_mem_uIcc⟩
  have hzc := upperClamp_mem_collar hR hzm
  have hwc := upperClamp_mem_collar hR hwm
  have hclip := collar_rectangle_subset hzc hwc
  have hhorizontal {y : ℝ} (hy : y∈Ioo (-R) R) :
      (∫ x in z.re..w.re,f ((x:ℂ)+(y:ℂ)*Complex.I))=
      ∫ x in z.re..w.re,f ((x:ℂ)+(max y 0:ℝ)*Complex.I) := by
    by_cases hy0 : 0≤y
    · rw [max_eq_left hy0]
    · have hy0' : y≤0 := le_of_lt (lt_of_not_ge hy0)
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' := ordConnected_Ioo.uIcc_subset hzm.1 hwm.1 hx
      have hxy : (x:ℂ)+(y:ℂ)*Complex.I∈realCollar a b R := by
        simpa [realCollar,mem_reProdIm] using And.intro hx' hy
      have hx0 : (x:ℂ)∈realCollar a b R := by
        simpa [realCollar,mem_reProdIm] using And.intro hx'
          (show (0:ℝ)∈Ioo (-R) R from ⟨neg_lt_zero.mpr hR,hR⟩)
      dsimp only
      rw [hz _ hxy (by simpa using hy0'),max_eq_right hy0']
      simp only [Complex.ofReal_zero,zero_mul,add_zero]
      exact (hz _ hx0 (by simp)).symm
  have hvertical {x : ℝ} (hx : x∈Ioo a b) :
      (∫ y in z.im..w.im,f ((x:ℂ)+(y:ℂ)*Complex.I))=
      ∫ y in max z.im 0..max w.im 0,f ((x:ℂ)+(y:ℂ)*Complex.I) := by
    apply intervalIntegral_eq_clamp hR _ _ hzm.2 hwm.2
    · apply hc.comp (by fun_prop)
      intro y hy
      simpa [realCollar,mem_reProdIm] using And.intro hx hy
    · intro y hy hy0
      apply hz
      · simpa [realCollar,mem_reProdIm] using And.intro hx hy
      · simpa using hy0
  have hcg := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (upperClamp z) (upperClamp w) (hc.mono hclip) (hd.mono (by
      intro t ht
      refine ⟨hclip ⟨⟨ht.1.1.le,ht.1.2.le⟩,⟨ht.2.1.le,ht.2.2.le⟩⟩,?_⟩
      simp only [upperClamp_im] at ht
      exact lt_of_le_of_lt (le_min (le_max_right _ _) (le_max_right _ _)) ht.2.1))
  rw [←add_eq_zero_iff_eq_neg,Complex.wedgeIntegral_add_wedgeIntegral_eq]
  simpa only [upperClamp_re,upperClamp_im,←hhorizontal hzm.2,←hhorizontal hwm.2,
    ←hvertical hzm.1,←hvertical hwm.1] using hcg

/-- The analytic zero extension is identically zero on the connected collar. -/
theorem eqOn_zero_collar_of_zero_below {f : ℂ→ℂ} {a b R : ℝ}
    (hab : a<b) (hR : 0<R) (hc : ContinuousOn f (realCollar a b R))
    (hd : DifferentiableOn ℂ f (realCollar a b R∩{z:ℂ|0<z.im}))
    (hzero : ∀ z∈realCollar a b R,z.im≤0→f z=0) :
    EqOn f 0 (realCollar a b R) := by
  have hopen : IsOpen (realCollar a b R) := isOpen_Ioo.reProdIm isOpen_Ioo
  have hconv : Convex ℝ (realCollar a b R) :=
    ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).inter
      ((convex_halfSpace_im_gt (-R)).inter (convex_halfSpace_im_lt R))
  let z₀ : ℂ := ((a+b)/2:ℝ)+(-R/2:ℝ)*Complex.I
  have hz₀ : z₀∈realCollar a b R := by
    simp only [z₀,realCollar,mem_reProdIm,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,sub_zero,add_zero,Complex.add_im,Complex.mul_im,
      zero_add,mul_one,mem_Ioo]
    constructor <;> constructor <;> linarith
  have hz₀neg : z₀.im<0 := by
    simp only [z₀,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
    linarith
  have hvan : f=ᶠ[𝓝 z₀]0 := by
    have hlow : {z:ℂ|z.im<0}∈𝓝 z₀ :=
      (isOpen_lt continuous_im continuous_const).mem_nhds hz₀neg
    filter_upwards [hopen.mem_nhds hz₀,hlow] with z hz hzneg
    exact hzero z hz hzneg.le
  have han := (differentiableOn_collar_of_zero_below hR hc hd hzero).analyticOnNhd hopen
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconv.isPreconnected hz₀ hvan

/-- Extension by clamping to the boundary.  If the real boundary values are
zero, this is precisely the zero extension to the lower half of the collar. -/
def zeroTraceExtension (f : ℂ→ℂ) : ℂ→ℂ := f ∘upperClamp

theorem continuousOn_zeroTraceExtension {f : ℂ→ℂ} {a b R : ℝ} (hR : 0<R)
    (hc : ContinuousOn f (realCollar a b R∩{z:ℂ|0≤z.im})) :
    ContinuousOn (zeroTraceExtension f) (realCollar a b R) := by
  apply hc.comp continuous_upperClamp.continuousOn
  intro z hz
  exact ⟨upperClamp_mem_collar hR hz,by simp⟩

/-- Schwarz zero-trace uniqueness for the actual upper half collar.
Continuity includes the real boundary, but no holomorphic continuation there
is assumed. -/
theorem eqOn_zero_of_upper_zero_trace {f : ℂ→ℂ} {a b R : ℝ}
    (hab : a<b) (hR : 0<R)
    (hc : ContinuousOn f (realCollar a b R∩{z:ℂ|0≤z.im}))
    (hd : DifferentiableOn ℂ f (realCollar a b R∩{z:ℂ|0<z.im}))
    (hzero : ∀ x∈Ioo a b,f (x:ℂ)=0) :
    EqOn f 0 (realCollar a b R∩{z:ℂ|0≤z.im}) := by
  have hext : EqOn (zeroTraceExtension f) f
      (realCollar a b R∩{z:ℂ|0≤z.im}) := by
    intro z hz
    simp only [zeroTraceExtension,Function.comp_apply,upperClamp_eq_self hz.2]
  have hde : DifferentiableOn ℂ (zeroTraceExtension f)
      (realCollar a b R∩{z:ℂ|0<z.im}) := by
    apply hd.congr
    intro z hz
    exact hext ⟨hz.1,(show 0<z.im from hz.2).le⟩
  have hze : ∀ z∈realCollar a b R,z.im≤0→zeroTraceExtension f z=0 := by
    intro z hz him
    simpa only [zeroTraceExtension,Function.comp_apply,upperClamp,max_eq_right him,
      Complex.ofReal_zero,zero_mul,add_zero] using hzero z.re hz.1
  have heq := eqOn_zero_collar_of_zero_below hab hR
    (continuousOn_zeroTraceExtension hR hc) hde hze
  intro z hz
  exact (hext hz).symm.trans (heq hz.1)

end
end IsoProof
