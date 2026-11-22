import IsoProof.Objects
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Sharp jet transport through an actual analytic change of coordinate

The transport uses the full Faà di Bruno formula and an analytic local inverse.
It does not identify derivatives with respect to s and E.  Terms below the top
jet are finite products of bounded lower jets; the top coefficient has a
nonzero limit at a nonsingular change of coordinate.
-/
namespace IsoProof
noncomputable section
open Complex Filter Set Asymptotics
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem analyticAt_iteratedComplexDeriv {f : ℂ→ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (j : ℕ) : AnalyticAt ℂ (iteratedDeriv j f) z := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

private theorem full_length_partSize {n : ℕ} (c : OrderedFinpartition n)
    (hc : c.length=n) (j : Fin c.length) : c.partSize j=1 := by
  have hsum : ∑ i : Fin c.length,c.partSize i=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr c.equivSigma
  have hsum' : (∑ i : Fin c.length,(1:ℕ))=∑ i : Fin c.length,c.partSize i := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
    exact hc.trans hsum.symm
  exact ((Finset.sum_eq_sum_iff_of_le (fun i _=>c.partSize_pos i)).mp hsum'
    j (Finset.mem_univ j)).symm

/-- The finite number of maximal-length terms in the chain rule.  Its precise
value is not needed: it is positive because the singleton partition occurs. -/
def topCompositionMultiplicity (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun c : OrderedFinpartition n=>c.length=n)).card

private theorem topCompositionMultiplicity_pos (n : ℕ) :
    0<topCompositionMultiplicity n := by
  apply Finset.card_pos.mpr
  exact ⟨OrderedFinpartition.atomic n,by simp⟩

/-- The lower part of Faà di Bruno's formula, with every top-order term
removed. -/
def lowerCompositionTerm (n : ℕ) (f g : ℂ→ℂ) (z : ℂ) : ℂ :=
  ∑ c ∈ Finset.univ.filter (fun c : OrderedFinpartition n=>c.length≠n),
    iteratedDeriv c.length f (g z)*∏ j,iteratedDeriv (c.partSize j) g z

private theorem iteratedDeriv_comp_top_split {f g : ℂ→ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (g z)) (hg : AnalyticAt ℂ g z) (n : ℕ) :
    iteratedDeriv n (f∘g) z=
      ((topCompositionMultiplicity n:ℂ)*(deriv g z)^n)*iteratedDeriv n f (g z)+
        lowerCompositionTerm n f g z := by
  classical
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    (n:=(n:ℕ∞ω)) hf.contDiffAt hg.contDiffAt le_rfl]
  rw [←Finset.sum_filter_add_sum_filter_not _ (fun c : OrderedFinpartition n=>c.length=n)]
  congr 1
  have hterm (c : OrderedFinpartition n) (hc : c∈Finset.univ.filter (fun c=>c.length=n)) :
      iteratedDeriv c.length f (g z)*∏ j,iteratedDeriv (c.partSize j) g z =
      iteratedDeriv n f (g z)*(deriv g z)^n := by
    have hcl := (Finset.mem_filter.mp hc).2
    have hp : (∏ j,iteratedDeriv (c.partSize j) g z)=(deriv g z)^n := by
      simp only [full_length_partSize c hcl,iteratedDeriv_one,
        Finset.prod_const,Finset.card_univ,Fintype.card_fin,hcl]
    rw [hp,hcl]
  rw [Finset.sum_congr rfl hterm,Finset.sum_const]
  simp only [topCompositionMultiplicity,nsmul_eq_mul]
  ring

private theorem coordinate_jet_factor_tendsto {α : Type*} {l : Filter α}
    {p : α→ℂ} {z : ℂ} {g : ℂ→ℂ} (hp : Tendsto p l (𝓝 z))
    (hg : AnalyticAt ℂ g z) {n : ℕ} (c : OrderedFinpartition n) :
    Tendsto (fun t=>∏ j,iteratedDeriv (c.partSize j) g (p t)) l
      (𝓝 (∏ j,iteratedDeriv (c.partSize j) g z)) := by
  exact tendsto_finsetProd _ (fun j _=>(analyticAt_iteratedComplexDeriv hg
    (c.partSize j)).continuousAt.tendsto.comp hp)

private theorem lowerCompositionTerm_isBigO {α : Type*} {l : Filter α}
    {p : α→ℂ} {z : ℂ} {f g : ℂ→ℂ} (hp : Tendsto p l (𝓝 z))
    (hg : AnalyticAt ℂ g z) (n : ℕ)
    (hb : ∀ j<n,(fun t=>iteratedDeriv j f (g (p t)))=O[l](fun _=> (1:ℂ))) :
    (fun t=>lowerCompositionTerm n f g (p t))=O[l](fun _=>(1:ℂ)) := by
  classical
  have hsum := Asymptotics.IsBigO.sum
    (s:=Finset.univ.filter (fun c : OrderedFinpartition n=>c.length≠n))
    (A:=fun c t=>iteratedDeriv c.length f (g (p t))*
      ∏ j,iteratedDeriv (c.partSize j) g (p t)) (g:=fun _=>(1:ℂ)) (by
      intro c hc
      have hcl : c.length<n := lt_of_le_of_ne c.length_le (Finset.mem_filter.mp hc).2
      simpa only [one_mul] using (hb c.length hcl).mul
        ((coordinate_jet_factor_tendsto hp hg c).isBigO_one ℂ))
  simpa only [Finset.sum_fn,lowerCompositionTerm] using hsum

/-- Bounded lower jets are preserved by composition with a coordinate map
which is analytic at the endpoint of the path. -/
theorem lower_jets_comp_isBigO {α : Type*} {l : Filter α}
    {p : α→ℂ} {z : ℂ} {f g : ℂ→ℂ} (hp : Tendsto p l (𝓝 z))
    (hg : AnalyticAt ℂ g z) (k : ℕ)
    (hf : ∀ᶠ t in l,AnalyticAt ℂ f (g (p t)))
    (hb : ∀ j<k,(fun t=>iteratedDeriv j f (g (p t)))=O[l](fun _=>(1:ℂ))) :
    ∀ j<k,(fun t=>iteratedDeriv j (f∘g) (p t))=O[l](fun _=>(1:ℂ)) := by
  intro j hj
  have he : (fun t=>iteratedDeriv j (f∘g) (p t))=ᶠ[l]
      (fun t=>∑ c : OrderedFinpartition j,
        iteratedDeriv c.length f (g (p t))*∏ i,iteratedDeriv (c.partSize i) g (p t)) := by
    filter_upwards [hf,hp.eventually hg.eventually_analyticAt] with t hft hgt
    exact iteratedDeriv_comp_eq_sum_orderedFinpartition
      (n:=(j:ℕ∞ω)) hft.contDiffAt hgt.contDiffAt le_rfl
  apply Asymptotics.IsBigO.congr' ?_ he.symm Filter.EventuallyEq.rfl
  have hsum := Asymptotics.IsBigO.sum (s:=Finset.univ)
    (A:=fun (c : OrderedFinpartition j) t=>iteratedDeriv c.length f (g (p t))*
      ∏ i,iteratedDeriv (c.partSize i) g (p t)) (g:=fun _=>(1:ℂ)) (by
      intro c _
      simpa only [one_mul] using (hb c.length (c.length_le.trans_lt hj)).mul
        ((coordinate_jet_factor_tendsto hp hg c).isBigO_one ℂ))
  simpa only [Finset.sum_fn] using hsum

/-- A nonzero limiting scalar times a divergent jet still dominates every
bounded remainder. -/
theorem norm_tendsto_atTop_mul_add_bounded {α : Type*} {l : Filter α}
    {A H B : α→ℂ} {a : ℂ} (ha : a≠0) (hA : Tendsto A l (𝓝 a))
    (hH : Tendsto (fun t=>‖H t‖) l atTop)
    (hB : B=O[l](fun _=>(1:ℂ))) :
    Tendsto (fun t=>‖A t*H t+B t‖) l atTop := by
  have hprod : Tendsto (fun t=>‖A t*H t‖) l atTop := by
    simpa only [norm_mul] using hA.norm.pos_mul_atTop (norm_pos_iff.mpr ha) hH
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp hB
  simp only [norm_one,mul_one] at hC
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [hprod.eventually_ge_atTop (M+C),hC] with t ht hBt
  have htri := norm_add_le (A t*H t+B t) (-B t)
  simp only [add_neg_cancel_right,norm_neg] at htri
  linarith

/-- The first unbounded derivative and every lower bounded jet are invariant
under an analytic change of coordinate with nonzero derivative. -/
theorem sharp_jets_comp {α : Type*} {l : Filter α}
    {p : α→ℂ} {z : ℂ} {f g : ℂ→ℂ} (hp : Tendsto p l (𝓝 z))
    (hg : AnalyticAt ℂ g z) (hg' : deriv g z≠0) (k : ℕ)
    (hf : ∀ᶠ t in l,AnalyticAt ℂ f (g (p t)))
    (htop : Tendsto (fun t=>‖iteratedDeriv k f (g (p t))‖) l atTop)
    (hb : ∀ j<k,(fun t=>iteratedDeriv j f (g (p t)))=O[l](fun _=>(1:ℂ))) :
    Tendsto (fun t=>‖iteratedDeriv k (f∘g) (p t)‖) l atTop ∧
      ∀ j<k,(fun t=>iteratedDeriv j (f∘g) (p t))=O[l](fun _=>(1:ℂ)) := by
  refine ⟨?_,lower_jets_comp_isBigO hp hg k hf hb⟩
  have hcoef0 : (topCompositionMultiplicity k:ℂ)*(deriv g z)^k≠0 :=
    mul_ne_zero (by exact_mod_cast (topCompositionMultiplicity_pos k).ne')
      (pow_ne_zero k hg')
  have hcoef : Tendsto (fun t=>(topCompositionMultiplicity k:ℂ)*(deriv g (p t))^k) l
      (𝓝 ((topCompositionMultiplicity k:ℂ)*(deriv g z)^k)) := by
    simpa only [iteratedDeriv_one,Function.comp_apply] using
      (((analyticAt_iteratedComplexDeriv hg 1).continuousAt.tendsto.comp hp).pow k).const_mul
        (topCompositionMultiplicity k:ℂ)
  have hlim := norm_tendsto_atTop_mul_add_bounded hcoef0 hcoef htop
    (lowerCompositionTerm_isBigO hp hg k hb)
  apply hlim.congr'
  filter_upwards [hf,hp.eventually hg.eventually_analyticAt] with t hft hgt
  exact congrArg norm (iteratedDeriv_comp_top_split hft hgt k).symm

/-- Explicit finite trace formula for a composition.  J j denotes a continuous
extension of the j-th outer jet evaluated along the coordinate map. -/
def compositionJetTrace (n : ℕ) (J : ℕ→ℂ→ℂ) (g : ℂ→ℂ) (z : ℂ) : ℂ :=
  ∑ c : OrderedFinpartition n,J c.length z*∏ j,iteratedDeriv (c.partSize j) g z

theorem continuousOn_compositionJetTrace (n : ℕ) (J : ℕ→ℂ→ℂ) (g : ℂ→ℂ)
    {U : Set ℂ} (hJ : ∀ j≤n,ContinuousOn (J j) U)
    (hg : AnalyticOnNhd ℂ g U) : ContinuousOn (compositionJetTrace n J g) U := by
  apply continuousOn_finsetSum
  intro c _
  apply (hJ c.length c.length_le).mul
  apply continuousOn_finsetProd
  intro j _ z hz
  exact (analyticAt_iteratedComplexDeriv (hg z hz) (c.partSize j)).continuousAt.continuousWithinAt

theorem compositionJetTrace_eq_iteratedDeriv (n : ℕ) (J : ℕ→ℂ→ℂ)
    {f g : ℂ→ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (g z)) (hg : AnalyticAt ℂ g z)
    (hJ : ∀ j≤n,J j z=iteratedDeriv j f (g z)) :
    compositionJetTrace n J g z=iteratedDeriv n (f∘g) z := by
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    (n:=(n:ℕ∞ω)) hf.contDiffAt hg.contDiffAt le_rfl]
  apply Finset.sum_congr rfl
  intro c _
  rw [hJ c.length c.length_le]

/-- The bounded remainder in Leibniz's rule, excluding the top source jet. -/
def lowerProductTerm (n : ℕ) (f A : ℂ→ℂ) (z : ℂ) : ℂ :=
  ∑ i∈Finset.range n,(n.choose i:ℂ)*iteratedDeriv i f z*iteratedDeriv (n-i) A z

private theorem iteratedDeriv_mul_top_split {f A : ℂ→ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hA : AnalyticAt ℂ A z) (n : ℕ) :
    iteratedDeriv n (f*A) z=A z*iteratedDeriv n f z+lowerProductTerm n f A z := by
  rw [iteratedDeriv_mul hf.contDiffAt hA.contDiffAt,Finset.sum_range_succ]
  simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,iteratedDeriv_zero]
  dsimp only [lowerProductTerm]
  ring

private theorem lowerProductTerm_isBigO {α : Type*} {l : Filter α}
    {p : α→ℂ} {z : ℂ} {f A : ℂ→ℂ} (hp : Tendsto p l (𝓝 z))
    (hA : AnalyticAt ℂ A z) (n : ℕ)
    (hb : ∀ j<n,(fun t=>iteratedDeriv j f (p t))=O[l](fun _=>(1:ℂ))) :
    (fun t=>lowerProductTerm n f A (p t))=O[l](fun _=>(1:ℂ)) := by
  have hs := Asymptotics.IsBigO.sum (s:=Finset.range n)
    (A:=fun i t=>(n.choose i:ℂ)*iteratedDeriv i f (p t)*iteratedDeriv (n-i) A (p t))
    (g:=fun _=>(1:ℂ)) (by
      intro i hi
      have hAi := ((analyticAt_iteratedComplexDeriv hA (n-i)).continuousAt.tendsto.comp hp).isBigO_one ℂ
      simpa only [one_mul,Function.comp_apply] using ((hb i (Finset.mem_range.mp hi)).const_mul_left
        (n.choose i:ℂ)).mul hAi)
  simpa only [lowerProductTerm,Finset.sum_fn] using hs

/-- Multiplication by an analytic nonvanishing physical prefactor preserves
the exact first divergent derivative and all bounded lower derivatives. -/
theorem sharp_jets_mul {α : Type*} {l : Filter α}
    {p : α→ℂ} {z : ℂ} {f A : ℂ→ℂ} (hp : Tendsto p l (𝓝 z))
    (hA : AnalyticAt ℂ A z) (hA0 : A z≠0) (k : ℕ)
    (hf : ∀ᶠ t in l,AnalyticAt ℂ f (p t))
    (htop : Tendsto (fun t=>‖iteratedDeriv k f (p t)‖) l atTop)
    (hb : ∀ j<k,(fun t=>iteratedDeriv j f (p t))=O[l](fun _=>(1:ℂ))) :
    Tendsto (fun t=>‖iteratedDeriv k (f*A) (p t)‖) l atTop ∧
      ∀ j<k,(fun t=>iteratedDeriv j (f*A) (p t))=O[l](fun _=>(1:ℂ)) := by
  have hsplit (j : ℕ) : (fun t=>iteratedDeriv j (f*A) (p t))=ᶠ[l]
      (fun t=>A (p t)*iteratedDeriv j f (p t)+lowerProductTerm j f A (p t)) := by
    filter_upwards [hf,hp.eventually hA.eventually_analyticAt] with t hft hAt
    exact iteratedDeriv_mul_top_split hft hAt j
  constructor
  · have hlim := norm_tendsto_atTop_mul_add_bounded hA0
      (hA.continuousAt.tendsto.comp hp) htop (lowerProductTerm_isBigO hp hA k hb)
    exact hlim.congr' ((hsplit k).symm.fun_comp norm)
  · intro j hj
    have hm : (fun t=>A (p t)*iteratedDeriv j f (p t))=O[l](fun _=>(1:ℂ)) := by
      simpa only [one_mul,Function.comp_apply] using ((hA.continuousAt.tendsto.comp hp).isBigO_one ℂ).mul (hb j hj)
    exact (hm.add (lowerProductTerm_isBigO hp hA j (fun i hi=>hb i (hi.trans hj)))).congr' (hsplit j).symm Filter.EventuallyEq.rfl

/-- The physical energy coordinate is analytic away from s=0. -/
theorem energy_analyticAt {s : ℂ} (hs : s≠0) : AnalyticAt ℂ energy s :=
  analyticAt_id.add (analyticAt_id.inv hs)

theorem energy_hasDerivAt {s : ℂ} (hs : s≠0) :
    HasDerivAt energy (1-(s^2)⁻¹) s := by
  simpa only [energy,sub_eq_add_neg,Pi.add_apply,id_eq] using!
    (hasDerivAt_id s).add (hasDerivAt_inv hs)

/-- The only finite critical points of s+s⁻¹ are the two axes s=±1. -/
theorem energy_deriv_ne_zero {s : ℂ} (hs0 : s≠0) (hs1 : s≠1) (hsm1 : s≠ -1) :
    deriv energy s≠0 := by
  rw [(energy_hasDerivAt hs0).deriv]
  intro h
  have hinv : (s^2)⁻¹=1 := (sub_eq_zero.mp h).symm
  have hsq : s^2=1 := by simpa only [inv_inv,inv_one] using congrArg Inv.inv hinv
  have hmul : (s-1)*(s+1)=0 := by linear_combination hsq
  rcases mul_eq_zero.mp hmul with h | h
  · exact hs1 (sub_eq_zero.mp h)
  · exact hsm1 (eq_neg_of_add_eq_zero_left h)

/-- Analyticity of a genuine E-function can be produced from its actual
s-composition, using the noncritical energy coordinate. -/
theorem analyticAt_energyFunction_of_composition {F : ℂ→ℂ} {s : ℂ}
    (hs0 : s≠0) (hs1 : s≠1) (hsm1 : s≠ -1)
    (hF : AnalyticAt ℂ (F∘energy) s) : AnalyticAt ℂ F (energy s) :=
  (analyticAt_comp_iff_of_deriv_ne_zero (energy_analyticAt hs0)
    (energy_deriv_ne_zero hs0 hs1 hsm1)).mp hF

end
end IsoProof
