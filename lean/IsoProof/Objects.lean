import IsingBulk.HT22.Physical.Angular
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.RingTheory.MvPolynomial.Basic

/-! Shared literal objects for the five-page isotropic manuscript.  Definitions
are owned by the integration agent.  No analytic estimate or terminal claim is
an input field here. -/
namespace IsoProof
noncomputable section
open scoped BigOperators Topology
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour

inductive Phase where
  | high
  | low
  deriving DecidableEq, Repr

inductive Sign where
  | positive
  | negative
  deriving DecidableEq, Repr

def signValue : Sign → ℂ
  | .positive => 1
  | .negative => -1

def signAngle : Sign → ℝ
  | .positive => 0
  | .negative => Real.pi

def particleOrder : Phase → ℕ → ℕ
  | .high, n => 2*n+1
  | .low, n => 2*(n+1)

def energy (s : ℂ) : ℂ := s + s⁻¹

def seriesCoordinate (E : ℂ) : ℂ := (2*E)⁻¹

def physicalDomain : Phase → Set ℂ
  | .high => {s | ‖s‖ < 1}
  | .low => {s | 1 < ‖s‖}

def realTemperatureDomain : Phase → Set ℝ
  | .high => Set.Ioo 0 1
  | .low => Set.Ioi 1

def energyDomain : Set ℂ := {E | E.im ≠ 0 ∨ 2 < |E.re|}

def angleRoot (E : ℂ) (q : ℝ) : ℂ :=
  IsingBulk.Preferred22.physicalRoot (E - (Real.cos q : ℂ))

def anglePoint (q : ℝ) : ℂ := limitingAngle q

def pairProduct {N : ℕ} (E : ℂ) (q : Fin N → ℝ) : ℂ :=
  canceledPairProduct (fun i => angleRoot E (q i)) (fun i => anglePoint (q i))

def siteCoefficient (N A : ℕ) (B : ℤ) (E : ℂ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^N *
    multiAngleIntegral N (fun q =>
      pairProduct E q *
      (∏ i, (angleRoot E (q i))^A * (anglePoint (q i))^B *
        IsingBulk.HT22.Physical.oneBody (angleRoot E (q i))))

def constrainedAngles (σ : Sign) (n : ℕ) (q : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.snoc (α := fun _ : Fin (n+1) => ℝ) q (signAngle σ - ∑ i, q i)

def particleDensity (σ : Sign) {N : ℕ} (E : ℂ) (q : Fin N → ℝ) : ℂ :=
  let Z := ∏ i, angleRoot E (q i)
  ((1+signValue σ*Z)/(1-signValue σ*Z)) * pairProduct E q *
    ∏ i, IsingBulk.HT22.Physical.oneBody (angleRoot E (q i))

def particleCoefficient (σ : Sign) (N : ℕ) (E : ℂ) : ℂ :=
  if N = 0 then 0 else
    (N.factorial : ℂ)⁻¹ * ((2*(Real.pi : ℂ))⁻¹)^(N-1) *
      multiAngleIntegral (N-1) (fun q => particleDensity σ E (constrainedAngles σ (N-1) q))

def fullEnergySum (ν : Phase) (σ : Sign) (E : ℂ) : ℂ :=
  ∑' n : ℕ, particleCoefficient σ (particleOrder ν n) E

def energyTail (ν : Phase) (σ : Sign) (cutoff : ℕ) (E : ℂ) : ℂ :=
  ∑' n : ℕ, if cutoff < particleOrder ν n then
    particleCoefficient σ (particleOrder ν n) E else 0

def normalization : Phase → ℂ → ℂ
  | .high, s => Complex.cpow (1-s^4) (1/4 : ℂ) / s
  | .low, s => Complex.cpow (1-s⁻¹^4) (1/4 : ℂ)

def reducedSusceptibility (ν : Phase) (s : ℂ) : ℂ :=
  if ν = .high ∧ s = 0 then 1 else
    normalization ν s * fullEnergySum ν .positive (energy s)

abbrev complexJet (j : ℕ) (f : ℂ → ℂ) : ℂ → ℂ := iteratedDeriv j f

def GermEqAt (z : ℂ) (f g : ℂ → ℂ) : Prop := f =ᶠ[nhds z] g

def LocalExtension (D : Set ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g U ∧ Set.EqOn f g (U ∩ D)

def NaturalBoundary (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ¬ LocalExtension D f z

/-- The upper-side jet trace at a real cut point; continuity at the boundary
is expressed using the actual derivatives, not independent formal variables. -/
def UpperJetTrace (f : ℂ → ℂ) (j : ℕ) (x : ℝ) (b : ℂ) : Prop :=
  Filter.Tendsto (complexJet j f)
    (nhdsWithin (x : ℂ) {E : ℂ | 0 < E.im}) (nhds b)

end
end IsoProof
