import IsoProof.EnergyJetAssembly
import IsoProof.ResonanceFiniteExtension

/-! Unconditional construction for the actual full energy sums. The finite
part is continued by the constrained common-contour theorem, the infinite
part by the proved site bounds and exact square-shell summation. -/
namespace IsoProof
noncomputable section

/-- Every finite jet order of either full susceptibility has a genuine
nondegenerate upper boundary interval with continuous actual jet traces. -/
theorem regularEnergyJetInterval (ν : Phase) (n : ℕ) :
    Nonempty (RegularEnergyJetInterval ν n) := by
  apply regularEnergyJetInterval_of_finite_extensions ν n
  intro a b ha hab hb
  exact finite_particleCoefficient_extensions_in_interval .positive (2*n+4) ha hab hb

end
end IsoProof
