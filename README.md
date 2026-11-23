# Square-lattice Ising susceptibility

Two self-contained papers on the full zero-field susceptibility of the square-lattice Ising model.

## Natural boundary and differential transcendence of the isotropic square-lattice Ising susceptibility

For equal couplings, the unit circle in the complex temperature variable `s = sinh(2βJ)` is a natural boundary for the full susceptibility in both the high- and low-temperature phases. The paper also proves differential transcendence in each phase.

[PDF](isotropic-susceptibility.pdf) · [TeX source](isotropic-susceptibility.tex) · [Lean theorems](lean/IsoProof/Final.lean)

## Boundary jets of the anisotropic square-lattice Ising susceptibility

The paper identifies the boundaries of holomorphy in two complex coupling variables and proves natural boundaries and differential transcendence along every fixed positive coupling ratio. It also gives sharp estimates for boundary derivatives.

[PDF](anisotropic-susceptibility-boundary-jets.pdf) · [TeX source](anisotropic-susceptibility-boundary-jets.tex)

The [manuscript archive](archive/before-2026-11-24/) contains the 5-page isotropic paper and the 39-page anisotropic paper that preceded the 24 November 2026 revision, in PDF and TeX.

## Lean formalization of the isotropic paper

The formalization proves the main theorems for the reduced and physical susceptibilities in both phases, as well as differential transcendence of the normalized series at the origin. At first resonance it uses full-series asymptotics at prime particle orders in the high-temperature phase and twice-prime orders in the low-temperature phase. These points form a dense family on the relevant boundary arcs. The identification with the physical susceptibility uses the real-temperature site expansions and the magnetic-field response identity. [Main theorems](lean/IsoProof/Final.lean) · [Physical inputs](lean/IsoProof/PhysicalIdentification.lean)

The project pins Lean 4.34.1 and its mathlib revision. From the repository root, run the following commands with Elan installed.

```sh
cd lean
lake exe cache get
lake build
lake env lean IsoProofAudit.lean
lake env leanchecker --fresh --verbose IsoProof
lake env leanchecker --fresh --verbose IsoProofAudit
```

The project includes the [reused Lean sources](https://github.com/LeoLam233/ising-bulk-natural-boundary/tree/fd0fd6ebe8b82a00184735ad06c0db483923c244/lean) from the earlier collection and their [license notices](third-party/ising-bulk-natural-boundary/).

## Authorship and AI contributions

**Dehao Lin** · School of Physics, Sun Yat-sen University · [ORCID 0009-0001-4551-8490](https://orcid.org/0009-0001-4551-8490)

The repository maintainer directed the project, set the scope of the two papers, and proposed using insights from each proof to simplify the others. OpenAI Codex contributed to developing and simplifying the mathematical arguments, drafting and revising the manuscripts, checking formulas and references, and preparing the TeX and PDF files.

## Related papers

An [earlier collection of eight papers](https://github.com/LeoLam233/ising-bulk-natural-boundary) treats natural boundaries in four settings: low temperature, high temperature, fixed anisotropy, and two independent complex couplings. It gives two proofs for each setting.
