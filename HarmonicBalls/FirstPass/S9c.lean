import HarmonicBalls.Proofs.Sec9.NumberedResultsAssembly
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec9.DyadicGlobalUniqueness
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences
import HarmonicBalls.Steps.Sec2.VolumeGrowth
import HarmonicBalls.Draft.Section9

/-! # Result 9.2, corrected form [C51]: `firstPass_9_2_corrected`

Proposition 9.2 of "Harmonic balls in Liouville quantum gravity" (Bou-Rabee-Gwynne, arXiv:2208.11795), in the corrected
form [C51] of docs/campaign/CORRECTIONS.md: `SubharmonicBallUniquenessC51Stmt` (section 1). The weak form `SubharmonicBallUniquenessWeakStmt` (Draft/Section9.lean)
gives only `cluster ⊆ A` and `μ(A \ regularizedCluster) = 0`.

Route (the "smallest upgrade of the weak theorem"):
* the weak theorem (`subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales`);
* the all-radii, simultaneous-centre boundary nullity `ClusterBoundaryNullAllRadii` (Steps 1, 2, 6 of the proof, via
  Proposition 8.1 and Lemma 3.5 on dyadic radii: `clusterBoundaryNullAllRadii_of_dyadic_typical_scales`);
* full support of `μ_h` (`lqgMeasureFullSupportStmt_of_volumeGrowth`), used pathwise in the measure-theoretic lemma
  `c51_of_weak_boundary_fullSupport`, which is pure topology and measure theory (Steps 7 and 8).

Hypotheses are exactly those of the weak theorem `firstPass_9_2_corrected` (FirstPass/S2S3S4S9SA.lean): the five staged
LQG Props of Proposed/LQG.lean and the Draft statement `TypicalPointManyGoodScalesStmt` (Lemma 8.2). No new frozen input.
This file does not import FirstPass/S2S3S4S9SA.lean, and its theorem lives in the namespace `HarmonicBalls.S9c`, to avoid
the name clash with the weak theorem. -/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.S9c

universe u

/-- Proposition 9.2, corrected form ([C51], section 1). On one event of probability one, for every `A`, `z`, `t`, `R` with
`0 < t`, `0 < R`, `z ∈ B_R`, `A ⋐ B_R` a subharmonic ball centred at `z` with `μ_h(A) = t`:
the cluster `Λ^{B_R;z}_t` (eq:non-co-set) is contained in `A`, `A` is contained in its regularization
`Λ̂^{B_R;z}_t = int(closure Λ^{B_R;z}_t)` (eq:regular-cluster), `μ_h(A \ Λ^{B_R;z}_t) = 0`,
`μ_h(Λ̂^{B_R;z}_t \ A) = 0`, and `A = Λ̂^{B_R;z}_t` when `A` is regular open (`int(closure A) = A`).
The conull event is fixed before `A`, `z`, `t`, `R`.

The printed strong form `SubharmonicBallUniquenessStmt` is false ([C51]); this is the corrected statement. -/
def SubharmonicBallUniquenessC51Stmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ),
    0 < t → 0 < R → z ∈ ball (0 : ℂ) R →
    closure A ⊆ ball (0 : ℂ) R → IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
    cluster (μ ω) R z t ⊆ A ∧
    A ⊆ regularizedCluster (μ ω) R z t ∧
    μ ω (A \ cluster (μ ω) R z t) = 0 ∧
    μ ω (regularizedCluster (μ ω) R z t \ A) = 0 ∧
    (A = interior (closure A) → A = regularizedCluster (μ ω) R z t)

/-- Pathwise form of the upgrade (section 4). On one realization `μ`, given full
support, the weak conclusion for every subharmonic ball, and the boundary nullity `μ(∂Λ^{B_R;z}_t) = 0` for every cluster
with `closure ⊆ B_R`, the five conclusions of [C51] hold. Only topology and measure theory are used. -/
theorem c51_of_weak_boundary_fullSupport (μ : Measure ℂ)
    (hfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U)
    (hweak : ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R → z ∈ ball (0 : ℂ) R →
      closure A ⊆ ball (0 : ℂ) R → IsSubharmonicBall μ A z → μ A = ENNReal.ofReal t →
      cluster μ R z t ⊆ A ∧ μ (A \ regularizedCluster μ R z t) = 0)
    (hbd : ∀ R t : ℝ, 0 < R → 0 < t → ∀ z ∈ ball (0 : ℂ) R,
      closure (cluster μ R z t) ⊆ ball 0 R → μ (frontier (cluster μ R z t)) = 0)
    (A : Set ℂ) (z : ℂ) (t R : ℝ) (ht : 0 < t) (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R)
    (hA : closure A ⊆ ball (0 : ℂ) R) (hsub : IsSubharmonicBall μ A z) (hmass : μ A = ENNReal.ofReal t) :
    cluster μ R z t ⊆ A ∧ A ⊆ regularizedCluster μ R z t ∧
      μ (A \ cluster μ R z t) = 0 ∧ μ (regularizedCluster μ R z t \ A) = 0 ∧
      (A = interior (closure A) → A = regularizedCluster μ R z t) := by
  obtain ⟨hGA, hAH⟩ := hweak A z t R ht hR hz hA hsub hmass
  -- the regularization lies in the closure of the cluster; the frontier contains the closure minus the cluster
  have hHG : regularizedCluster μ R z t ⊆ closure (cluster μ R z t) := interior_subset
  have hGcl : closure (cluster μ R z t) ⊆ ball 0 R := (closure_mono hGA).trans hA
  have hfr : μ (frontier (cluster μ R z t)) = 0 := hbd R t hR ht z hz hGcl
  have hcl : ∀ x, x ∈ closure (cluster μ R z t) → x ∉ cluster μ R z t →
      x ∈ frontier (cluster μ R z t) := fun x h1 h2 => by
    rw [frontier]
    exact ⟨h1, fun hi => h2 (interior_subset hi)⟩
  -- A lies in the closure of the cluster, by full support of μ and the null difference A \ regularization
  have hU : A \ closure (cluster μ R z t) ⊆ A \ regularizedCluster μ R z t :=
    fun x hx => ⟨hx.1, fun hxH => hx.2 (hHG hxH)⟩
  have hU0 : μ (A \ closure (cluster μ R z t)) = 0 := measure_mono_null hU hAH
  have hA_cl : A ⊆ closure (cluster μ R z t) := by
    by_contra hcon
    obtain ⟨x, hxA, hxG⟩ := Set.not_subset.mp hcon
    have hpos := hfull _ (hsub.1.sdiff isClosed_closure) ⟨x, hxA, hxG⟩
    rw [hU0] at hpos
    exact lt_irrefl _ hpos
  -- A is open, so A lies in the regularization
  have hA_H : A ⊆ regularizedCluster μ R z t := interior_maximal hA_cl hsub.1
  -- A \ cluster ⊆ (A \ regularization) ∪ frontier(cluster)
  have hAG : μ (A \ cluster μ R z t) = 0 := by
    refine measure_mono_null ?_ (measure_union_null hAH hfr)
    intro x hx
    by_cases hxH : x ∈ regularizedCluster μ R z t
    · exact Or.inr (hcl x (hHG hxH) hx.2)
    · exact Or.inl ⟨hx.1, hxH⟩
  -- regularization \ A ⊆ frontier(cluster), since cluster ⊆ A
  have hHA : μ (regularizedCluster μ R z t \ A) = 0 := by
    refine measure_mono_null ?_ hfr
    intro x hx
    exact hcl x (hHG hx.1) (fun hxG => hx.2 (hGA hxG))
  refine ⟨hGA, hA_H, hAG, hHA, fun hreg => ?_⟩
  -- regular open A: the regularization of the cluster lies in int(closure A) = A
  apply Set.Subset.antisymm hA_H
  have hsubcl : regularizedCluster μ R z t ⊆ interior (closure A) :=
    interior_mono (closure_mono hGA)
  intro x hx
  rw [← hreg] at hsubcl
  exact hsubcl hx

/-- **Proposition 9.2**, corrected form ([C51]) — result `firstPass_9_2_corrected`.
Hypotheses: the five staged LQG Props of Proposed/LQG.lean (as in the weak theorem) and the Draft statement
`TypicalPointManyGoodScalesStmt` (Lemma 8.2). The volume-growth input `LQGVolumeGrowthAllScalesStmt` (Draft Section 2) is
derived from the five staged Props, as in the weak theorem. -/
theorem firstPass_9_2_corrected
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    SubharmonicBallUniquenessC51Stmt.{u} := by
  have hI2 : LQGVolumeGrowthAllScalesStmt.{u} :=
    HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs hDG hCC hW hE hN
  have hfull : LQGMeasureFullSupportStmt.{u} := lqgMeasureFullSupportStmt_of_volumeGrowth hI2
  have hweak : SubharmonicBallUniquenessWeakStmt.{u} :=
    subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales hI2 h82
  have hbd : ClusterBoundaryNullAllRadii.{u} :=
    clusterBoundaryNullAllRadii_of_dyadic_typical_scales hI2
      (HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc)
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hweak γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hbd γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hf hw hb
  intro A z t R ht hR hz hA hsub hmass
  exact c51_of_weak_boundary_fullSupport (μ ω) hf hw hb A z t R ht hR hz hA hsub hmass


end HarmonicBalls.S9c
