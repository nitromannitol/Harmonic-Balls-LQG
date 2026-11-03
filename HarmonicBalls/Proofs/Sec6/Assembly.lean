import HarmonicBalls.Proofs.Sec6.HarnackType
import HarmonicBalls.Proofs.Sec6.Prevalence
import HarmonicBalls.Proofs.Sec6.HarnackIteration
import HarmonicBalls.Proofs.Sec6.GreenMono
import HarmonicBalls.Draft.Section3

/-!
# Section 6 assembly

* `clusterComponentInnerBallStep_of_clusterOpen`: the step `ClusterComponentInnerBallStep` (line 1877) from Lemma 3.2
  (`ClusterOpenLaplacianStmt`: `Λ^z_t` is open and connected). A component `Λ̃` of `Λ^z_t ∩ B_ρ(x₀)` missing
  `𝔸_{ρ/2,d}(x₀)` and meeting `closure B_{ρ/2}(x₀)` lies in `closure B_{ρ/2}(x₀)` (it is connected); it is then open
  (a component of an open set) and relatively closed in `Λ^z_t` (every point of `Λ^z_t` in its closure has an open
  component meeting it), so by connectedness `Λ^z_t ⊆ Λ̃`, against `z ∈ Λ^z_t \ closure B_ρ(x₀)`. This replaces the
  printed maximum-principle argument.
* `veryGoodAnnulusHarnackTypeStmt_of_sec3`: Lemma 6.11 from Lemmas 3.2, 6.8, 6.10, 6.13.
* `harnackTypeComponentStmt_of_inputs`, `harnackTypeEstimateStmt_of_inputs`: Propositions 6.2 and 6.1 from
  step S-SubRange for very good annuli, `LQGMeasureExistence` and `LQGMeasureWeylScaling` (α₀ = 0), Lemmas 3.2, 6.8,
  6.10 and 6.13.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

open Section6

universe u

namespace Section6

/-- A component of `L ∩ B_ρ(x₀)` (`L` open and preconnected, `z ∈ L \ closure B_ρ(x₀)`) missing `𝔸_{ρ/2,d}(x₀)` misses
`closure B_{ρ/2}(x₀)`. -/
theorem component_inter_closedBall_eq_empty {L : Set ℂ} {z x₀ : ℂ} {ρ d : ℝ} (hopen : IsOpen L)
    (hconn : IsPreconnected L) (hzL : z ∈ L) (hzB : z ∉ closedBall x₀ ρ) {Λ : Set ℂ}
    (hΛ : Λ ∈ connectedComponentsIn (L ∩ ball x₀ ρ)) (hd : d ∈ Ioo (ρ / 2) ρ)
    (hempty : Λ ∩ annulus x₀ (ρ / 2) d = ∅) : Λ ∩ closedBall x₀ (ρ / 2) = ∅ := by
  obtain ⟨y, -, rfl⟩ := hΛ
  set F := L ∩ ball x₀ ρ with hF
  set C := connectedComponentIn F y with hCdef
  by_contra hne
  obtain ⟨x, hxC, hxB⟩ := nonempty_iff_ne_empty.2 hne
  have hFo : IsOpen F := hopen.inter isOpen_ball
  have hCo : IsOpen C := hFo.connectedComponentIn
  have hCsub : C ⊆ F := connectedComponentIn_subset F y
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hnotA : ∀ w ∈ C, w ∉ annulus x₀ (ρ / 2) d := fun w hw hwA =>
    (eq_empty_iff_forall_notMem.1 hempty) w ⟨hw, hwA⟩
  set m := (ρ / 2 + d) / 2 with hm
  have hm1 : ρ / 2 < m := by rw [hm]; linarith [hd.1]
  have hm2 : m < d := by rw [hm]; linarith [hd.1]
  have hCm : C ⊆ closedBall x₀ (ρ / 2) := by
    have hsplit : C ⊆ ball x₀ m ∪ (closedBall x₀ m)ᶜ := by
      intro w hw
      by_cases h : dist w x₀ < m
      · exact Or.inl h
      · refine Or.inr fun hc => hnotA w hw ⟨mem_ball.2 ?_, fun hc' => ?_⟩
        · have := mem_closedBall.1 hc; linarith
        · have := mem_closedBall.1 hc'; linarith
    have hleft := IsPreconnected.subset_left_of_subset_union isOpen_ball isClosed_closedBall.isOpen_compl
      (disjoint_compl_right_iff_subset.2 ball_subset_closedBall) hsplit
      ⟨x, hxC, mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hxB) hm1)⟩ hCpre
    intro w hw
    have h1 := mem_ball.1 (hleft hw)
    by_contra h2
    exact hnotA w hw ⟨mem_ball.2 (by linarith), h2⟩
  have hclC : closure C ⊆ closedBall x₀ (ρ / 2) := closure_minimal hCm isClosed_closedBall
  have hCL : L ⊆ C ∪ (closure C)ᶜ := by
    intro w hwL
    by_cases hw : w ∈ closure C
    · left
      have hwB : w ∈ ball x₀ ρ := mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 (hclC hw)) (by linarith [hd.1, hd.2]))
      have hwF : w ∈ F := ⟨hwL, hwB⟩
      obtain ⟨v, hvW, hvC⟩ := mem_closure_iff.1 hw _ hFo.connectedComponentIn (mem_connectedComponentIn hwF)
      have e1 : connectedComponentIn F w = connectedComponentIn F v := connectedComponentIn_eq hvW
      have e2 : connectedComponentIn F y = connectedComponentIn F v := connectedComponentIn_eq hvC
      rw [hCdef, e2, ← e1]
      exact mem_connectedComponentIn hwF
    · exact Or.inr hw
  have hLC := IsPreconnected.subset_left_of_subset_union hCo isClosed_closure.isOpen_compl
    (disjoint_compl_right_iff_subset.2 subset_closure) hCL ⟨x, (hCsub hxC).1, hxC⟩ hconn
  exact hzB (closedBall_subset_closedBall (by linarith [hd.1, hd.2]) (hCm (hLC hzL)))

end Section6

/-- `ClusterComponentInnerBallStep` from Lemma 3.2 (`Λ^z_t` open and connected). -/
theorem clusterComponentInnerBallStep_of_clusterOpen (h32 : ClusterOpenLaplacianStmt.{u}) :
    ClusterComponentInnerBallStep.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω
  intro z hz t ht ρ _ x₀ hball Λ hΛ d hd hempty
  obtain ⟨hopen, hconn, -⟩ := hω t 1 ht one_pos z hz
  exact component_inter_closedBall_eq_empty hopen hconn.isPreconnected ⟨hz, Or.inl rfl⟩
    (fun h => (hball h).2 rfl) hΛ hd hempty

/-- **Lemma 6.11** from Lemmas 3.2, 6.8, 6.10 and 6.13 (and the proved Lemma 6.12 and domain monotonicity). -/
theorem veryGoodAnnulusHarnackTypeStmt_of_sec3 (h32 : ClusterOpenLaplacianStmt.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u}) (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (h613 : LowMassSmallOdometerStmt.{u}) : VeryGoodAnnulusHarnackTypeStmt.{u} :=
  veryGoodAnnulusHarnackTypeStmt_of_lemmas h68 h610 h613 (clusterComponentInnerBallStep_of_clusterOpen h32)
    greenPotentialSupMonoStep_proved

/-- **Proposition 6.2** from step S-SubRange (very good annuli, α₀ = 0), the staged inputs `LQGMeasureExistence`
and `LQGMeasureWeylScaling` (α₀ = 0), and Lemmas 3.2, 6.8, 6.10, 6.13. -/
theorem harnackTypeComponentStmt_of_inputs (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (h32 : ClusterOpenLaplacianStmt.{u}) (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u}) (h613 : LowMassSmallOdometerStmt.{u}) :
    HarnackTypeComponentStmt.{u} :=
  harnackTypeComponentStmt_of_lemmas (manyVeryGoodAnnuliStmt_of_literature hsub hex hW)
    (veryGoodAnnulusHarnackTypeStmt_of_sec3 h32 h68 h610 h613)

/-- **Proposition 6.1** from the same inputs. -/
theorem harnackTypeEstimateStmt_of_inputs (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (h32 : ClusterOpenLaplacianStmt.{u}) (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u}) (h613 : LowMassSmallOdometerStmt.{u}) :
    HarnackTypeEstimateStmt.{u} :=
  harnackTypeEstimateStmt_of_component (harnackTypeComponentStmt_of_inputs hsub hex hW h32 h68 h610 h613)

end HarmonicBalls
