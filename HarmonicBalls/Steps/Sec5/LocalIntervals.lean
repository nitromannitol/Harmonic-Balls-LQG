import HarmonicBalls.Steps.Sec5.Existence
import HarmonicBalls.Steps.Sec5.StrongCompatibility
import HarmonicBalls.Proofs.Sec5.RegularizedSubharmonic
import HarmonicBalls.Proofs.Sec5.AllScaleCompatibility

/-!
# Construction from cofinal local regularized clusters

Once local Proposition 5.4 estimates have been transferred to sufficiently
large ambient balls with cofinal time horizons, cluster compatibility and
the subharmonic-ball property provide the remaining gluing hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- The scale-transfer and cofinal-exit-time part of the proof of Theorem
5.5. The radius sequence need not be monotone. -/
def CofinalRegularizedClusterIntervalsStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z : ℂ, ∃ (R T : ℕ → ℝ),
      (∀ n, 0 < R n ∧ z ∈ ball 0 (R n) ∧ 0 < T n ∧
        SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) (R n) z) z (T n) ∧
        ∀ t ∈ Ioo 0 (T n), closure (cluster (μ ω) (R n) z t) ⊆ ball 0 (R n) ∧
          μ ω (frontier (cluster (μ ω) (R n) z t)) = 0) ∧
      (∀ t : ℝ, 0 < t → ∃ n, t < T n)

/-- Cofinal local intervals, cluster compatibility and the subharmonic-ball
statement supply the complete local construction used in Theorem 5.5. -/
theorem localRegularizedClusterFamilies_of_steps
    (hlocal : CofinalRegularizedClusterIntervalsStep.{u}) (h35 : ClusterCompatibilityStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h43 : ClusterSubharmonicBallStmt.{u}) :
    LocalRegularizedClusterFamiliesStep.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hlocal γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterCompatibilityAllRadii_of_steps h35 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h43 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hlocalω hcompat hopen hsub
  intro z
  obtain ⟨R, T, hloc, hcover⟩ := hlocalω z
  let Λ : ℕ → ℝ → Set ℂ := fun n => regularizedCluster (μ ω) (R n) z
  have hopen' : ∀ n t, 0 < t → IsOpen (cluster (μ ω) (R n) z t) :=
    fun n t ht => (hopen t (R n) ht (hloc n).1 z (hloc n).2.1).1
  refine ⟨T, Λ, ?_, hcover, ?_, ?_, ?_⟩
  · intro m n t ht htm htn
    have hm := (hloc m).2.2.2.2 t ⟨ht, htm⟩
    have hn := (hloc n).2.2.2.2 t ⟨ht, htn⟩
    have heq : cluster (μ ω) (R m) z t = cluster (μ ω) (R n) z t := by
      by_cases hmn : R m ≤ R n
      · exact (hcompat t ht (R m) z (hloc m).2.1 (R m) le_rfl hm.1 (R n) hmn).symm
      · have hnm : R n ≤ R m := le_of_not_ge hmn
        exact hcompat t ht (R n) z (hloc n).2.1 (R n) le_rfl hn.1 (R m) hnm
    change interior (closure (cluster (μ ω) (R m) z t)) =
      interior (closure (cluster (μ ω) (R n) z t))
    rw [heq]
  · intro n
    exact (hloc n).2.2.2.1
  · intro n t ht
    have hnt := (hloc n).2.2.2.2 t ht
    exact isSubharmonicBall_regularizedCluster
      (hsub (R n) t (hloc n).1 ht.1 z (hloc n).2.1 hnt.1 hnt.2) hnt.2
  · intro n t ht s hs hcl r hsr
    have hnt := (hloc n).2.2.2.2 t ht
    have hzS : z ∈ ball (0 : ℂ) s := hcl (subset_closure ((hloc n).2.2.2.1.mem t ht))
    have hclosure := closure_regularizedCluster_eq_of_isOpen (hopen' n t ht.1)
    have heq : cluster (μ ω) r z t = cluster (μ ω) (R n) z t := by
      by_cases hsR : s ≤ R n
      · apply hcompat t ht.1 s z hzS (R n) hsR
        · simpa only [← hclosure] using hcl
        · exact hsr
      · have hRs : R n ≤ s := le_of_not_ge hsR
        exact hcompat t ht.1 (R n) z (hloc n).2.1 (R n) le_rfl hnt.1 r (hRs.trans hsr)
    change interior (closure (cluster (μ ω) (R n) z t)) = interior (closure (cluster (μ ω) r z t))
    rw [heq]

/-- Theorem 5.5 from cofinal local intervals and the Section 3–4 cluster
properties. -/
theorem existenceHarmonicBalls_of_cofinalIntervals
    (hlocal : CofinalRegularizedClusterIntervalsStep.{u}) (h35 : ClusterCompatibilityStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h43 : ClusterSubharmonicBallStmt.{u}) :
    ExistenceHarmonicBallsStmt.{u} :=
  existenceHarmonicBalls_of_steps (localRegularizedClusterFamilies_of_steps hlocal h35 h32 h43)

end HarmonicBalls
