import HarmonicBalls.Proofs.Sec7.OriginAvoidingShell
import HarmonicBalls.Proofs.Sec7.AnnulusMass

/-!
# Confinement of a cluster increment

The mass increment bound and Harnack exclusions confine the later connected
cluster to a neighbourhood of the earlier cluster.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped Pointwise

/-- Ball-volume bounds and the Harnack cover confine a connected increment
to the `70 √ε` neighbourhood of the earlier set. -/
theorem closure_subset_add_ball_of_increment_volume_and_harnack
    (μ : Measure ℂ) {A B : Set ℂ} {ε α β T : ℝ}
    (hε : 0 < ε) (hεsqrt : ε ≤ Real.sqrt ε) (hα : 0 < α)
    (hAne : A.Nonempty) (hAB : A ⊆ B) (hB : IsPreconnected B)
    (hA : NullMeasurableSet A μ) (hAfin : μ A ≠ ⊤)
    (hmass : μ B ≤ μ A + ENNReal.ofReal T)
    (hT : T ≤ α * (ε / 8) ^ β)
    (hunit : thickening (70 * Real.sqrt ε) A ⊆ ball 0 1)
    (hvol : ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal ((ε / 8) ^ β) ≤ μ (ball x (ε / 8)))
    (P : ℝ → ℂ → Prop)
    (hgood : ∀ w ∈ prevalenceGrid ε, ∃ ρ ∈ Icc ε (Real.sqrt ε), P ρ w)
    (hharnack : ∀ w ∈ prevalenceGrid ε, ∀ ρ ∈ Icc ε (Real.sqrt ε), P ρ w →
      closedBall w ρ ⊆ ball 0 1 \ A →
      μ (B ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) →
      B ∩ ball w (ρ / 2) = ∅) :
    closure B ⊆ A + ball 0 (70 * Real.sqrt ε) := by
  obtain ⟨q, hq, hqR, hcover⟩ :=
    exists_origin_avoiding_lattice_shell_cover hAne hε hεsqrt hunit P hgood
  apply IsPreconnected.closure_subset_add_ball_of_disjoint_infDist_level hB
    (hAne.mono (fun x hx => ⟨hx, hAB hx⟩)) hq hqR
  intro x hxB hxq
  obtain ⟨w, hw, ρ, hρ, hP, hxball, hdomain⟩ := hcover x hxq
  have hdis : Disjoint (annulus w (ρ / 2) ρ) A := by
    apply disjoint_left.2
    intro y hy hyA
    exact (hdomain (ball_subset_closedBall hy.1)).2 hyA
  have hlower : ENNReal.ofReal T ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) := by
    calc
      ENNReal.ofReal T ≤ ENNReal.ofReal (α * (ε / 8) ^ β) := ENNReal.ofReal_le_ofReal hT
      _ = ENNReal.ofReal α * ENNReal.ofReal ((ε / 8) ^ β) := ENNReal.ofReal_mul hα.le
      _ ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) := by
        gcongr
        exact lower_mass_half_annulus_of_ball_volume μ hε hvol hρ.1
          (hdomain.trans sdiff_subset)
  have hsmall := (measure_inter_le_of_disjoint_of_measure_le_add hAB hA hAfin hmass hdis).trans hlower
  have hempty := hharnack w hw ρ hρ hP hdomain hsmall
  exact (eq_empty_iff_forall_notMem.1 hempty) x ⟨hxB, hxball⟩

end HarmonicBalls
