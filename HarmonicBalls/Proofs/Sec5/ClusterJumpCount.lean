import HarmonicBalls.Proofs.Sec5.ClusterJumpDeficit

/-! # Disjoint immediate cluster increments

Immediate increments at distinct times are disjoint. Conservation of mass
therefore bounds the total mass of finitely many immediate increments.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped BigOperators ENNReal

/-- The points present at every dyadic future time but absent now. -/
def futureIncrementSet (F : ℝ → Set ℂ) (t : ℝ) : Set ℂ :=
  (⋂ n : ℕ, F (t + dyadicScale n)) \ F t

/-- An immediate increment lies in every strictly later set. -/
theorem futureIncrementSet_subset_of_lt {F : ℝ → Set ℂ} {t s : ℝ}
    (ht : 0 < t) (hts : t < s)
    (hmono : ∀ a b, 0 < a → a ≤ b → F a ⊆ F b) :
    futureIncrementSet F t ⊆ F s := by
  have hsmall : ∀ᶠ n : ℕ in atTop, dyadicScale n < s - t :=
    tendsto_dyadicScale_nhdsGT
      (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (sub_pos.mpr hts)))
  obtain ⟨n, hn⟩ := hsmall.exists
  intro x hx
  apply hmono (t + dyadicScale n) s (add_pos ht (dyadicScale_pos n)) (by linarith)
  exact Set.mem_iInter.mp hx.1 n

/-- Immediate increments at distinct positive times are disjoint. -/
theorem disjoint_futureIncrementSet {F : ℝ → Set ℂ} {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hne : s ≠ t)
    (hmono : ∀ a b, 0 < a → a ≤ b → F a ⊆ F b) :
    Disjoint (futureIncrementSet F s) (futureIncrementSet F t) := by
  rcases lt_or_gt_of_ne hne with hst | hts
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.2 (futureIncrementSet_subset_of_lt hs hst hmono hx)
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.2 (futureIncrementSet_subset_of_lt ht hts hmono hy)

/-- A finite collection of immediate increments has total mass at most the
mass at any strictly later time. -/
theorem sum_measure_futureIncrementSet_le
    (μ : Measure ℂ) (F : ℝ → Set ℂ) (T : ℝ) (S : Finset ℝ)
    (hS : ∀ t ∈ S, 0 < t ∧ t < T)
    (hmono : ∀ a b, 0 < a → a ≤ b → F a ⊆ F b)
    (hmeas : ∀ t, 0 < t → MeasurableSet (F t)) :
    ∑ t ∈ S, μ (futureIncrementSet F t) ≤ μ (F T) := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑S : Set ℝ) (futureIncrementSet F) := by
    intro s hs t ht hne
    exact disjoint_futureIncrementSet (hS s hs).1 (hS t ht).1 hne hmono
  have hmeas' : ∀ t ∈ S, MeasurableSet (futureIncrementSet F t) := by
    intro t ht
    exact (MeasurableSet.iInter fun n => hmeas _ (add_pos (hS t ht).1 (dyadicScale_pos n))).diff
      (hmeas t (hS t ht).1)
  rw [← measure_biUnion_finset hdisj hmeas']
  apply measure_mono
  exact iUnion₂_subset fun t ht => futureIncrementSet_subset_of_lt (hS t ht).1 (hS t ht).2 hmono

universe u

/-- The total mass of finitely many immediate interior cluster jumps before
`T` is at most `T`, simultaneously for all centres and finite time sets. -/
theorem ae_sum_interior_future_jump_mass_le_time
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, 0 < T → ∀ z ∈ ball (0 : ℂ) 1, ∀ S : Finset ℝ,
      (∀ t ∈ S, 0 < t ∧ t < T) →
      (∑ t ∈ S, μ ω (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \
        cluster (μ ω) 1 z t)) ≤ ENNReal.ofReal T := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps h32 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hmass hfront
  intro T hT z hz S hS
  have hsum := sum_measure_futureIncrementSet_le (μ ω) (fun t => cluster (μ ω) 1 z t) T S hS
    (fun a b ha hab => hmono a b 1 ha hab zero_lt_one z hz)
    (fun t ht => (hopen t 1 ht zero_lt_one z hz).1.measurableSet)
  have heq : (∑ t ∈ S, μ ω (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \
      cluster (μ ω) 1 z t)) = ∑ t ∈ S, μ ω (futureIncrementSet (fun t => cluster (μ ω) 1 z t) t) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact measure_future_closure_sdiff_eq_measure_future_sdiff (μ ω) (ball 0 1)
      (cluster (μ ω) 1 z t) (fun n => cluster (μ ω) 1 z (t + dyadicScale n))
      (fun _ => cluster_subset_ball)
      (fun n => (hopen (t + dyadicScale n) 1 (add_pos (hS t ht).1 (dyadicScale_pos n))
        zero_lt_one z hz).1)
      (fun n => hfront (t + dyadicScale n) (add_pos (hS t ht).1 (dyadicScale_pos n)) z hz)
  rw [heq]
  exact hsum.trans (hmass 1 T zero_lt_one hT z hz).1

/-- Any finite collection of jumps of size at least `ε` before `T` has
cardinality at most `T / ε`. -/
theorem card_mul_le_of_sum_ennreal_le {S : Finset ℝ} {J : ℝ → ℝ≥0∞} {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 ≤ ε) (hsum : (∑ t ∈ S, J t) ≤ ENNReal.ofReal T)
    (hlarge : ∀ t ∈ S, ENNReal.ofReal ε ≤ J t) :
    (S.card : ℝ) * ε ≤ T := by
  have hfin : ∀ t ∈ S, J t ≠ ⊤ := by
    intro t ht
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact (Finset.single_le_sum (fun _ _ => bot_le) ht).trans hsum
  have hsumreal : (∑ t ∈ S, (J t).toReal) ≤ T := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    simpa [ENNReal.toReal_sum hfin, ENNReal.toReal_ofReal hT] using h
  have hlower : ∀ t ∈ S, ε ≤ (J t).toReal := by
    intro t ht
    have h := ENNReal.toReal_mono (hfin t ht) (hlarge t ht)
    simpa [ENNReal.toReal_ofReal hε] using h
  have h := Finset.sum_le_sum hlower
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  exact h.trans hsumreal

/-- Almost surely, before any time `T`, there are at most `⌈T / ε⌉`
times at which the immediate interior jump has mass at least `ε`. -/
theorem ae_encard_large_interior_future_jumps_le
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, 0 < T → ∀ z ∈ ball (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      {t : ℝ | 0 < t ∧ t < T ∧ ENNReal.ofReal ε ≤
        μ ω (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \
          cluster (μ ω) 1 z t)}.encard ≤ ⌈T / ε⌉₊ := by
  filter_upwards [ae_sum_interior_future_jump_mass_le_time h32 h33 h34 h611 h82
    γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hsum
  intro T hT z hz ε hε
  let A : Set ℝ := {t : ℝ | 0 < t ∧ t < T ∧ ENNReal.ofReal ε ≤
    μ ω (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \
      cluster (μ ω) 1 z t)}
  change A.encard ≤ ⌈T / ε⌉₊
  classical
  have hcard : ∀ S : Finset ℝ, (↑S : Set ℝ) ⊆ A → S.card ≤ ⌈T / ε⌉₊ := by
    intro S hS
    have hreal := card_mul_le_of_sum_ennreal_le hT.le hε.le
      (hsum T hT z hz S (fun t ht => ⟨(hS ht).1, (hS ht).2.1⟩))
      (fun t ht => (hS ht).2.2)
    have hdiv : (S.card : ℝ) ≤ T / ε := (le_div_iff₀ hε).2 hreal
    exact_mod_cast hdiv.trans (Nat.le_ceil _)
  have hfinite : A.Finite := by
    by_contra h
    obtain ⟨S, hS, hsize⟩ := (show A.Infinite from h).exists_subset_card_eq (⌈T / ε⌉₊ + 1)
    have hbound := hcard S hS
    omega
  rw [hfinite.encard_eq_coe_toFinset_card]
  exact_mod_cast hcard hfinite.toFinset (by simp)

end HarmonicBalls
