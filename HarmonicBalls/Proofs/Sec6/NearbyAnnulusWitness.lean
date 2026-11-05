import HarmonicBalls.Proofs.Sec6.NearbyAnnulusBoundary

/-! # Small-mass witnesses for nearby annuli

A test set on a displaced annulus extends across the boundary layer to a
small-mass test set on the reference annulus. The comparison of the Brownian
avoidance probabilities remains a separate question.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter Metric MarkovProcess
open scoped ENNReal Topology

/-- At null boundary circles, strict slack in the mass parameter absorbs both
annulus mass variation and the boundary layer. -/
theorem exists_nearby_annulus_witness_mass_transfer
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (r R : ℝ)
    (hr : μ (sphere z r) = 0) (hR : μ (sphere z R) = 0)
    (hpos : 0 < μ (annulus z r R)) (hfin : μ (annulus z r R) ≠ ∞)
    {a a' : ℝ≥0∞} (ha : a' < a) (ha' : a' ≠ ∞) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, dist w z < ε → ∀ Y : Set ℂ,
      μ Y ≤ a' * μ (annulus w r R) →
      μ ((annulus z r R ∩ Y) ∪ (annulus z r R \ annulus w r R)) ≤
        a * μ (annulus z r R) := by
  let A := annulus z r R
  let d : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [d, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hf : Tendsto (fun n => a' * (μ A + d n) + d n) atTop (𝓝 (a' * μ A)) := by
    have hh : Tendsto (fun n => a' * (μ A + d n)) atTop (𝓝 (a' * μ A)) := by
      have ht := (ENNReal.continuous_const_mul ha').tendsto (μ A)
      have hs : Tendsto (fun n => μ A + d n) atTop (𝓝 (μ A)) := by
        simpa using tendsto_const_nhds.add hd
      exact ht.comp hs
    simpa using hh.add hd
  have hlt : a' * μ A < a * μ A := ENNReal.mul_lt_mul_left hpos.ne' hfin ha
  have hex : ∀ᶠ n in atTop, a' * (μ A + d n) + d n < a * μ A :=
    hf.eventually_lt_const hlt
  obtain ⟨n, hn⟩ := hex.exists
  have hdpos : 0 < d n := by dsimp [d]; exact ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨ε, hε, hδ⟩ := exists_nearby_annulus_symmDiff_mass_lt μ z r R hr hR hdpos
  refine ⟨ε, hε, ?_⟩
  intro w hw Y hY
  let B := annulus w r R
  let D := (A \ B) ∪ (B \ A)
  have hD : μ D ≤ d n := (hδ w hw).le
  have hAB : μ (A \ B) ≤ d n := (measure_mono (subset_union_left : A \ B ⊆ D)).trans hD
  have hBA : μ (B \ A) ≤ d n := (measure_mono (subset_union_right : B \ A ⊆ D)).trans hD
  have hB : μ B ≤ μ A + d n := by
    calc
      μ B ≤ μ (A ∪ (B \ A)) := measure_mono (by intro x hx; by_cases hxA : x ∈ A <;> simp_all)
      _ ≤ μ A + μ (B \ A) := measure_union_le _ _
      _ ≤ μ A + d n := add_le_add le_rfl hBA
  calc
    μ ((A ∩ Y) ∪ (A \ B)) ≤ μ (A ∩ Y) + μ (A \ B) := measure_union_le _ _
    _ ≤ μ Y + d n := add_le_add (measure_mono inter_subset_right) hAB
    _ ≤ a' * (μ A + d n) + d n := add_le_add (hY.trans (by gcongr)) le_rfl
    _ ≤ a * μ A := hn.le

/-- An avoidance comparison for the extended witnesses transfers a good
annulus to nearby centres with slack in both parameters. The comparison is an
explicit Brownian hypothesis; it is not implied by the mass estimate. -/
theorem nearby_isGoodAnnulus_of_witness_avoidance_comparison
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (r : ℝ)
    (hr : μ (sphere z (3 * r)) = 0) (hR : μ (sphere z (5 * r)) = 0)
    (hpos : 0 < μ (annulus z (3 * r) (5 * r)))
    (hfin : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    {a a' b b' : ℝ} (haa : ENNReal.ofReal a' < ENNReal.ofReal a)
    (hgood : IsGoodAnnulus μ r z a b) (c : ℝ≥0∞)
    (hbc : ENNReal.ofReal b + c ≤ ENNReal.ofReal b') :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, dist w z < ε →
      (∀ Y : Set ℂ, MeasurableSet Y → Y ⊆ annulus w (3 * r) (5 * r) →
        ∀ u ∈ sphere w (4 * r), ∃ v ∈ sphere z (4 * r),
        planarBrownianMotion u {p | ContinuousPath.exitTime (annulus w (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime Y p} ≤
        planarBrownianMotion v {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime ((annulus z (3 * r) (5 * r) ∩ Y) ∪
            (annulus z (3 * r) (5 * r) \ annulus w (3 * r) (5 * r))) p} + c) →
      IsGoodAnnulus μ r w a' b' := by
  obtain ⟨ε, hε, hmass⟩ := exists_nearby_annulus_witness_mass_transfer μ z (3 * r) (5 * r)
    hr hR hpos hfin haa ENNReal.ofReal_ne_top
  refine ⟨ε, hε, ?_⟩
  intro w hw hcompare Y hY hYA hYmass u hu
  let A := annulus z (3 * r) (5 * r)
  let B := annulus w (3 * r) (5 * r)
  let X := (A ∩ Y) ∪ (A \ B)
  have hA : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hB : MeasurableSet B := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hX : MeasurableSet X := (hA.inter hY).union (hA.diff hB)
  have hXA : X ⊆ A := union_subset inter_subset_left sdiff_subset
  have hXm : μ X ≤ ENNReal.ofReal a * μ A := hmass w hw Y hYmass
  obtain ⟨v, hv, hcomp⟩ := hcompare Y hY hYA u hu
  exact hcomp.trans ((add_le_add (hgood X hX hXA hXm v hv) le_rfl).trans hbc)

end HarmonicBalls.Section6
