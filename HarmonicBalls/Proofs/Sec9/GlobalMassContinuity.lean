import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec9.CountableNestedBalls
import HarmonicBalls.Proofs.Sec9.MonotoneMassConvergence

/-! # Global mass ordering and continuity of subharmonic balls -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped symmDiff

universe u

/-- Volume growth and the typical-point good-scale estimate imply that any
bounded same-centre subharmonic balls are ordered almost everywhere by mass. -/
theorem ae_bounded_subharmonicBall_order_by_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ), Bornology.IsBounded A → Bornology.IsBounded B →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z → μ ω A ≤ μ ω B →
      μ ω (A \ B) = 0 := by
  have h611 := Section6.veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure hI2
    (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2)
  have hAff := fun (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) =>
    @wholePlaneGFFAffineInvariance_proved Ω ‹MeasurableSpace Ω› P hC hcirc
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_order_of_weak_uniqueness hI2
      (subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales hI2 h82)
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_bounded_subharmonicBall_restrict_eq_of_dyadic_typical_scales hI2 h611 h82 hAff
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder hfront
  intro A B z hAb hBb hA hB hmass
  have hAB := (horder A B z hAb hBb hA hB hmass).1
  have hzero := (hfront B B z hBb hBb hB hB rfl).1
  apply measure_mono_null _ hzero
  rw [hB.1.frontier_eq]
  intro x hx
  exact ⟨interior_subset (hAB hx.1), hx.2⟩

/-- Every countable mass-ordered family of bounded same-centre subharmonic
balls has nested measurable representatives after removal of one null set. -/
theorem ae_countable_bounded_subharmonicBalls_have_nested_representatives
    {I : Type*} [Countable I] [Preorder I]
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : I → Set ℂ) (z : ℂ),
      (∀ i, Bornology.IsBounded (A i) ∧ IsSubharmonicBall (μ ω) (A i) z) →
      (∀ i j, i ≤ j → μ ω (A i) ≤ μ ω (A j)) →
      ∃ N : Set ℂ, MeasurableSet N ∧ μ ω N = 0 ∧
        (∀ i j, i ≤ j → A i \ N ⊆ A j \ N) ∧
        (∀ i, MeasurableSet (A i \ N) ∧
          (μ ω).restrict (A i \ N) = (μ ω).restrict (A i)) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_order_by_mass hI2 h82
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder
  intro A z hA hmass
  obtain ⟨N, hNm, hN, hnested⟩ := exists_common_null_set_of_ae_order (μ ω) A (by
    intro i j hij
    exact horder (A i) (A j) z (hA i).1 (hA j).1 (hA i).2 (hA j).2 (hmass i j hij))
  refine ⟨N, hNm, hN, hnested, ?_⟩
  intro i
  exact ⟨(hA i).2.1.measurableSet.diff hNm,
    Measure.restrict_congr_set (sdiff_null_ae_eq_self hN)⟩

/-- The symmetric-difference distance of bounded same-centre subharmonic
balls is the absolute difference of their real masses. -/
theorem ae_bounded_subharmonicBall_measureReal_symmDiff
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ), Bornology.IsBounded A → Bornology.IsBounded B →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      ((μ ω) (A ∆ B)).toReal = |((μ ω) A).toReal - ((μ ω) B).toReal| := by
  have h611 := Section6.veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure hI2
    (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2)
  have hAff := fun (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) =>
    @wholePlaneGFFAffineInvariance_proved Ω ‹MeasurableSpace Ω› P hC hcirc
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_symmDiff_mass_of_dyadic_typical_scales
    hI2 h611 h82 hAff γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro A B z hAb hBb hA hB
  exact measureReal_symmDiff_of_mass_identity (μ ω) (ne_of_lt hA.2.2.2.1)
    (ne_of_lt hB.2.2.2.1) (hω A B z hAb hBb hA hB)

/-- Any bounded mass-parametrized same-centre family in the plane varies
continuously in measure at positive interior times. Family existence and
joint measurability are not assumed or asserted. -/
theorem ae_massParametrized_bounded_subharmonicBall_continuous_in_measure
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : ℝ → Set ℂ) (z : ℂ) (a b t : ℝ), t ∈ Ioo a b → 0 < t →
      (∀ s ∈ Ioo a b, 0 < s → Bornology.IsBounded (A s) ∧
        IsSubharmonicBall (μ ω) (A s) z ∧ μ ω (A s) = ENNReal.ofReal s) →
      Tendsto (fun s : ℝ => ((μ ω) (A s ∆ A t)).toReal) (𝓝 t) (𝓝 0) ∧
      Tendsto (fun s : ℝ => (μ ω) (A s ∆ A t)) (𝓝 t) (𝓝 0) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_measureReal_symmDiff hI2 h82
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro A z a b t ht htpos hA
  have hAt := hA t ht htpos
  have hevent : (fun s : ℝ => ((μ ω) (A s ∆ A t)).toReal) =ᶠ[𝓝 t]
      (fun s : ℝ => |s - t|) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht, Ioi_mem_nhds htpos] with s hs hspos
    obtain ⟨hscl, hsb, hsm⟩ := hA s hs hspos
    rw [hω (A s) (A t) z hscl hAt.1 hsb hAt.2.1, hsm, hAt.2.2,
      ENNReal.toReal_ofReal hspos.le, ENNReal.toReal_ofReal htpos.le]
  have hlim : Tendsto (fun s : ℝ => |s - t|) (𝓝 t) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℝ => |s - t|) t :=
      (continuousAt_id.sub continuousAt_const).abs
    simpa using hc.tendsto
  have hreal := hlim.congr' hevent.symm
  refine ⟨hreal, ?_⟩
  have hfinite : (fun s : ℝ => ENNReal.ofReal (((μ ω) (A s ∆ A t)).toReal)) =ᶠ[𝓝 t]
      (fun s : ℝ => (μ ω) (A s ∆ A t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht, Ioi_mem_nhds htpos] with s hs hspos
    have hsfin : (μ ω) (A s) ≠ ⊤ := ne_of_lt (hA s hs hspos).2.1.2.2.2.1
    have htfin : (μ ω) (A t) ≠ ⊤ := ne_of_lt hAt.2.1.2.2.2.1
    exact ENNReal.ofReal_toReal (measure_symmDiff_ne_top hsfin htfin)
  have hm := ENNReal.tendsto_ofReal hreal
  simpa only [ENNReal.ofReal_zero] using hm.congr' hfinite


/-- Almost surely, every mass-increasing sequence of same-centre subharmonic
bounded balls in the plane eventually agrees pointwise
almost everywhere with any such ball whose real mass is its limiting mass.
The exceptional null set may depend on the sequence and comparison ball. -/
theorem ae_bounded_subharmonicBall_eventually_mem_iff_of_monotone_mass_limit
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : ℕ → Set ℂ) (B : Set ℂ) (z : ℂ),
      (∀ n, Bornology.IsBounded (A n) ∧ IsSubharmonicBall (μ ω) (A n) z) →
      Bornology.IsBounded B → IsSubharmonicBall (μ ω) B z →
      Monotone (fun n => (μ ω (A n)).toReal) →
      Tendsto (fun n => (μ ω (A n)).toReal) atTop (𝓝 ((μ ω B).toReal)) →
      ∀ᵐ x ∂(μ ω), ∀ᶠ n in atTop, (x ∈ A n ↔ x ∈ B) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_order_by_mass hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_bounded_subharmonicBall_measureReal_symmDiff hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder hdist
  intro A B z hA hBcl hB hmono hlim
  have hfin (n : ℕ) : μ ω (A n) ≠ ⊤ := ne_of_lt (hA n).2.2.2.2.1
  have hBfin : μ ω B ≠ ⊤ := ne_of_lt hB.2.2.2.1
  have hreal : Tendsto (fun n => ((μ ω) (A n ∆ B)).toReal) atTop (𝓝 0) := by
    have habs : Tendsto (fun n => |(μ ω (A n)).toReal - (μ ω B).toReal|) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => (μ ω B).toReal) atTop (𝓝 (μ ω B).toReal) :=
        tendsto_const_nhds
      simpa using (hlim.sub hconst).abs
    apply habs.congr'
    exact Eventually.of_forall fun n => (hdist (A n) B z (hA n).1 hBcl (hA n).2 hB).symm
  have hdistlim : Tendsto (fun n => (μ ω) (A n ∆ B)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hreal
    simpa only [ENNReal.ofReal_zero, ENNReal.ofReal_toReal
      (measure_symmDiff_ne_top (hfin _) hBfin)] using h
  apply ae_eventually_mem_iff_of_ae_monotone_and_tendsto_symmDiff (μ ω) A B
  · intro n m hnm
    have hle : μ ω (A n) ≤ μ ω (A m) :=
      (ENNReal.toReal_le_toReal (hfin n) (hfin m)).1 (hmono hnm)
    exact horder (A n) (A m) z (hA n).1 (hA m).1 (hA n).2 (hA m).2 hle
  · intro n
    have hle : μ ω (A n) ≤ μ ω B :=
      (ENNReal.toReal_le_toReal (hfin n) hBfin).1 (hmono.ge_of_tendsto hlim n)
    exact horder (A n) B z (hA n).1 hBcl (hA n).2 hB hle
  · exact hdistlim

/-- The same almost-everywhere convergence for mass-decreasing sequences. -/
theorem ae_bounded_subharmonicBall_eventually_mem_iff_of_antitone_mass_limit
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : ℕ → Set ℂ) (B : Set ℂ) (z : ℂ),
      (∀ n, Bornology.IsBounded (A n) ∧ IsSubharmonicBall (μ ω) (A n) z) →
      Bornology.IsBounded B → IsSubharmonicBall (μ ω) B z →
      Antitone (fun n => (μ ω (A n)).toReal) →
      Tendsto (fun n => (μ ω (A n)).toReal) atTop (𝓝 ((μ ω B).toReal)) →
      ∀ᵐ x ∂(μ ω), ∀ᶠ n in atTop, (x ∈ A n ↔ x ∈ B) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_order_by_mass hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_bounded_subharmonicBall_measureReal_symmDiff hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder hdist
  intro A B z hA hBcl hB hanti hlim
  have hfin (n : ℕ) : μ ω (A n) ≠ ⊤ := ne_of_lt (hA n).2.2.2.2.1
  have hBfin : μ ω B ≠ ⊤ := ne_of_lt hB.2.2.2.1
  have hreal : Tendsto (fun n => ((μ ω) (A n ∆ B)).toReal) atTop (𝓝 0) := by
    have habs : Tendsto (fun n => |(μ ω (A n)).toReal - (μ ω B).toReal|) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => (μ ω B).toReal) atTop (𝓝 (μ ω B).toReal) :=
        tendsto_const_nhds
      simpa using (hlim.sub hconst).abs
    apply habs.congr'
    exact Eventually.of_forall fun n => (hdist (A n) B z (hA n).1 hBcl (hA n).2 hB).symm
  have hdistlim : Tendsto (fun n => (μ ω) (A n ∆ B)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hreal
    simpa only [ENNReal.ofReal_zero, ENNReal.ofReal_toReal
      (measure_symmDiff_ne_top (hfin _) hBfin)] using h
  apply ae_eventually_mem_iff_of_ae_antitone_and_tendsto_symmDiff (μ ω) A B
  · intro n m hnm
    have hle : μ ω (A m) ≤ μ ω (A n) :=
      (ENNReal.toReal_le_toReal (hfin m) (hfin n)).1 (hanti hnm)
    exact horder (A m) (A n) z (hA m).1 (hA n).1 (hA m).2 (hA n).2 hle
  · intro n
    have hle : μ ω B ≤ μ ω (A n) :=
      (ENNReal.toReal_le_toReal hBfin (hfin n)).1 (hanti.le_of_tendsto hlim n)
    exact horder B (A n) z hBcl (hA n).1 hB (hA n).2 hle
  · exact hdistlim


end HarmonicBalls
