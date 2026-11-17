import HarmonicBalls.Proofs.Potential.LQGClockInsertedLocalizedTimeSplit

/-! # Measurability of localized inserted occupations

Closed-cutoff occupations of inserted circle-average densities admit
jointly measurable field and path representatives.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Closed-cutoff inserted occupations at any countable family of positive
smoothing radii have measurable versions on one field event for all paths. -/
theorem exists_measurable_inserted_closedBall_occupations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α δ : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ F : ℕ → ContinuousPath ℂ × Ω → ℝ, (∀ n, Measurable (F n)) ∧
      ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (n : ℕ),
        F n (b, ω) = ∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => (ε n)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z)) z
          ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1)))) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let E : Set ℂ := {z | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}
  have hE : MeasurableSet E := (measurableSet_le measurable_norm measurable_const).inter
    (measurableSet_le measurable_norm measurable_const)
  let G : ℕ → Ω × ℂ → ℝ := fun n q => E.indicator (fun z =>
    (ε n)^(γ^2/2) * Real.exp (γ * (H q.1 (ε n) z - H q.1 1 0 -
      α * Real.log (max (ε n) ‖z‖)))) q.2
  have hG (n : ℕ) : Measurable (G n) := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 (ε n) q.2) :=
      (hHm (ε n) (hε n)).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
    apply Measurable.indicator _ (hE.preimage measurable_snd)
    exact measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have heval0 : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2) := by fun_prop
  have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ≥0 => q.1.1 q.2) :=
    heval0.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hpath (n : ℕ) : Measurable (fun q : ContinuousPath ℂ × Ω =>
      ∫ z, G n (q.2,z) ∂(Measure.map (fun t => q.1 t) ν)) := by
    have h := ((hG n).comp ((measurable_snd.comp measurable_fst).prodMk heval)).stronglyMeasurable.integral_prod_right' (ν := ν)
    convert h.measurable using 1
    funext q
    exact integral_map q.1.continuous.measurable.aemeasurable
      ((hG n).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  refine ⟨fun n q => ∫ z, G n (q.2,z) ∂(Measure.map (fun t => q.1 t) ν), hpath, ?_⟩
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hr b n
  apply integral_congr_ae
  filter_upwards with z
  simp only [G, Set.indicator_apply]
  split_ifs
  · rw [hω, hω, hr (ε n) z (hε n)]
  · rfl

/-- An actual closed-cutoff occupation is almost everywhere measurable under
any product of the field law and an s-finite path law. -/
theorem aemeasurable_inserted_closedBall_occupation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (Q : Measure (ContinuousPath ℂ)) [SFinite Q] (γ α δ ε : ℝ) (hε : 0 < ε) :
    AEMeasurable (fun q : ContinuousPath ℂ × Ω =>
      ∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ε^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z)) z
        ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))) (Q.prod P) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_inserted_closedBall_occupations hh γ α δ
    (fun _ => ε) (fun _ => hε)
  apply (hFm 0).aemeasurable.congr
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := Q) (ν := P)).ae hFae] with q hq
  exact hq q.1 0

end HarmonicBalls
