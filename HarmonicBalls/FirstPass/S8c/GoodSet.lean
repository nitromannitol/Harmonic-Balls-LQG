import HarmonicBalls.FirstPass.S8c.Measurability
import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodScaling

/-! # The recentred good set (step G: local finiteness and measurability)

The good set `recentredGoodSet` consists of the pairs `(z, η)` such that, for all large `N`, at least `(1 - ζ) N`
scales `n ∈ [N+1, 2N]` are good for the normalised recentred measure `η`, at the origin with lattice phase `-z`
(the lattice of `(VG-iii)` is anchored at the original origin and is shifted by `-z` after recentring; see
`docs/campaign/audits/LocalRootedComparisonRepair.md`, "Countable tail event and exact transfer").
Its second component is taken through `finitePart`, which is locally finite for every measure
(`isLocallyFiniteMeasure_finitePart`), so that the phase-annulus measurability of
`Proofs/Sec8/PhaseVeryGoodScaling.lean:24` applies. Measurability of the good set is proved from the unit
good-annulus measurability hypothesis `hunit` (open input L2); the locality identity is a separate step.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

section LocalFiniteness

/-- The finite part of any measure is finite on every closed ball. -/
theorem finitePart_closedBall_lt_top (η : Measure ℂ) (m : ℕ) :
    finitePart η (closedBall 0 m) < ∞ := by
  rw [finitePart_apply measurableSet_closedBall, tsum_eq_sum (s := Finset.range (m + 1)) ?_]
  · refine ENNReal.sum_lt_top.mpr fun n _ => ?_
    have := isFiniteMeasure_ballPiece n η
    exact measure_lt_top _ _
  · intro n hn
    have hmn : m < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    have hdisj : Disjoint (ballShell n) (closedBall (0 : ℂ) m) := by
      unfold ballShell
      rw [disjointed_apply]
      have hle : closedBall (0 : ℂ) (m : ℝ) ≤
          (Finset.Iio n).sup (fun k : ℕ => closedBall (0 : ℂ) (k : ℝ)) :=
        Finset.le_sup (f := fun k : ℕ => closedBall (0 : ℂ) (k : ℝ)) (Finset.mem_Iio.mpr hmn)
      have h0 : Disjoint
          (closedBall (0 : ℂ) (n : ℝ) \
            (Finset.Iio n).sup (fun k : ℕ => closedBall (0 : ℂ) (k : ℝ)))
          ((Finset.Iio n).sup (fun k : ℕ => closedBall (0 : ℂ) (k : ℝ))) :=
        disjoint_sdiff_self_left
      exact h0.mono_right hle
    have hempty : closedBall (0 : ℂ) m ∩ ballShell n = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp hdisj.symm
    unfold ballPiece
    split_ifs
    · rw [Measure.restrict_apply measurableSet_closedBall, hempty, measure_empty]
    · rfl

/-- The finite part of any measure is locally finite. -/
theorem isLocallyFiniteMeasure_finitePart (η : Measure ℂ) : IsLocallyFiniteMeasure (finitePart η) := by
  have : IsFiniteMeasureOnCompacts (finitePart η) := ⟨fun K hK => by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
    exact lt_of_le_of_lt
      (measure_mono (hr.trans (closedBall_subset_closedBall (Nat.le_ceil r))))
      (finitePart_closedBall_lt_top η ⌈r⌉₊)⟩
  infer_instance

end LocalFiniteness

section GoodSet

theorem measurableSet_annulus_local (z : ℂ) (r₁ r₂ : ℝ) : MeasurableSet (annulus z r₁ r₂) := by
  unfold annulus
  exact measurableSet_ball.diff measurableSet_closedBall

theorem measurable_finitePart : Measurable finitePart := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have h : (fun η : Measure ℂ => finitePart η s) = fun η => ∑' n : ℕ, ballPiece n η s :=
    funext fun η => finitePart_apply hs
  rw [h]
  exact Measurable.tsum fun n => (Measure.measurable_coe hs).comp (measurable_ballPiece n)

/-- The scale-`n` predicate of the recentred good set: the very good annulus at the origin with lattice phase
`-z` for the finite part of the second component, together with the annulus-ball comparison. -/
def recentredScalePred (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (n : ℕ)
    (p : ℂ × Measure ℂ) : Prop :=
  PhaseVeryGoodAnnulus (finitePart p.2) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (-p.1) ∧
    AnnulusBallComparison (finitePart p.2) n 0 m

/-- The recentred good set: for all large `N`, at least `(1 - ζ) N` scales in `[N+1, 2N]` are good. -/
def recentredGoodSet (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) :
    Set (ℂ × Measure ℂ) :=
  {p | ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
    ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
      recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n p}.ncard : ℝ)}

theorem measurableSet_recentredScalePred (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) (n : ℕ) :
    MeasurableSet {p : ℂ × Measure ℂ | recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n p} := by
  have hμ : Measurable (fun p : ℂ × Measure ℂ => finitePart p.2) :=
    measurable_finitePart.comp measurable_snd
  have h1 : MeasurableSet {p : ℂ × Measure ℂ |
      PhaseVeryGoodAnnulus (finitePart p.2) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (-p.1)} :=
    measurableSet_phaseVeryGoodAnnulus hμ (fun p => isLocallyFiniteMeasure_finitePart p.2)
      (c := fun _ => (0 : ℂ)) measurable_const (phase := fun p => -p.1) measurable_fst.neg
      β (dyadicScale n) (dyadicScale_pos n) N₀ a b C₁m C₁p C₂m C₂p C₃ hunit
  have h2 : MeasurableSet {p : ℂ × Measure ℂ | AnnulusBallComparison (finitePart p.2) n 0 m} := by
    unfold AnnulusBallComparison
    exact measurableSet_le
      (measurable_const.mul ((Measure.measurable_coe measurableSet_ball).comp hμ))
      ((Measure.measurable_coe (measurableSet_annulus_local _ _ _)).comp hμ)
  exact h1.inter h2

theorem measurableSet_recentredGoodSet (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    MeasurableSet (recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ) := by
  classical
  have hQ := measurableSet_recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m hunit
  -- the count of good scales is a finite sum of indicators
  have hcount : ∀ (N : ℕ) (p : ℂ × Measure ℂ),
      (({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n p}.ncard : ℕ) : ℝ) =
        ∑ n ∈ Finset.Icc (N + 1) (2 * N),
          Set.indicator {q : ℂ × Measure ℂ | recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n q}
            (fun _ => (1 : ℝ)) p := by
    intro N p
    have hset : {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n p} =
        ↑((Finset.Icc (N + 1) (2 * N)).filter
          (fun n => recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n p)) := by
      ext n
      simp [Finset.mem_Icc]
    rw [hset, Set.ncard_coe_finset, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    simp [Set.indicator_apply]
  have hS : ∀ N : ℕ, MeasurableSet {p : ℂ × Measure ℂ | (1 - ζ) * (N : ℝ) ≤
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n p}.ncard : ℝ)} := by
    intro N
    have heq : {p : ℂ × Measure ℂ | (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n p}.ncard : ℝ)} =
        {p : ℂ × Measure ℂ | (1 - ζ) * (N : ℝ) ≤
          ∑ n ∈ Finset.Icc (N + 1) (2 * N),
            Set.indicator {q : ℂ × Measure ℂ | recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n q}
              (fun _ => (1 : ℝ)) p} := by
      ext p
      simp only [Set.mem_ofPred_eq, hcount N p]
    rw [heq]
    refine measurableSet_le measurable_const ?_
    exact Finset.measurable_sum _ fun n _ => measurable_const.indicator (hQ n)
  have heq : recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ =
      ⋃ M : ℕ, ⋂ N : ℕ, ⋂ (_ : M ≤ N), {p : ℂ × Measure ℂ | (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n p}.ncard : ℝ)} := by
    ext p
    simp only [recentredGoodSet, Set.mem_ofPred_eq, Filter.eventually_atTop, mem_iUnion, mem_iInter]
  rw [heq]
  exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun N =>
    MeasurableSet.iInter fun _ => hS N

end GoodSet


end HarmonicBalls
