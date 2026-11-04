import HarmonicBalls.Proofs.Sec8.PhaseScaleTransport
import HarmonicBalls.Proofs.Sec8.AEIndicatorFrequency
import Mathlib.Dynamics.Ergodic.Function

/-! # Ergodic averages for phase-shifted scales

The pointwise ergodic theorem and its invariant limit are from Leonardo
Bonanno's LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory Filter Finset
open scoped Topology BigOperators

namespace HarmonicBalls

/-- An ergodic sequence law has an almost-surely constant Cesàro limit.
Ergodicity is an explicit hypothesis: stationarity alone does not imply it. -/
theorem ae_constant_initialScaleAverage_of_ergodic_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n))
    (hInt : Integrable (X 1) P)
    (herg : Ergodic (fun x : ℕ → ℝ => fun n => x (n + 1))
      (P.map (fun ω n => X (n + 1) ω))) :
    ∃ c : ℝ, ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)) atTop (𝓝 c) := by
  let path : Ω → ℕ → ℝ := fun ω n => X (n + 1) ω
  let shift : (ℕ → ℝ) → (ℕ → ℝ) := fun x n => x (n + 1)
  let Q : Measure (ℕ → ℝ) := P.map path
  have hp : Measurable path := Measurable.of_eval (fun n => hXm (n + 1))
  have heval : Measurable (fun x : ℕ → ℝ => x 0) := measurable_pi_apply 0
  have hi : Integrable (fun x : ℕ → ℝ => x 0) Q := by
    apply (integrable_map_measure heval.aestronglyMeasurable hp.aemeasurable).2
    simpa only [Function.comp_def, path, zero_add] using hInt
  have he : Ergodic shift Q := herg
  have : IsProbabilityMeasure Q := inferInstance
  have hm := LatticeProb.measurable_bLimsup he.toMeasurePreserving.measurable heval
  have hinv := LatticeProb.ae_bLimsup_comp he.toMeasurePreserving heval hi
  obtain ⟨c, hc⟩ := he.ae_eq_const_of_ae_eq_comp₀ hm.nullMeasurable hinv
  have hconv := LatticeProb.ae_tendsto_bLimsup he.toMeasurePreserving heval hi
  have hpath : ∀ᵐ ω ∂P, Tendsto (fun n => LatticeProb.bAvg shift (fun x => x 0) n (path ω))
      atTop (𝓝 c) := by
    have ha : ∀ᵐ x ∂Q, Tendsto (fun n => LatticeProb.bAvg shift (fun x => x 0) n x)
        atTop (𝓝 c) := by
      filter_upwards [hconv, hc] with x hx hcx
      simpa only [Function.const_apply, hcx] using hx
    exact ae_of_ae_map hp.aemeasurable ha
  refine ⟨c, ?_⟩
  filter_upwards [hpath] with ω hω
  convert hω using 1
  funext N
  have hsum : (∑ n ∈ Icc 1 N, X n ω) = ∑ n ∈ range N, X (n + 1) ω := by
    symm
    apply Finset.sum_bij (fun n _ => n + 1)
    · intro n hn; simp only [mem_range] at hn; simp only [mem_Icc]; omega
    · intro a ha b hb hab; omega
    · intro b hb; simp only [mem_Icc] at hb
      refine ⟨b - 1, ?_, ?_⟩
      · simp only [mem_range]; omega
      · omega
    · intro a ha; rfl
  rw [hsum]
  unfold LatticeProb.bAvg birkhoffSum
  simp only [div_eq_mul_inv, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hiter : ∀ k : ℕ, ∀ x : ℕ → ℝ, ∀ m : ℕ, (shift^[k] x) m = x (m + k) := by
    intro k
    induction k with
    | zero => intro x m; simp
    | succ k ih =>
      intro x m
      rw [Function.iterate_succ_apply']
      change (shift^[k] x) (m + 1) = x (m + (k + 1))
      rw [ih]
      congr 1; omega
  simpa [path] using (hiter n (path ω) 0).symm

/-- A bounded stationary sequence with an ergodic tail law has almost-sure
limiting frequency equal to its one-scale mean. -/
theorem ae_tendsto_initialScaleAverage_of_ergodic_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n))
    (hbound : ∀ n ω, X n ω ∈ Set.Icc (0 : ℝ) 1)
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω))
    (herg : Ergodic (fun x : ℕ → ℝ => fun n => x (n + 1))
      (P.map (fun ω n => X (n + 1) ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)) atTop (𝓝 (∫ ω, X 0 ω ∂P)) := by
  have hXi : ∀ n, Integrable (X n) P := by
    intro n
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hXm n).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound n ω).1]
    exact (hbound n ω).2
  obtain ⟨c, hc⟩ := ae_constant_initialScaleAverage_of_ergodic_law P X hXm (hXi 1) herg
  let F : ℕ → Ω → ℝ := fun N ω => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)
  have hF : ∀ N, AEStronglyMeasurable (F N) P :=
    fun N => (integrable_initialScaleAverage P X hXi N).aestronglyMeasurable
  have hFb : ∀ N, ∀ᵐ ω ∂P, ‖F N ω‖ ≤ 1 := by
    intro N
    filter_upwards with ω
    have h := initialScaleAverage_mem_Icc (fun n => X n ω) (fun n => hbound n ω) N
    simpa only [F, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have hmean : ∀ n, ∫ ω, X n ω ∂P = ∫ ω, X 0 ω ∂P :=
    integral_eq_first_of_stationary P X hXm hstat
  have hFm : ∀ᶠ N : ℕ in atTop, ∫ ω, F N ω ∂P = ∫ ω, X 0 ω ∂P := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact integral_initialScaleAverage_eq P X _ hXi hmean (by omega)
  have heq := constant_limit_eq_of_eventually_integral_eq P F c (∫ ω, X 0 ω ∂P) 1
    hF hFb hc hFm
  simpa only [heq] using hc

open Classical in
/-- A phase-shifted good-scale sequence has its one-scale mean as limiting
frequency if its tail law is ergodic. The phase and measure laws are assumed
invariant under their respective dyadic maps. -/
theorem ae_tendsto_phaseVeryGoodComparable_average_of_ergodic_law
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure T) [IsProbabilityMeasure Q]
    (D : T → T) (hD : Measurable D) (hQ : Q.map D = Q)
    (phase : T → ℂ) (hphase : Measurable phase)
    (hperiod : ∀ t, phase (D t) - (2 : ℝ) • phase t ∈
      Section6.scaledLattice ((1 : ℝ) / 100))
    (U V : Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν})
    (hU : Measurable U) (hV : Measurable V) (hlaw : P.map V = P.map U)
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α β : ℝ)
    (hVeq : ∀ ω, (V ω).val =
      normalizedPullbackMeasure γ α (dyadicScale 1) (hcirc ω) (U ω).val)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (herg : Ergodic (fun x : ℕ → ℝ => fun n => x (n + 1))
      ((Q.prod P).map (fun p n => if
        PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale (n + 1)) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
        AnnulusBallComparison (U p.2).val (n + 1) 0 m then (1 : ℝ) else 0))) :
    ∀ᵐ p ∂(Q.prod P), Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, if
        PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
        AnnulusBallComparison (U p.2).val n 0 m then (1 : ℝ) else 0) / (N : ℝ)) atTop
      (𝓝 (((Q.prod P) {p | PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale 0) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
        AnnulusBallComparison (U p.2).val 0 0 m}).toReal)) := by
  let X : ℕ → T × Ω → ℝ := fun n p => if
    PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
    AnnulusBallComparison (U p.2).val n 0 m then 1 else 0
  have hval : Measurable (fun p : T × Ω => (U p.2).val) :=
    measurable_subtype_coe.comp (hU.comp measurable_snd)
  have hfin : ∀ p : T × Ω, IsLocallyFiniteMeasure (U p.2).val := fun p => (U p.2).property
  have hm : ∀ n, Measurable (X n) := by
    intro n
    have hs := (measurableSet_phaseVeryGoodAnnulus
      (c := fun _ : T × Ω => (0 : ℂ)) hval hfin measurable_const
      (hphase.comp measurable_fst) β (dyadicScale n) (dyadicScale_pos n) N₀
      a b C₁m C₁p C₂m C₂p C₃ hunit).inter
      (measurableSet_annulusBallComparison_joint (c := fun _ : T × Ω => (0 : ℂ))
        hval hfin measurable_const n m)
    exact measurable_const.piecewise hs measurable_const
  have hb : ∀ n p, X n p ∈ Set.Icc (0 : ℝ) 1 := by
    intro n p
    dsimp only [X]
    split_ifs <;> norm_num
  have hstat : (Q.prod P).map (fun p n => X (n + 1) p) =
      (Q.prod P).map (fun p n => X n p) :=
    phaseVeryGoodComparable_stationary_of_pullback_law P Q D hD hQ phase hphase hperiod
      U V hU hV hlaw hcirc γ α β hVeq N₀ a b C₁m C₁p C₂m C₂p C₃ m hunit
  have hconv := ae_tendsto_initialScaleAverage_of_ergodic_law (Q.prod P) X hm hb hstat herg
  have hint := integral_eq_measure_of_indicator (Q.prod P)
    {p | PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale 0) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
      AnnulusBallComparison (U p.2).val 0 0 m} (X 0) (hm 0) (fun p => by simp only [X, Set.mem_ofPred_eq]; split_ifs <;> rfl)
  simpa only [X, hint] using hconv

end HarmonicBalls
