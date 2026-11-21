import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller
import HarmonicBalls.Proofs.Sec6.CompactHittingStopping
import MarkovProcess.Trajectory.StoppingLtTop
import MarkovProcess.Path.ExitTimeShift

/-! # Return iteration for Brownian occupation moments

A nonnegative density supported on a closed set `Q`, possibly depending on an
independent random environment, is integrated along a planar Brownian path until
the path leaves an open set `D`. A visit to `Q` is followed up to the exit from an
open set `U`; from outside `U` the path comes back to `Q` before leaving `D` with
probability at most `θ < 1`. The strong Markov property at the exit time of `U`
and at the entrance time of `Q` bounds the `q`-th moment of the total occupation,
for `q ≥ 1`, by the largest moment of one visit divided by `(1 - θ ^ (1 / q)) ^ q`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology

namespace HarmonicBalls

/-- The occupation of a nonnegative density by a path at the nonnegative times
before `T`. -/
noncomputable def pathOccupationBefore (g : ℂ → ℝ≥0∞) (T : ℝ≥0∞)
    (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∫⁻ s, {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T}.indicator (fun s => g (b s.toNNReal)) s

/-- The occupation is jointly measurable in a parameter that measurably selects the
density, the time and the path. -/
theorem measurable_pathOccupationBefore {α : Type*} [MeasurableSpace α]
    (g : α → ℂ → ℝ≥0∞) (hg : Measurable (Function.uncurry g))
    (T : α → ℝ≥0∞) (hT : Measurable T) (π : α → ContinuousPath ℂ) (hπ : Measurable π) :
    Measurable (fun a => pathOccupationBefore (g a) (T a) (π a)) := by
  have hev : Measurable (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hset : MeasurableSet {p : α × ℝ | 0 ≤ p.2 ∧ ENNReal.ofReal p.2 < T p.1} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hT.comp measurable_fst))
  have hF : Measurable (fun p : α × ℝ => g p.1 (π p.1 p.2.toNNReal)) :=
    hg.comp (measurable_fst.prodMk (hev.comp ((hπ.comp measurable_fst).prodMk measurable_snd)))
  convert (hF.indicator hset).lintegral_prod_right' (ν := (volume : Measure ℝ)) using 1
  funext a
  unfold pathOccupationBefore
  apply lintegral_congr
  intro s
  by_cases hs : 0 ≤ s ∧ ENNReal.ofReal s < T a
  · rw [Set.indicator_of_mem (show s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T a} from hs),
      Set.indicator_of_mem
        (show (a, s) ∈ {p : α × ℝ | 0 ≤ p.2 ∧ ENNReal.ofReal p.2 < T p.1} from hs)]
  · rw [Set.indicator_of_notMem (show s ∉ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T a} from hs),
      Set.indicator_of_notMem
        (show (a, s) ∉ {p : α × ℝ | 0 ≤ p.2 ∧ ENNReal.ofReal p.2 < T p.1} from hs)]

/-- The occupation integrand is monotone in the density and in the time. -/
theorem occupation_indicator_mono {g g' : ℂ → ℝ≥0∞} (hg : ∀ z, g z ≤ g' z) {T T' : ℝ≥0∞}
    (hT : T ≤ T') (b : ContinuousPath ℂ) (s : ℝ) :
    {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T}.indicator (fun s => g (b s.toNNReal)) s ≤
      {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T'}.indicator (fun s => g' (b s.toNNReal)) s := by
  by_cases hs : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T}
  · have hs' : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T'} := ⟨hs.1, hs.2.trans_le hT⟩
    rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs']
    exact hg _
  · rw [Set.indicator_of_notMem hs]
    exact zero_le

/-- The occupation is monotone in the density and in the time. -/
theorem pathOccupationBefore_mono {g g' : ℂ → ℝ≥0∞} (hg : ∀ z, g z ≤ g' z) {T T' : ℝ≥0∞}
    (hT : T ≤ T') (b : ContinuousPath ℂ) :
    pathOccupationBefore g T b ≤ pathOccupationBefore g' T' b :=
  lintegral_mono fun s => occupation_indicator_mono hg hT b s

/-- A density bounded by `c` has occupation at most `c` times a finite time bound. -/
theorem pathOccupationBefore_le_mul {g : ℂ → ℝ≥0∞} {c : ℝ≥0∞} (hg : ∀ z, g z ≤ c)
    {T : ℝ≥0∞} {t : ℝ≥0} (hT : T ≤ t) (b : ContinuousPath ℂ) :
    pathOccupationBefore g T b ≤ c * t := by
  unfold pathOccupationBefore
  calc (∫⁻ s, {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T}.indicator (fun s => g (b s.toNNReal)) s)
      ≤ ∫⁻ s, (Ico (0 : ℝ) t).indicator (fun _ => c) s := by
        refine lintegral_mono fun s => ?_
        by_cases hs : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T}
        · have hst : s < (t : ℝ) := by
            have h := (ENNReal.ofReal_lt_iff_lt_toReal hs.1 ENNReal.coe_ne_top).1
              (hs.2.trans_le hT)
            rwa [ENNReal.coe_toReal] at h
          rw [Set.indicator_of_mem hs,
            Set.indicator_of_mem (show s ∈ Ico (0 : ℝ) t from ⟨hs.1, hst⟩)]
          exact hg _
        · rw [Set.indicator_of_notMem hs]
          exact zero_le
    _ = c * t := by
        rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico, sub_zero,
          ENNReal.ofReal_coe_nnreal]

/-- A density vanishing off `Q` has no occupation before the path first meets `Q`. -/
theorem pathOccupationBefore_eq_zero_of_le_exitTime_compl {Q : Set ℂ} {g : ℂ → ℝ≥0∞}
    (hg : ∀ z, z ∉ Q → g z = 0) (T : ℝ≥0∞) (b : ContinuousPath ℂ)
    (hT : T ≤ ContinuousPath.exitTime Qᶜ b) : pathOccupationBefore g T b = 0 := by
  unfold pathOccupationBefore
  have h0 : (fun s => {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T}.indicator
      (fun s => g (b s.toNNReal)) s) = fun _ => 0 := by
    funext s
    by_cases hs : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T}
    · rw [Set.indicator_of_mem hs]
      apply hg
      have hlt : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime Qᶜ b := hs.2.trans_le hT
      exact ContinuousPath.mem_of_lt_exitTime Qᶜ b s.toNNReal hlt
    · exact Set.indicator_of_notMem hs _
  rw [h0, lintegral_zero]

/-- Splitting the occupation before the exit from `D` at a deterministic time `ρ`:
the part after `ρ` is the occupation of the shifted path. -/
theorem pathOccupationBefore_le_add_shift {g : ℂ → ℝ≥0∞} (hg : Measurable g) (D : Set ℂ)
    (T : ℝ≥0∞) (ρ : ℝ≥0) (b : ContinuousPath ℂ) :
    pathOccupationBefore g (min (ContinuousPath.exitTime D b) T) b ≤
      pathOccupationBefore g (min (ρ : ℝ≥0∞) (min (ContinuousPath.exitTime D b) T)) b +
        pathOccupationBefore g (min (ContinuousPath.exitTime D (ContinuousPath.shift ρ b)) T)
          (ContinuousPath.shift ρ b) := by
  have hF : Measurable (fun s : ℝ => g (b s.toNNReal)) :=
    hg.comp (b.continuous.measurable.comp measurable_real_toNNReal)
  have hA1 : MeasurableSet {s : ℝ | 0 ≤ s ∧
      ENNReal.ofReal s < min (ρ : ℝ≥0∞) (min (ContinuousPath.exitTime D b) T)} :=
    (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  have hsplit : ∀ s, {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s <
        min (ContinuousPath.exitTime D b) T}.indicator (fun s => g (b s.toNNReal)) s ≤
      {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s <
        min (ρ : ℝ≥0∞) (min (ContinuousPath.exitTime D b) T)}.indicator
        (fun s => g (b s.toNNReal)) s +
      {s : ℝ | (ρ : ℝ) ≤ s ∧ ENNReal.ofReal s <
        min (ContinuousPath.exitTime D b) T}.indicator (fun s => g (b s.toNNReal)) s := by
    intro s
    by_cases hs : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < min (ContinuousPath.exitTime D b) T}
    · rw [Set.indicator_of_mem hs]
      by_cases hsρ : s < (ρ : ℝ)
      · have h1 : ENNReal.ofReal s < (ρ : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.1).2 hsρ
        have hmem : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s <
            min (ρ : ℝ≥0∞) (min (ContinuousPath.exitTime D b) T)} := ⟨hs.1, lt_min h1 hs.2⟩
        rw [Set.indicator_of_mem hmem]
        exact le_self_add
      · have hmem : s ∈ {s : ℝ | (ρ : ℝ) ≤ s ∧ ENNReal.ofReal s <
            min (ContinuousPath.exitTime D b) T} := ⟨not_lt.mp hsρ, hs.2⟩
        rw [Set.indicator_of_mem hmem]
        exact le_add_self
    · rw [Set.indicator_of_notMem hs]
      exact zero_le
  have htail : (∫⁻ s, {s : ℝ | (ρ : ℝ) ≤ s ∧ ENNReal.ofReal s <
        min (ContinuousPath.exitTime D b) T}.indicator (fun s => g (b s.toNNReal)) s) ≤
      pathOccupationBefore g (min (ContinuousPath.exitTime D (ContinuousPath.shift ρ b)) T)
        (ContinuousPath.shift ρ b) := by
    rw [← lintegral_add_right_eq_self (μ := volume) ({s : ℝ | (ρ : ℝ) ≤ s ∧ ENNReal.ofReal s <
        min (ContinuousPath.exitTime D b) T}.indicator (fun s => g (b s.toNNReal))) (ρ : ℝ)]
    unfold pathOccupationBefore
    refine lintegral_mono fun t => ?_
    by_cases ht : t + (ρ : ℝ) ∈ {s : ℝ | (ρ : ℝ) ≤ s ∧ ENNReal.ofReal s <
        min (ContinuousPath.exitTime D b) T}
    · have ht' : (ρ : ℝ) ≤ t + ρ ∧ ENNReal.ofReal (t + ρ) <
          min (ContinuousPath.exitTime D b) T := ht
      have ht0 : 0 ≤ t := by linarith [ht'.1]
      have hof : ENNReal.ofReal (t + (ρ : ℝ)) = ENNReal.ofReal t + (ρ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add ht0 ρ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      have hlt : ENNReal.ofReal t + (ρ : ℝ≥0∞) < min (ContinuousPath.exitTime D b) T := by
        rw [← hof]
        exact ht'.2
      have hρτ : (ρ : ℝ≥0∞) < ContinuousPath.exitTime D b :=
        lt_of_le_of_lt le_add_self (lt_of_lt_of_le hlt (min_le_left _ _))
      have hshift := ContinuousPath.exitTime_shift_add D b ρ hρτ
      have hmem : t ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s <
          min (ContinuousPath.exitTime D (ContinuousPath.shift ρ b)) T} := by
        refine ⟨ht0, lt_min ?_ ?_⟩
        · have h2 : ENNReal.ofReal t + (ρ : ℝ≥0∞) <
              ContinuousPath.exitTime D (ContinuousPath.shift ρ b) + ρ := by
            rw [hshift]
            exact lt_of_lt_of_le hlt (min_le_left _ _)
          exact (ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top).mp h2
        · exact lt_of_le_of_lt le_self_add (lt_of_lt_of_le hlt (min_le_right _ _))
      rw [Set.indicator_of_mem ht, Set.indicator_of_mem hmem]
      refine le_of_eq ?_
      congr 1
      rw [ContinuousPath.shift_apply, Real.toNNReal_add ht0 ρ.coe_nonneg, Real.toNNReal_coe,
        add_comm]
    · rw [Set.indicator_of_notMem ht]
      exact zero_le
  calc pathOccupationBefore g (min (ContinuousPath.exitTime D b) T) b
      ≤ ∫⁻ s, ({s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s <
          min (ρ : ℝ≥0∞) (min (ContinuousPath.exitTime D b) T)}.indicator
          (fun s => g (b s.toNNReal)) s +
        {s : ℝ | (ρ : ℝ) ≤ s ∧ ENNReal.ofReal s <
          min (ContinuousPath.exitTime D b) T}.indicator (fun s => g (b s.toNNReal)) s) :=
        lintegral_mono hsplit
    _ = pathOccupationBefore g (min (ρ : ℝ≥0∞) (min (ContinuousPath.exitTime D b) T)) b +
          ∫⁻ s, {s : ℝ | (ρ : ℝ) ≤ s ∧ ENNReal.ofReal s <
            min (ContinuousPath.exitTime D b) T}.indicator (fun s => g (b s.toNNReal)) s :=
        lintegral_add_left (hF.indicator hA1) _
    _ ≤ _ := add_le_add le_rfl htail

/-- Truncating the density at height `n` and the time at `n` recovers the occupation in
the limit. -/
theorem tendsto_pathOccupationBefore_min (g : ℂ → ℝ≥0∞) (hg : Measurable g) (T : ℝ≥0∞)
    (b : ContinuousPath ℂ) :
    Tendsto (fun n : ℕ => pathOccupationBefore (fun z => min (g z) (n : ℝ≥0∞))
      (min T (n : ℝ≥0∞)) b) atTop (𝓝 (pathOccupationBefore g T b)) := by
  unfold pathOccupationBefore
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact (((hg.comp (b.continuous.measurable.comp measurable_real_toNNReal)).min
      measurable_const).indicator ((measurableSet_le measurable_const measurable_id).inter
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const))).aemeasurable
  · refine Filter.Eventually.of_forall fun s n m hnm => ?_
    exact occupation_indicator_mono (g := fun z => min (g z) (n : ℝ≥0∞))
      (g' := fun z => min (g z) (m : ℝ≥0∞))
      (fun z => min_le_min_left _ (Nat.cast_le.mpr hnm))
      (min_le_min_left _ (Nat.cast_le.mpr hnm)) b s
  · refine Filter.Eventually.of_forall fun s => ?_
    by_cases hs : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T}
    · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.ofReal_ne_top (r := s))
      rw [Set.indicator_of_mem hs]
      have hev : (fun n : ℕ => min (g (b s.toNNReal)) (n : ℝ≥0∞)) =ᶠ[atTop]
          (fun n : ℕ => {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < min T (n : ℝ≥0∞)}.indicator
            (fun s => min (g (b s.toNNReal)) (n : ℝ≥0∞)) s) := by
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        have hmem : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < min T (n : ℝ≥0∞)} :=
          ⟨hs.1, lt_min hs.2 (hN.trans_le (Nat.cast_le.mpr hn))⟩
        exact (Set.indicator_of_mem hmem (fun s => min (g (b s.toNNReal)) (n : ℝ≥0∞))).symm
      refine Tendsto.congr' hev ?_
      have h := (tendsto_const_nhds (x := g (b s.toNNReal))).min ENNReal.tendsto_nat_nhds_top
      simpa using h
    · rw [Set.indicator_of_notMem hs]
      have h0 : ∀ n : ℕ, {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < min T (n : ℝ≥0∞)}.indicator
          (fun s => min (g (b s.toNNReal)) (n : ℝ≥0∞)) s = 0 := fun n =>
        Set.indicator_of_notMem (fun h => hs ⟨h.1, h.2.trans_le (min_le_left _ _)⟩) _
      simp only [h0]
      exact tendsto_const_nhds

/-- The strong Markov property at a possibly infinite stopping time, with an
independent environment: on an event of the stopped sigma-algebra, a functional of the
shifted path averages to its mean under Brownian motion restarted at the stopped point. -/
theorem lintegral_lintegral_indicator_shift_stoppingTime
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (F : Ω → ContinuousPath ℂ → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) (x : ℂ)
    (τ : ContinuousPath ℂ → ℝ≥0∞)
    (hτ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := ℂ)) τ)
    (A : Set (ContinuousPath ℂ)) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫⁻ ω, ∫⁻ b, (A ∩ {b | τ b < ⊤}).indicator
        (fun b => F ω (ContinuousPath.shift (τ b).toNNReal b)) b ∂planarBrownianMotion x ∂P) =
      ∫⁻ b, (A ∩ {b | τ b < ⊤}).indicator
        (fun b => ∫⁻ ω, ∫⁻ b', F ω b' ∂planarBrownianMotion (b (τ b).toNNReal) ∂P) b
        ∂planarBrownianMotion x := by
  have hshift : Measurable (fun b : ContinuousPath ℂ => ContinuousPath.shift (τ b).toNNReal b) :=
    ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ
  have heval : Measurable (fun b : ContinuousPath ℂ => b (τ b).toNNReal) :=
    ContinuousPath.measurable_eval_untopD_stoppingTime τ hτ
  have hA' : MeasurableSet (A ∩ {b | τ b < ⊤}) :=
    hτ.measurableSpace_le _ (hA.inter (StoppingTime.measurableSet_stoppingTime_lt_top hτ))
  have hrestart :=
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
      x τ hτ A hA
  rw [← planarBrownianMotion_eq_continuousProcess] at hrestart
  change ((planarBrownianMotion x).restrict (A ∩ {b | τ b < ⊤})).map
      (fun b => ContinuousPath.shift (τ b).toNNReal b) =
    Kernel.comap planarBrownianMotion (fun b => b (τ b).toNNReal) heval ∘ₘ
      ((planarBrownianMotion x).restrict (A ∩ {b | τ b < ⊤})) at hrestart
  have hFω : ∀ ω, Measurable (F ω) := fun ω => hF.comp measurable_prodMk_left
  have hH : Measurable (fun a : Ω × ℂ => ∫⁻ b', F a.1 b' ∂planarBrownianMotion a.2) := by
    have h := Measurable.lintegral_kernel_prod_right
      (κ := Kernel.prodMkLeft Ω planarBrownianMotion) (f := fun a b' => F a.1 b')
      (show Measurable (fun p : (Ω × ℂ) × ContinuousPath ℂ => F p.1.1 p.2) from
        hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    simpa only [Kernel.prodMkLeft_apply] using h
  have hG : Measurable (fun p : Ω × ContinuousPath ℂ =>
      ∫⁻ b', F p.1 b' ∂planarBrownianMotion (p.2 (τ p.2).toNNReal)) :=
    hH.comp (measurable_fst.prodMk (heval.comp measurable_snd))
  have hω : ∀ ω, (∫⁻ b, (A ∩ {b | τ b < ⊤}).indicator
      (fun b => F ω (ContinuousPath.shift (τ b).toNNReal b)) b ∂planarBrownianMotion x) =
      ∫⁻ b in A ∩ {b | τ b < ⊤}, ∫⁻ b', F ω b' ∂planarBrownianMotion (b (τ b).toNNReal)
        ∂planarBrownianMotion x := by
    intro ω
    rw [lintegral_indicator hA', ← lintegral_map (hFω ω) hshift, hrestart,
      Measure.lintegral_bind (Kernel.aemeasurable _) (hFω ω).aemeasurable]
    simp only [Kernel.comap_apply]
  rw [lintegral_congr hω, lintegral_lintegral_swap
    (f := fun (ω : Ω) (b : ContinuousPath ℂ) =>
      ∫⁻ b', F ω b' ∂planarBrownianMotion (b (τ b).toNNReal)) hG.aemeasurable,
    lintegral_indicator hA']

/-- From any start, the occupation moment is at most the largest moment from a start
in `Q`, times the probability of reaching `Q` before leaving `D`. -/
theorem lintegral_pathOccupationBefore_rpow_le_entrance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (f : Ω → ℂ → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    {Q D : Set ℂ} (hQ : IsClosed Q) (hD : IsOpen D)
    (hfQ : ∀ ω z, z ∉ Q → f ω z = 0) (T : ℝ≥0∞) {q : ℝ} (hq : 0 < q) (S : ℝ≥0∞)
    (hS : ∀ y ∈ Q, (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω)
      (min (ContinuousPath.exitTime D b) T) b ^ q ∂planarBrownianMotion y ∂P) ≤ S) (x : ℂ) :
    (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q
      ∂planarBrownianMotion x ∂P) ≤
      S * planarBrownianMotion x {b | ∃ s : ℝ≥0, b s ∈ Q ∧
        (s : ℝ≥0∞) < ContinuousPath.exitTime D b} := by
  have hσ := ContinuousPath.isStoppingTime_exitTime Qᶜ hQ.isOpen_compl
  have hτD := ContinuousPath.isStoppingTime_exitTime D hD
  have hA : MeasurableSet[hσ.measurableSpace]
      {b : ContinuousPath ℂ | ContinuousPath.exitTime Qᶜ b < ContinuousPath.exitTime D b} := by
    have h := (IsStoppingTime.measurableSet_stopping_time_le hτD hσ).compl
    convert h using 1
    ext b
    show ContinuousPath.exitTime Qᶜ b < ContinuousPath.exitTime D b ↔
      ¬ (ContinuousPath.exitTime D b ≤ ContinuousPath.exitTime Qᶜ b)
    exact not_le.symm
  have hZ : Measurable (fun p : Ω × ContinuousPath ℂ =>
      pathOccupationBefore (f p.1) (min (ContinuousPath.exitTime D p.2) T) p.2) :=
    measurable_pathOccupationBefore (fun (p : Ω × ContinuousPath ℂ) z => f p.1 z)
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (fun p => min (ContinuousPath.exitTime D p.2) T)
      (((ContinuousPath.measurable_exitTime D hD).comp measurable_snd).min measurable_const)
      (fun p => p.2) measurable_snd
  have hR := lintegral_lintegral_indicator_shift_stoppingTime (P := P)
    (fun ω b => pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q)
    (hZ.pow_const q) x (ContinuousPath.exitTime Qᶜ) hσ _ hA
  have hAm : MeasurableSet ({b : ContinuousPath ℂ | ContinuousPath.exitTime Qᶜ b <
      ContinuousPath.exitTime D b} ∩ {b | ContinuousPath.exitTime Qᶜ b < ⊤}) :=
    (measurableSet_lt (ContinuousPath.measurable_exitTime Qᶜ hQ.isOpen_compl)
      (ContinuousPath.measurable_exitTime D hD)).inter
      (measurableSet_lt (ContinuousPath.measurable_exitTime Qᶜ hQ.isOpen_compl) measurable_const)
  calc (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q
        ∂planarBrownianMotion x ∂P)
      ≤ ∫⁻ ω, ∫⁻ b, ({b : ContinuousPath ℂ | ContinuousPath.exitTime Qᶜ b <
          ContinuousPath.exitTime D b} ∩ {b | ContinuousPath.exitTime Qᶜ b < ⊤}).indicator
          (fun b => pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D
            (ContinuousPath.shift (ContinuousPath.exitTime Qᶜ b).toNNReal b)) T)
            (ContinuousPath.shift (ContinuousPath.exitTime Qᶜ b).toNNReal b) ^ q) b
          ∂planarBrownianMotion x ∂P := by
        refine lintegral_mono fun ω => lintegral_mono fun b => ?_
        have hfω : Measurable (f ω) := hf.comp measurable_prodMk_left
        by_cases h : ContinuousPath.exitTime Qᶜ b < ContinuousPath.exitTime D b
        · have hfin : ContinuousPath.exitTime Qᶜ b < ⊤ := lt_of_lt_of_le h le_top
          have hb : b ∈ ({b : ContinuousPath ℂ | ContinuousPath.exitTime Qᶜ b <
              ContinuousPath.exitTime D b} ∩ {b | ContinuousPath.exitTime Qᶜ b < ⊤}) :=
            ⟨h, hfin⟩
          rw [Set.indicator_of_mem hb]
          refine ENNReal.rpow_le_rpow ?_ hq.le
          have h0 : pathOccupationBefore (f ω)
              (min ((ContinuousPath.exitTime Qᶜ b).toNNReal : ℝ≥0∞)
                (min (ContinuousPath.exitTime D b) T)) b = 0 := by
            apply pathOccupationBefore_eq_zero_of_le_exitTime_compl (hfQ ω)
            rw [ENNReal.coe_toNNReal hfin.ne]
            exact min_le_left _ _
          exact (pathOccupationBefore_le_add_shift hfω D T
            (ContinuousPath.exitTime Qᶜ b).toNNReal b).trans (le_of_eq (by rw [h0, zero_add]))
        · rw [pathOccupationBefore_eq_zero_of_le_exitTime_compl (hfQ ω) _ b
            ((min_le_left _ _).trans (not_lt.mp h)), ENNReal.zero_rpow_of_pos hq]
          exact zero_le
    _ = ∫⁻ b, ({b : ContinuousPath ℂ | ContinuousPath.exitTime Qᶜ b <
          ContinuousPath.exitTime D b} ∩ {b | ContinuousPath.exitTime Qᶜ b < ⊤}).indicator
          (fun b => ∫⁻ ω, ∫⁻ b', pathOccupationBefore (f ω)
            (min (ContinuousPath.exitTime D b') T) b' ^ q
            ∂planarBrownianMotion (b (ContinuousPath.exitTime Qᶜ b).toNNReal) ∂P) b
          ∂planarBrownianMotion x := hR
    _ ≤ ∫⁻ b, ({b : ContinuousPath ℂ | ContinuousPath.exitTime Qᶜ b <
          ContinuousPath.exitTime D b} ∩ {b | ContinuousPath.exitTime Qᶜ b < ⊤}).indicator
          (fun _ => S) b ∂planarBrownianMotion x := by
        refine lintegral_mono fun b => ?_
        by_cases hb : b ∈ ({b : ContinuousPath ℂ | ContinuousPath.exitTime Qᶜ b <
            ContinuousPath.exitTime D b} ∩ {b | ContinuousPath.exitTime Qᶜ b < ⊤})
        · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
          have hfin : ContinuousPath.exitTime Qᶜ b < ⊤ := hb.2
          apply hS
          have h := Section6.coordinate_exitTime_notMem hQ.isOpen_compl b hfin.ne
          simpa using h
        · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
    _ = S * planarBrownianMotion x ({b : ContinuousPath ℂ | ContinuousPath.exitTime Qᶜ b <
          ContinuousPath.exitTime D b} ∩ {b | ContinuousPath.exitTime Qᶜ b < ⊤}) :=
        lintegral_indicator_const hAm S
    _ ≤ _ := by
        refine mul_le_mul_right (measure_mono ?_) S
        rintro b ⟨h, hfin⟩
        have hfin' : ContinuousPath.exitTime Qᶜ b < ⊤ := hfin
        refine ⟨(ContinuousPath.exitTime Qᶜ b).toNNReal, ?_, ?_⟩
        · have h' := Section6.coordinate_exitTime_notMem hQ.isOpen_compl b hfin'.ne
          simpa using h'
        · rw [ENNReal.coe_toNNReal hfin'.ne]
          exact h

/-- The algebraic step of the return iteration: a finite `S` with
`S ^ (1 / q) ≤ M ^ (1 / q) + (S θ) ^ (1 / q)` and `θ < 1` is bounded by
`M / (1 - θ ^ (1 / q)) ^ q`. -/
theorem le_div_one_sub_rpow_of_le_add_rpow {S M θ : ℝ≥0∞} {q : ℝ} (hq : 0 < q)
    (hS : S ≠ ⊤) (hθ : θ < 1) (h : S ≤ (M ^ (1 / q) + (S * θ) ^ (1 / q)) ^ q) :
    S ≤ M / (1 - θ ^ (1 / q)) ^ q := by
  have hq' : 0 ≤ 1 / q := one_div_nonneg.mpr hq.le
  have hs_top : S ^ (1 / q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq' hS
  have ht : θ ^ (1 / q) < 1 := ENNReal.rpow_lt_one hθ (one_div_pos.mpr hq)
  have hSs : S = (S ^ (1 / q)) ^ q := by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  have h1 : S ^ (1 / q) ≤ M ^ (1 / q) + S ^ (1 / q) * θ ^ (1 / q) := by
    have h2 := ENNReal.rpow_le_rpow h hq'
    rwa [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ hq'] at h2
  have h3 : S ^ (1 / q) * (1 - θ ^ (1 / q)) ≤ M ^ (1 / q) := by
    rw [ENNReal.mul_sub (fun _ _ => hs_top), mul_one]
    exact tsub_le_iff_right.mpr h1
  have h4 : S ^ (1 / q) ≤ M ^ (1 / q) / (1 - θ ^ (1 / q)) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (tsub_pos_of_lt ht).ne')
      (Or.inl (ENNReal.sub_ne_top ENNReal.one_ne_top))]
    exact h3
  calc S = (S ^ (1 / q)) ^ q := hSs
    _ ≤ (M ^ (1 / q) / (1 - θ ^ (1 / q))) ^ q := ENNReal.rpow_le_rpow h4 hq.le
    _ = M / (1 - θ ^ (1 / q)) ^ q := by
      rw [ENNReal.div_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne',
        ENNReal.rpow_one]

/-- Return iteration for a bounded density and a finite time horizon `T`. -/
theorem lintegral_pathOccupationBefore_min_rpow_le_of_return
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (f : Ω → ℂ → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    {Q U D : Set ℂ} (hQ : IsClosed Q) (hU : IsOpen U) (hD : IsOpen D)
    (hfQ : ∀ ω z, z ∉ Q → f ω z = 0) {c : ℝ≥0∞} (hc : c ≠ ⊤) (hfc : ∀ ω z, f ω z ≤ c)
    {T : ℝ≥0∞} (hT : T ≠ ⊤) {q : ℝ} (hq : 1 ≤ q) {θ M : ℝ≥0∞} (hθ : θ < 1)
    (hret : ∀ y, y ∉ U → planarBrownianMotion y {b | ∃ s : ℝ≥0, b s ∈ Q ∧
      (s : ℝ≥0∞) < ContinuousPath.exitTime D b} ≤ θ)
    (hM : ∀ y ∈ Q, (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω)
      (min (ContinuousPath.exitTime U b) (min (ContinuousPath.exitTime D b) T)) b ^ q
        ∂planarBrownianMotion y ∂P) ≤ M) (x : ℂ) :
    (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q
      ∂planarBrownianMotion x ∂P) ≤ M / (1 - θ ^ (1 / q)) ^ q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq' : 0 ≤ 1 / q := one_div_nonneg.mpr hq0.le
  have hρ := ContinuousPath.isStoppingTime_exitTime U hU
  have hZ : Measurable (fun p : Ω × ContinuousPath ℂ =>
      pathOccupationBefore (f p.1) (min (ContinuousPath.exitTime D p.2) T) p.2) :=
    measurable_pathOccupationBefore (fun (p : Ω × ContinuousPath ℂ) z => f p.1 z)
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (fun p => min (ContinuousPath.exitTime D p.2) T)
      (((ContinuousPath.measurable_exitTime D hD).comp measurable_snd).min measurable_const)
      (fun p => p.2) measurable_snd
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ≥0∞, S = ⨆ y ∈ Q, ∫⁻ ω, ∫⁻ b,
      pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q
        ∂planarBrownianMotion y ∂P := ⟨_, rfl⟩
  have hSle : ∀ y ∈ Q, (∫⁻ ω, ∫⁻ b,
      pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q
        ∂planarBrownianMotion y ∂P) ≤ S := by
    intro y hy
    rw [hSdef]
    exact le_iSup₂ (f := fun y (_ : y ∈ Q) => ∫⁻ ω, ∫⁻ b,
      pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q
        ∂planarBrownianMotion y ∂P) y hy
  have hSfin : S ≠ ⊤ := by
    have hC : (c * T.toNNReal) ^ q * P univ < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le
        (ENNReal.mul_ne_top hc ENNReal.coe_ne_top)) (measure_lt_top P univ)
    refine (lt_of_le_of_lt ?_ hC).ne
    rw [hSdef]
    refine iSup₂_le fun y _ => ?_
    calc (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q
          ∂planarBrownianMotion y ∂P)
        ≤ ∫⁻ ω, ∫⁻ b, (c * T.toNNReal) ^ q ∂planarBrownianMotion y ∂P := by
          refine lintegral_mono fun ω => lintegral_mono fun b => ?_
          refine ENNReal.rpow_le_rpow (pathOccupationBefore_le_mul (hfc ω) ?_ b) hq0.le
          rw [ENNReal.coe_toNNReal hT]
          exact min_le_right _ _
      _ = (c * T.toNNReal) ^ q * P univ := by
          simp only [lintegral_const, measure_univ, mul_one]
  have hent : ∀ y, y ∉ U → (∫⁻ ω, ∫⁻ b,
      pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q
        ∂planarBrownianMotion y ∂P) ≤ S * θ := fun y hy =>
    (lintegral_pathOccupationBefore_rpow_le_entrance f hf hQ hD hfQ T hq0 S hSle y).trans
      (mul_le_mul_right (hret y hy) S)
  have hshiftU : Measurable (fun b : ContinuousPath ℂ =>
      ContinuousPath.shift (ContinuousPath.exitTime U b).toNNReal b) :=
    ContinuousPath.measurable_shift_untopD_stoppingTime (ContinuousPath.exitTime U) hρ
  have hexit : ∀ y ∈ Q, (∫⁻ ω, ∫⁻ b,
      pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q
        ∂planarBrownianMotion y ∂P) ≤ (M ^ (1 / q) + (S * θ) ^ (1 / q)) ^ q := by
    intro y hy
    let Y : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun p => pathOccupationBefore (f p.1)
      (min (ContinuousPath.exitTime U p.2) (min (ContinuousPath.exitTime D p.2) T)) p.2
    let W : Ω × ContinuousPath ℂ → ℝ≥0∞ :=
      {p : Ω × ContinuousPath ℂ | ContinuousPath.exitTime U p.2 < ⊤}.indicator
        (fun p => pathOccupationBefore (f p.1) (min (ContinuousPath.exitTime D
          (ContinuousPath.shift (ContinuousPath.exitTime U p.2).toNNReal p.2)) T)
          (ContinuousPath.shift (ContinuousPath.exitTime U p.2).toNNReal p.2))
    have hY : Measurable Y := measurable_pathOccupationBefore (fun (p : Ω × ContinuousPath ℂ) z => f p.1 z)
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (fun p => min (ContinuousPath.exitTime U p.2) (min (ContinuousPath.exitTime D p.2) T))
      (((ContinuousPath.measurable_exitTime U hU).comp measurable_snd).min
        (((ContinuousPath.measurable_exitTime D hD).comp measurable_snd).min measurable_const))
      (fun p => p.2) measurable_snd
    have hW : Measurable W :=
      (hZ.comp (measurable_fst.prodMk (hshiftU.comp measurable_snd))).indicator
        (measurableSet_lt ((ContinuousPath.measurable_exitTime U hU).comp measurable_snd)
          measurable_const)
    have hpath : ∀ ω b, pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ≤
        Y (ω, b) + W (ω, b) := by
      intro ω b
      have hfω : Measurable (f ω) := hf.comp measurable_prodMk_left
      by_cases h : ContinuousPath.exitTime U b < ⊤
      · have hW' : W (ω, b) = pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D
            (ContinuousPath.shift (ContinuousPath.exitTime U b).toNNReal b)) T)
            (ContinuousPath.shift (ContinuousPath.exitTime U b).toNNReal b) :=
          Set.indicator_of_mem (show (ω, b) ∈ {p : Ω × ContinuousPath ℂ |
            ContinuousPath.exitTime U p.2 < ⊤} from h) _
        have hsplit := pathOccupationBefore_le_add_shift hfω D T
          (ContinuousPath.exitTime U b).toNNReal b
        rw [ENNReal.coe_toNNReal h.ne] at hsplit
        rw [hW']
        exact hsplit
      · have hW' : W (ω, b) = 0 := Set.indicator_of_notMem (show (ω, b) ∉
          {p : Ω × ContinuousPath ℂ | ContinuousPath.exitTime U p.2 < ⊤} from h) _
        have htop : ContinuousPath.exitTime U b = ⊤ := not_lt_top_iff.mp h
        rw [hW', add_zero]
        refine le_of_eq ?_
        show _ = pathOccupationBefore (f ω)
          (min (ContinuousPath.exitTime U b) (min (ContinuousPath.exitTime D b) T)) b
        rw [htop, min_top_left]
    have hmink := ENNReal.lintegral_Lp_add_le (μ := P.prod (planarBrownianMotion y))
      hY.aemeasurable hW.aemeasurable hq
    have hYM : (∫⁻ p, Y p ^ q ∂(P.prod (planarBrownianMotion y))) ≤ M := by
      rw [lintegral_prod _ (hY.pow_const q).aemeasurable]
      exact hM y hy
    have hWS : (∫⁻ p, W p ^ q ∂(P.prod (planarBrownianMotion y))) ≤ S * θ := by
      have hR := lintegral_lintegral_indicator_shift_stoppingTime (P := P)
        (fun ω b => pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q)
        (hZ.pow_const q) y (ContinuousPath.exitTime U) hρ univ
        (@MeasurableSet.univ _ hρ.measurableSpace)
      have hset : MeasurableSet (univ ∩ {b : ContinuousPath ℂ |
          ContinuousPath.exitTime U b < ⊤}) :=
        MeasurableSet.univ.inter
          (measurableSet_lt (ContinuousPath.measurable_exitTime U hU) measurable_const)
      rw [lintegral_prod _ (hW.pow_const q).aemeasurable]
      calc (∫⁻ ω, ∫⁻ b, W (ω, b) ^ q ∂planarBrownianMotion y ∂P)
          = ∫⁻ ω, ∫⁻ b, (univ ∩ {b : ContinuousPath ℂ |
              ContinuousPath.exitTime U b < ⊤}).indicator (fun b =>
              pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D
                (ContinuousPath.shift (ContinuousPath.exitTime U b).toNNReal b)) T)
                (ContinuousPath.shift (ContinuousPath.exitTime U b).toNNReal b) ^ q) b
              ∂planarBrownianMotion y ∂P := by
            refine lintegral_congr fun ω => lintegral_congr fun b => ?_
            by_cases h : ContinuousPath.exitTime U b < ⊤
            · rw [Set.indicator_of_mem (show b ∈ (univ ∩ {b : ContinuousPath ℂ |
                ContinuousPath.exitTime U b < ⊤}) from ⟨trivial, h⟩)]
              rw [show W (ω, b) = _ from Set.indicator_of_mem (show (ω, b) ∈
                {p : Ω × ContinuousPath ℂ | ContinuousPath.exitTime U p.2 < ⊤} from h) _]
            · rw [Set.indicator_of_notMem (show b ∉ (univ ∩ {b : ContinuousPath ℂ |
                ContinuousPath.exitTime U b < ⊤}) from fun hb => h hb.2)]
              rw [show W (ω, b) = 0 from Set.indicator_of_notMem (show (ω, b) ∉
                {p : Ω × ContinuousPath ℂ | ContinuousPath.exitTime U p.2 < ⊤} from h) _,
                ENNReal.zero_rpow_of_pos hq0]
        _ = _ := hR
        _ ≤ ∫⁻ b, (univ ∩ {b : ContinuousPath ℂ |
              ContinuousPath.exitTime U b < ⊤}).indicator (fun _ => S * θ) b
              ∂planarBrownianMotion y := by
            refine lintegral_mono fun b => ?_
            by_cases hb : b ∈ (univ ∩ {b : ContinuousPath ℂ | ContinuousPath.exitTime U b < ⊤})
            · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
              have hfin : ContinuousPath.exitTime U b < ⊤ := hb.2
              exact hent _ (Section6.coordinate_exitTime_notMem hU b hfin.ne)
            · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
        _ = S * θ * planarBrownianMotion y (univ ∩ {b : ContinuousPath ℂ |
              ContinuousPath.exitTime U b < ⊤}) := lintegral_indicator_const hset _
        _ ≤ S * θ * 1 := mul_le_mul_right prob_le_one _
        _ = S * θ := mul_one _
    calc (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (min (ContinuousPath.exitTime D b) T) b ^ q
          ∂planarBrownianMotion y ∂P)
        = ∫⁻ p, pathOccupationBefore (f p.1) (min (ContinuousPath.exitTime D p.2) T) p.2 ^ q
            ∂(P.prod (planarBrownianMotion y)) :=
          (lintegral_prod _ (hZ.pow_const q).aemeasurable).symm
      _ ≤ ∫⁻ p, (Y + W) p ^ q ∂(P.prod (planarBrownianMotion y)) :=
          lintegral_mono fun p => ENNReal.rpow_le_rpow (hpath p.1 p.2) hq0.le
      _ = ((∫⁻ p, (Y + W) p ^ q ∂(P.prod (planarBrownianMotion y))) ^ (1 / q)) ^ q := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
      _ ≤ ((∫⁻ p, Y p ^ q ∂(P.prod (planarBrownianMotion y))) ^ (1 / q) +
            (∫⁻ p, W p ^ q ∂(P.prod (planarBrownianMotion y))) ^ (1 / q)) ^ q :=
          ENNReal.rpow_le_rpow hmink hq0.le
      _ ≤ (M ^ (1 / q) + (S * θ) ^ (1 / q)) ^ q :=
          ENNReal.rpow_le_rpow (add_le_add (ENNReal.rpow_le_rpow hYM hq')
            (ENNReal.rpow_le_rpow hWS hq')) hq0.le
  have hSb : S ≤ (M ^ (1 / q) + (S * θ) ^ (1 / q)) ^ q := by
    rw [hSdef] at hexit ⊢
    exact iSup₂_le hexit
  have hSM := le_div_one_sub_rpow_of_le_add_rpow hq0 hSfin hθ hSb
  calc _ ≤ S * planarBrownianMotion x {b | ∃ s : ℝ≥0, b s ∈ Q ∧
        (s : ℝ≥0∞) < ContinuousPath.exitTime D b} :=
        lintegral_pathOccupationBefore_rpow_le_entrance f hf hQ hD hfQ T hq0 S hSle x
    _ ≤ S * 1 := mul_le_mul_right prob_le_one _
    _ = S := mul_one S
    _ ≤ _ := hSM

/-- **Return iteration for Brownian occupation moments.** Let a density `f ω`, jointly
measurable in an environment `ω` with a finite law `P`, vanish off a closed set `Q`.
Suppose that every start outside an open set `U` reaches `Q` before leaving the open
set `D` with probability at most `θ < 1`, and that from every start in `Q` the
`q`-th moment of the occupation until the first exit from `U` or `D` is at most `M`,
with `q ≥ 1`. Then from every start the `q`-th moment of the occupation before the
exit from `D` is at most `M / (1 - θ ^ (1 / q)) ^ q`. -/
theorem lintegral_pathOccupationBefore_rpow_le_of_return
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (f : Ω → ℂ → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    {Q U D : Set ℂ} (hQ : IsClosed Q) (hU : IsOpen U) (hD : IsOpen D)
    (hfQ : ∀ ω z, z ∉ Q → f ω z = 0) {q : ℝ} (hq : 1 ≤ q) {θ M : ℝ≥0∞} (hθ : θ < 1)
    (hret : ∀ y, y ∉ U → planarBrownianMotion y {b | ∃ s : ℝ≥0, b s ∈ Q ∧
      (s : ℝ≥0∞) < ContinuousPath.exitTime D b} ≤ θ)
    (hM : ∀ y ∈ Q, (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω)
      (min (ContinuousPath.exitTime U b) (ContinuousPath.exitTime D b)) b ^ q
        ∂planarBrownianMotion y ∂P) ≤ M) (x : ℂ) :
    (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (ContinuousPath.exitTime D b) b ^ q
      ∂planarBrownianMotion x ∂P) ≤ M / (1 - θ ^ (1 / q)) ^ q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hbound : ∀ n : ℕ, (∫⁻ ω, ∫⁻ b, pathOccupationBefore (fun z => min (f ω z) (n : ℝ≥0∞))
      (min (ContinuousPath.exitTime D b) (n : ℝ≥0∞)) b ^ q ∂planarBrownianMotion x ∂P) ≤
      M / (1 - θ ^ (1 / q)) ^ q := by
    intro n
    refine lintegral_pathOccupationBefore_min_rpow_le_of_return
      (fun ω z => min (f ω z) (n : ℝ≥0∞)) (hf.min measurable_const) hQ hU hD
      (fun ω z hz => by rw [hfQ ω z hz]; exact min_eq_left zero_le)
      (ENNReal.natCast_ne_top n) (fun ω z => min_le_right _ _) (ENNReal.natCast_ne_top n)
      hq hθ hret ?_ x
    intro y hy
    refine le_trans ?_ (hM y hy)
    refine lintegral_mono fun ω => lintegral_mono fun b => ENNReal.rpow_le_rpow ?_ hq0.le
    exact pathOccupationBefore_mono (fun z => min_le_left _ _)
      (min_le_min_left _ (min_le_left _ _)) b
  have hZn : ∀ n : ℕ, Measurable (fun p : Ω × ContinuousPath ℂ =>
      pathOccupationBefore (fun z => min (f p.1 z) (n : ℝ≥0∞))
        (min (ContinuousPath.exitTime D p.2) (n : ℝ≥0∞)) p.2) := fun n =>
    measurable_pathOccupationBefore (fun (p : Ω × ContinuousPath ℂ) z => min (f p.1 z) (n : ℝ≥0∞))
      ((hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).min
        measurable_const)
      (fun p => min (ContinuousPath.exitTime D p.2) (n : ℝ≥0∞))
      (((ContinuousPath.measurable_exitTime D hD).comp measurable_snd).min measurable_const)
      (fun p => p.2) measurable_snd
  have hmono : ∀ ω b, Monotone fun n : ℕ =>
      pathOccupationBefore (fun z => min (f ω z) (n : ℝ≥0∞))
        (min (ContinuousPath.exitTime D b) (n : ℝ≥0∞)) b := fun ω b n m hnm =>
    pathOccupationBefore_mono (fun z => min_le_min_left _ (Nat.cast_le.mpr hnm))
      (min_le_min_left _ (Nat.cast_le.mpr hnm)) b
  have hlim : ∀ ω b, Tendsto (fun n : ℕ =>
      pathOccupationBefore (fun z => min (f ω z) (n : ℝ≥0∞))
        (min (ContinuousPath.exitTime D b) (n : ℝ≥0∞)) b ^ q) atTop
      (𝓝 (pathOccupationBefore (f ω) (ContinuousPath.exitTime D b) b ^ q)) := fun ω b =>
    (ENNReal.continuous_rpow_const.tendsto _).comp
      (tendsto_pathOccupationBefore_min (f ω) (hf.comp measurable_prodMk_left) _ b)
  have hinner : ∀ ω, Tendsto (fun n : ℕ => ∫⁻ b,
      pathOccupationBefore (fun z => min (f ω z) (n : ℝ≥0∞))
        (min (ContinuousPath.exitTime D b) (n : ℝ≥0∞)) b ^ q ∂planarBrownianMotion x) atTop
      (𝓝 (∫⁻ b, pathOccupationBefore (f ω) (ContinuousPath.exitTime D b) b ^ q
        ∂planarBrownianMotion x)) := fun ω =>
    lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (((hZn n).comp measurable_prodMk_left).pow_const q).aemeasurable)
      (Filter.Eventually.of_forall fun b n m hnm =>
        ENNReal.rpow_le_rpow (hmono ω b hnm) hq0.le)
      (Filter.Eventually.of_forall fun b => hlim ω b)
  have houter : Tendsto (fun n : ℕ => ∫⁻ ω, ∫⁻ b,
      pathOccupationBefore (fun z => min (f ω z) (n : ℝ≥0∞))
        (min (ContinuousPath.exitTime D b) (n : ℝ≥0∞)) b ^ q ∂planarBrownianMotion x ∂P) atTop
      (𝓝 (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (ContinuousPath.exitTime D b) b ^ q
        ∂planarBrownianMotion x ∂P)) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (((hZn n).pow_const q).lintegral_prod_right'
        (ν := planarBrownianMotion x)).aemeasurable)
      (Filter.Eventually.of_forall fun ω n m hnm => lintegral_mono fun b =>
        ENNReal.rpow_le_rpow (hmono ω b hnm) hq0.le)
      (Filter.Eventually.of_forall hinner)
  exact le_of_tendsto' houter hbound

end HarmonicBalls
