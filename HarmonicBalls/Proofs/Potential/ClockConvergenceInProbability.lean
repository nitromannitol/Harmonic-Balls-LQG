import HarmonicBalls.Proofs.Potential.BrownianOriginOccupationDensity

/-! # Convergence in probability of clocks with a small inner part

Suppose approximating clocks split as `A j = Y n j + Z n j` for every cutoff `n`, where the
outer parts `Y n j` converge almost surely and locally uniformly to continuous limits `G n`
as `j → ∞`, increase in `n` with nondecreasing differences in time, and the inner parts
`Z n j ≥ 0` are nondecreasing in time with expectation at time `T` at most `ε_T n → 0`,
uniformly in `j`. Then the limits `G n` increase to a limit `F` and the clocks `A j`
converge to `F` in probability, uniformly on every interval `[0, T]`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Every real number is a limit of rationals. -/
theorem exists_rat_seq_tendsto_real (t : ℝ) :
    ∃ r : ℕ → ℚ, Tendsto (fun n => (r n : ℝ)) atTop (𝓝 t) := by
  have h (n : ℕ) : ∃ q : ℚ, t - 1/((n : ℝ)+1) < q ∧ (q : ℝ) < t + 1/((n : ℝ)+1) := by
    have : (0 : ℝ) < 1/((n : ℝ)+1) := by positivity
    exact exists_rat_btwn (by linarith)
  choose r hr using h
  refine ⟨r, ?_⟩
  have h0 : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun n : ℕ => t - 1/((n : ℝ)+1)) atTop (𝓝 t) := by
    have := (tendsto_const_nhds (x := t)).sub h0
    rwa [sub_zero] at this
  have hu : Tendsto (fun n : ℕ => t + 1/((n : ℝ)+1)) atTop (𝓝 t) := by
    have := (tendsto_const_nhds (x := t)).add h0
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun n => (hr n).1.le)
    (fun n => (hr n).2.le)

/-- The supremum over times in `[0, T]` of the absolute value of a continuous function is
attained along the rational times clipped at `T`. -/
theorem ofReal_abs_le_iSup_rat {f : ℝ≥0 → ℝ} (hf : Continuous f) {T t : ℝ≥0}
    (ht : t ≤ T) :
    ENNReal.ofReal |f t| ≤ ⨆ r : ℚ, ENNReal.ofReal |f (min (Real.toNNReal r) T)| := by
  obtain ⟨r, hr⟩ := exists_rat_seq_tendsto_real (t : ℝ)
  have hτ : Tendsto (fun n => min (Real.toNNReal (r n)) T) atTop (𝓝 t) := by
    have h1 : Tendsto (fun n => Real.toNNReal (r n)) atTop (𝓝 (Real.toNNReal t)) :=
      (continuous_real_toNNReal.tendsto _).comp hr
    have h2 := h1.min (tendsto_const_nhds (x := T))
    rwa [Real.toNNReal_coe, min_eq_left ht] at h2
  have hcf : Continuous (fun s => ENNReal.ofReal |f s|) :=
    ENNReal.continuous_ofReal.comp hf.abs
  exact le_of_tendsto' ((hcf.tendsto t).comp hτ) (fun n =>
    le_iSup (fun r : ℚ => ENNReal.ofReal |f (min (Real.toNNReal r) T)|) (r n))

/-- **Clocks with a small inner part converge in probability.** -/
theorem exists_tendsto_measure_of_split_inner_small
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (A : ℕ → X → ℝ≥0 → ℝ) (Y Z : ℕ → ℕ → X → ℝ≥0 → ℝ) (G : ℕ → X → ℝ≥0 → ℝ)
    (hsplit : ∀ n j x t, A j x t = Y n j x t + Z n j x t)
    (hZ0 : ∀ n j x t, 0 ≤ Z n j x t) (hZmono : ∀ n j x, Monotone (Z n j x))
    (hYle : ∀ n m j x t, n ≤ m → Y n j x t ≤ Y m j x t)
    (hYdiff : ∀ n m j x, n ≤ m → Monotone (fun t => Y m j x t - Y n j x t))
    (hYc : ∀ n j x, Continuous (Y n j x)) (hGc : ∀ n x, Continuous (G n x))
    (hYm : ∀ n j t, Measurable (fun x => Y n j x t)) (hGm : ∀ n t, Measurable (fun x => G n x t))
    (hZm : ∀ n j t, Measurable (fun x => Z n j x t))
    (hlim : ∀ n, ∀ᵐ x ∂μ, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t ≤ T,
      |Y n j x t - G n x t| < η)
    (hZbound : ∀ T : ℝ≥0, ∃ ε : ℕ → ℝ≥0∞, Tendsto ε atTop (𝓝 0) ∧
      ∀ n j, ∫⁻ x, ENNReal.ofReal (Z n j x T) ∂μ ≤ ε n) :
    ∃ F : X → ℝ≥0 → ℝ, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      Tendsto (fun j => μ {x | ∃ t ≤ T, η ≤ |A j x t - F x t|}) atTop (𝓝 0) := by
  classical
  have hlimall : ∀ᵐ x ∂μ, ∀ n, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t ≤ T,
      |Y n j x t - G n x t| < η := ae_all_iff.mpr hlim
  -- pointwise convergence of the outer parts
  have hpt : ∀ x, (∀ n, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t ≤ T,
      |Y n j x t - G n x t| < η) → ∀ n t, Tendsto (fun j => Y n j x t) atTop (𝓝 (G n x t)) := by
    intro x hx n t
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨J, hJ⟩ := (hx n t η hη).exists_forall_of_atTop
    exact ⟨J, fun j hj => by rw [Real.dist_eq]; exact hJ j hj t le_rfl⟩
  -- the inner parts control the increments of the outer limits
  have hYZ : ∀ n m j x t, n ≤ m → Y m j x t - Y n j x t ≤ Z n j x t := by
    intro n m j x t _
    have h1 := hsplit n j x t
    have h2 := hsplit m j x t
    have h3 := hZ0 m j x t
    linarith
  have hord : ∀ x, (∀ n, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t ≤ T,
      |Y n j x t - G n x t| < η) → ∀ n m, n ≤ m →
      (∀ t, G n x t ≤ G m x t) ∧ Monotone (fun t => G m x t - G n x t) ∧
      ∀ t, ENNReal.ofReal (G m x t - G n x t) ≤
        liminf (fun j => ENNReal.ofReal (Z n j x t)) atTop := by
    intro x hx n m hnm
    have hc := hpt x hx
    refine ⟨fun t => le_of_tendsto_of_tendsto' (hc n t) (hc m t) (fun j => hYle n m j x t hnm),
      fun s t hst => ?_, fun t => ?_⟩
    · exact le_of_tendsto_of_tendsto' ((hc m s).sub (hc n s)) ((hc m t).sub (hc n t))
        (fun j => hYdiff n m j x hnm hst)
    · have hlim' : Tendsto (fun j => ENNReal.ofReal (Y m j x t - Y n j x t)) atTop
          (𝓝 (ENNReal.ofReal (G m x t - G n x t))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp ((hc m t).sub (hc n t))
      rw [← hlim'.liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall fun j =>
        ENNReal.ofReal_le_ofReal (hYZ n m j x t hnm))
  -- integral control of the increments
  have hint : ∀ T : ℝ≥0, ∀ (ε : ℕ → ℝ≥0∞), (∀ n j, ∫⁻ x, ENNReal.ofReal (Z n j x T) ∂μ ≤ ε n) →
      ∀ n m, n ≤ m → ∫⁻ x, ENNReal.ofReal (G m x T - G n x T) ∂μ ≤ ε n := by
    intro T ε hε n m hnm
    calc ∫⁻ x, ENNReal.ofReal (G m x T - G n x T) ∂μ
        ≤ ∫⁻ x, liminf (fun j => ENNReal.ofReal (Z n j x T)) atTop ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hlimall] with x hx
          exact (hord x hx n m hnm).2.2 T
      _ ≤ liminf (fun j => ∫⁻ x, ENNReal.ofReal (Z n j x T) ∂μ) atTop :=
          lintegral_liminf_le fun j => (hZm n j T).ennreal_ofReal
      _ ≤ ε n := liminf_le_of_le (by isBoundedDefault) fun b hb => by
          obtain ⟨J, hJ⟩ := hb.exists_forall_of_atTop
          exact (hJ J le_rfl).trans (hε n J)
  -- boundedness of the outer limits along integer horizons
  have hfin : ∀ N : ℕ, ∃ n, ∀ᵐ x ∂μ, (⨆ m, ENNReal.ofReal (G (n + m) x N - G n x N)) < ⊤ := by
    intro N
    obtain ⟨ε, hε0, hε⟩ := hZbound N
    obtain ⟨n, hn⟩ := (hε0.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).exists
    refine ⟨n, ae_lt_top' ?_ ?_⟩
    · exact (Measurable.iSup fun m => ((hGm _ _).sub (hGm _ _)).ennreal_ofReal).aemeasurable
    · refine ne_top_of_le_ne_top (b := ε n) (ne_top_of_lt (hn.trans ENNReal.one_lt_top)) ?_
      rw [lintegral_iSup' (f := fun (m : ℕ) (x : X) => ENNReal.ofReal (G (n + m) x N - G n x N))
        (fun m => ((hGm _ _).sub (hGm _ _)).ennreal_ofReal.aemeasurable) ?_]
      · exact iSup_le fun m => hint N ε hε n (n + m) (Nat.le_add_right n m)
      · filter_upwards [hlimall] with x hx
        intro m₁ m₂ hm
        apply ENNReal.ofReal_le_ofReal
        have := (hord x hx (n + m₁) (n + m₂) (by omega)).1 N
        linarith
  choose nN hnN using hfin
  have hgood : ∀ᵐ x ∂μ, ∀ N : ℕ, (⨆ m, ENNReal.ofReal (G (nN N + m) x N - G (nN N) x N)) < ⊤ :=
    ae_all_iff.mpr hnN
  -- the limit
  let F : X → ℝ≥0 → ℝ := fun x t => limUnder atTop (fun m => G m x t)
  have hconv : ∀ x, (∀ n, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t ≤ T,
      |Y n j x t - G n x t| < η) →
      (∀ N : ℕ, (⨆ m, ENNReal.ofReal (G (nN N + m) x N - G (nN N) x N)) < ⊤) →
      ∀ t, Tendsto (fun m => G m x t) atTop (𝓝 (F x t)) := by
    intro x hx hb t
    obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
    have hmono : Monotone (fun m => G m x t) := monotone_nat_of_le_succ fun m =>
      (hord x hx m (m + 1) (Nat.le_succ m)).1 t
    have hbdd : BddAbove (Set.range (fun m => G m x t)) := by
      obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, (⨆ m, ENNReal.ofReal (G (nN N + m) x N - G (nN N) x N)) ≤ C :=
        ⟨_, (ENNReal.coe_toNNReal (hb N).ne).symm.le⟩
      refine ⟨G (nN N) x t + C, ?_⟩
      rintro _ ⟨m, rfl⟩
      have htN : t ≤ (N : ℝ≥0) := by exact_mod_cast hN
      have h1 : G m x t ≤ G (nN N + m) x t := (hord x hx m (nN N + m) (Nat.le_add_left m _)).1 t
      have h2 := (hord x hx (nN N) (nN N + m) (Nat.le_add_right _ m)).2.1 htN
      have h3 : ENNReal.ofReal (G (nN N + m) x N - G (nN N) x N) ≤ C :=
        (le_iSup (fun m => ENNReal.ofReal (G (nN N + m) x N - G (nN N) x N)) m).trans hC
      have h4 : G (nN N + m) x N - G (nN N) x N ≤ C := by
        have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).mp h3
        simpa using this
      simp only at h2
      linarith
    exact tendsto_nhds_limUnder ⟨_, tendsto_atTop_ciSup hmono hbdd⟩
  refine ⟨F, fun T η hη => ?_⟩
  obtain ⟨ε, hε0, hε⟩ := hZbound T
  have hη3 : 0 < η / 3 := by positivity
  set δ : ℝ≥0∞ := ENNReal.ofReal (η / 3) with hδdef
  have hδ0 : δ ≠ 0 := by
    rw [hδdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hη3
  have hδtop : δ ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the tail of the limit
  have hFm : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (F x T - G n x T)) μ := by
    intro n
    refine aemeasurable_of_tendsto_metrizable_ae'
      (f := fun m x => ENNReal.ofReal (G m x T - G n x T))
      (fun m => ((hGm m T).sub (hGm n T)).ennreal_ofReal.aemeasurable) ?_
    filter_upwards [hlimall, hgood] with x hx hb
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((hconv x hx hb T).sub tendsto_const_nhds)
  have hFtail : ∀ n, ∫⁻ x, ENNReal.ofReal (F x T - G n x T) ∂μ ≤ ε n := by
    intro n
    have hae : ∀ᵐ x ∂μ, ENNReal.ofReal (F x T - G n x T) =
        liminf (fun m => ENNReal.ofReal (G m x T - G n x T)) atTop := by
      filter_upwards [hlimall, hgood] with x hx hb
      exact ((ENNReal.continuous_ofReal.tendsto _).comp
        ((hconv x hx hb T).sub tendsto_const_nhds)).liminf_eq.symm
    rw [lintegral_congr_ae hae]
    calc _ ≤ liminf (fun m => ∫⁻ x, ENNReal.ofReal (G m x T - G n x T) ∂μ) atTop :=
          lintegral_liminf_le fun m => ((hGm m T).sub (hGm n T)).ennreal_ofReal
      _ ≤ ε n := liminf_le_of_le (by isBoundedDefault) fun b hb => by
          obtain ⟨J, hJ⟩ := hb.exists_forall_of_atTop
          exact (hJ (max J n) (le_max_left _ _)).trans
            (hint T ε hε n (max J n) (le_max_right _ _))
  -- the outer part converges uniformly on `[0, T]` along rational times
  let U : ℕ → ℕ → X → ℝ≥0∞ := fun n j x => ⨆ r : ℚ,
    ENNReal.ofReal |Y n j x (min (Real.toNNReal r) T) - G n x (min (Real.toNNReal r) T)|
  have hUm : ∀ n j, Measurable (U n j) := fun n j =>
    Measurable.iSup fun r => (((hYm n j _).sub (hGm n _)).abs).ennreal_ofReal
  have hU : ∀ n, Tendsto (fun j => μ {x | δ ≤ U n j x}) atTop (𝓝 0) := by
    intro n
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := μ)
      (A := (∅ : Set X)) (L := atTop) (As := fun j => {x | δ ≤ U n j x}) MeasurableSet.empty
      (fun j => measurableSet_le measurable_const (hUm n j)) ?_
    · simpa using h
    filter_upwards [hlimall] with x hx
    filter_upwards [hx n T (η / 6) (by positivity)] with j hj
    refine ⟨fun hjS => ?_, fun h => (Set.notMem_empty x h).elim⟩
    have hg : U n j x ≤ ENNReal.ofReal (η / 6) :=
      iSup_le fun r => ENNReal.ofReal_le_ofReal (hj _ (min_le_right _ _)).le
    have hc := (show δ ≤ U n j x from hjS).trans hg
    rw [hδdef, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hc
    linarith
  -- splitting the deviation
  have hsub : ∀ n j, ∀ᵐ x ∂μ, x ∈ {x | ∃ t ≤ T, η ≤ |A j x t - F x t|} →
      x ∈ {x | δ ≤ U n j x} ∪ {x | δ ≤ ENNReal.ofReal (Z n j x T)} ∪
        {x | δ ≤ ENNReal.ofReal (F x T - G n x T)} := by
    intro n j
    filter_upwards [hlimall, hgood] with x hx hb
    rintro ⟨t, ht, hle⟩
    have hFG : G n x t ≤ F x t := ge_of_tendsto (hconv x hx hb t)
      (eventually_atTop.mpr ⟨n, fun m hm => (hord x hx n m hm).1 t⟩)
    have hFGT : F x t - G n x t ≤ F x T - G n x T :=
      le_of_tendsto_of_tendsto ((hconv x hx hb t).sub tendsto_const_nhds)
        ((hconv x hx hb T).sub tendsto_const_nhds)
        (eventually_atTop.mpr ⟨n, fun m hm => (hord x hx n m hm).2.1 ht⟩)
    have hU1 : ENNReal.ofReal |Y n j x t - G n x t| ≤ U n j x :=
      ofReal_abs_le_iSup_rat ((hYc n j x).sub (hGc n x)) ht
    have hZt : Z n j x t ≤ Z n j x T := hZmono n j x ht
    have h0 := hZ0 n j x t
    have hdec : |A j x t - F x t| ≤
        |Y n j x t - G n x t| + Z n j x T + (F x T - G n x T) := by
      rw [hsplit n j x t, show Y n j x t + Z n j x t - F x t =
        (Y n j x t - G n x t) + (Z n j x t - (F x t - G n x t)) by ring]
      have h2 : |Z n j x t - (F x t - G n x t)| ≤ Z n j x t + (F x t - G n x t) :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      calc |(Y n j x t - G n x t) + (Z n j x t - (F x t - G n x t))|
          ≤ |Y n j x t - G n x t| + |Z n j x t - (F x t - G n x t)| := abs_add_le _ _
        _ ≤ _ := by linarith
    by_cases h1 : η / 3 ≤ |Y n j x t - G n x t|
    · exact Or.inl (Or.inl ((ENNReal.ofReal_le_ofReal h1).trans hU1))
    by_cases h2 : η / 3 ≤ Z n j x T
    · exact Or.inl (Or.inr (ENNReal.ofReal_le_ofReal h2))
    · refine Or.inr (ENNReal.ofReal_le_ofReal ?_)
      have h1' := not_le.mp h1
      have h2' := not_le.mp h2
      linarith
  -- conclusion
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have h2 : Tendsto (fun n => 2 * (ε n / δ)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.div_const hε0 (Or.inr hδ0))
      (a := 2) (Or.inr (by norm_num))
    simpa using h
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.mp h2 (e / 2)
    (ENNReal.half_pos he.ne')).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hU n) (e / 2) (ENNReal.half_pos he.ne')]
    with j hj
  calc μ {x | ∃ t ≤ T, η ≤ |A j x t - F x t|}
      ≤ μ ({x | δ ≤ U n j x} ∪ {x | δ ≤ ENNReal.ofReal (Z n j x T)} ∪
          {x | δ ≤ ENNReal.ofReal (F x T - G n x T)}) := measure_mono_ae (hsub n j)
    _ ≤ μ {x | δ ≤ U n j x} + μ {x | δ ≤ ENNReal.ofReal (Z n j x T)} +
          μ {x | δ ≤ ENNReal.ofReal (F x T - G n x T)} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ e / 2 + ε n / δ + ε n / δ :=
        add_le_add (add_le_add hj
          ((meas_ge_le_lintegral_div (hZm n j T).ennreal_ofReal.aemeasurable hδ0 hδtop).trans
            (ENNReal.div_le_div_right (hε n j) δ)))
          ((meas_ge_le_lintegral_div (hFm n) hδ0 hδtop).trans
            (ENNReal.div_le_div_right (hFtail n) δ))
    _ ≤ e := by
        rw [add_assoc, ← two_mul]
        calc e / 2 + 2 * (ε n / δ) ≤ e / 2 + e / 2 := add_le_add le_rfl hn
          _ = e := ENNReal.add_halves e

end HarmonicBalls
