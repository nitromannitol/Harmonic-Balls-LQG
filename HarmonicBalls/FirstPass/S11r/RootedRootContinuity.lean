import HarmonicBalls.FirstPass.S11r.RootedHe
import HarmonicBalls.Steps.Sec11.WeylPathSegments
import HarmonicBalls.Steps.Sec11.WeylLocalCurveLength

/-!
# First pass, root continuity of the internal physical metric (fp-S11r, owner n2; R2 Steps E-F)

Steps E-F of notes/fp-gaps/CHATGPT-n2-R2-rooted-length.md (section 3), proved as the input `he_cont` of
`eq_const_mul_internal_of_local_agreement` (RootedRepair.lean). Let `d` be an `IsEuclideanLengthMetric`, `D` an open set
containing `z`, and `f` a weight continuous on `D ∖ {z}`. If the Weyl distance `W(x,z) = weylScaling d ξ f x z` tends to `0`
as `x → z`, then the internal physical metric of `e = weylPhysicalE d ξ f` on `D` tends to `0` at `z` within `D`.

Route. (E) A length-parametrized path from `x` near `z` that reaches `d`-distance `c2` from `z` must cross the annulus
`{ρ' ≤ |w - z| ≤ ρ}`, where the weight is bounded below by `m > 0` and `d z ·` grows at unit speed (crossing lemma); its
cost is then at least `m (c2 - c0)`. (F) For `x` near `z` with `W(x,z) < m (c2 - c0)`, every almost optimal path from `x` to
`z` stays in `B_ρ(z) ⊆ D`, so the internal distance satisfies `I_D(x,z) ≤ W(x,z)`.

Terminology: Weyl scaling `e^{ξ f} · d` (Duplantier-Sheffield; Gwynne-Miller); internal metric `D(·,·;U)` (Armstrong-Kuusi-Mourrat).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

/-- Crossing lemma (real analysis). Let `g` be continuous on `[0, T]` with `g t ≤ g s + (t - s)` for `s ≤ t` in `[0, T]`,
`g 0 < c0 < c2`, and `g τ ≥ c2` for some `τ ∈ [0, T]`. Then there are `t1 < t2` in `[0, T]` with `c2 - c0 ≤ t2 - t1` and
`c0 < g τ < c2` on `(t1, t2)`: `t2` is the first time `g` reaches `c2`, `t1` the last time before it that `g ≤ c0`. -/
theorem exists_crossing {g : ℝ → ℝ} {T c0 c2 : ℝ} (hg : ContinuousOn g (Icc 0 T))
    (hlip : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → g t ≤ g s + (t - s))
    (h0 : g 0 < c0) (hc : c0 < c2) (hτ : ∃ τ ∈ Icc 0 T, c2 ≤ g τ) :
    ∃ t1 ∈ Icc 0 T, ∃ t2 ∈ Icc 0 T, t1 < t2 ∧ c2 - c0 ≤ t2 - t1 ∧
      ∀ τ ∈ Ioo t1 t2, c0 < g τ ∧ g τ < c2 := by
  obtain ⟨τ0, hτ0, hgτ0⟩ := hτ
  have hS2 : IsCompact (Icc 0 T ∩ g ⁻¹' Ici c2) :=
    isCompact_Icc.of_isClosed_subset (hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
      inter_subset_left
  obtain ⟨t2, ⟨ht2I, ht2g⟩, ht2min⟩ := hS2.exists_isLeast ⟨τ0, hτ0, hgτ0⟩
  have hg2 : c2 ≤ g t2 := ht2g
  have hbefore : ∀ τ ∈ Icc 0 T, τ < t2 → g τ < c2 := by
    intro τ hτ hlt
    by_contra hcon
    exact absurd (ht2min ⟨hτ, not_lt.1 hcon⟩) (not_le.2 hlt)
  have hgt2 : ContinuousOn g (Icc 0 t2) := hg.mono (Icc_subset_Icc le_rfl ht2I.2)
  have hS1 : IsCompact (Icc 0 t2 ∩ g ⁻¹' Iic c0) :=
    (isCompact_Icc (a := 0) (b := t2)).of_isClosed_subset
      (hgt2.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic) inter_subset_left
  obtain ⟨t1, ⟨ht1I, ht1g⟩, ht1max⟩ :=
    hS1.exists_isGreatest ⟨0, ⟨⟨le_rfl, ht2I.1⟩, h0.le⟩⟩
  have hg1 : g t1 ≤ c0 := ht1g
  have hlt : t1 < t2 := by
    rcases eq_or_lt_of_le ht1I.2 with h | h
    · rw [h] at hg1
      linarith
    · exact h
  refine ⟨t1, ⟨ht1I.1, ht1I.2.trans ht2I.2⟩, t2, ht2I, hlt, ?_, ?_⟩
  · have := hlip t1 ⟨ht1I.1, ht1I.2.trans ht2I.2⟩ t2 ht2I hlt.le
    linarith
  · intro τ hτ
    have hτ1 : t1 < τ := hτ.1
    have hτ2 : τ < t2 := hτ.2
    constructor
    · by_contra hcon
      have hmem : τ ∈ Icc 0 t2 ∩ g ⁻¹' Iic c0 :=
        ⟨⟨by linarith [ht1I.1], hτ2.le⟩, not_lt.1 hcon⟩
      exact absurd (ht1max hmem) (not_le.2 hτ1)
    · exact hbefore τ ⟨by linarith [ht1I.1], by linarith [ht2I.2]⟩ hτ2

/-- A positive lower bound for a function which is positive and continuous on a compact set. -/
theorem exists_pos_lower_bound_on_compact {K : Set ℂ} (hK : IsCompact K) {F : ℂ → ℝ} (hF : ContinuousOn F K)
    (hpos : ∀ w ∈ K, 0 < F w) : ∃ m : ℝ, 0 < m ∧ ∀ w ∈ K, m ≤ F w := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨1, one_pos, fun w hw => by simp [h] at hw⟩
  · obtain ⟨w0, hw0, hmin⟩ := hK.exists_isMinOn hne hF
    exact ⟨F w0, hpos w0 hw0, fun w hw => isMinOn_iff.1 hmin w hw⟩

/-- The `d`-sublevel set `{v | d z v < c}` is Euclidean open (the triangle inequality and `isOpen_iff`). -/
theorem isOpen_dist_lt_set {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (z : ℂ) (c : ℝ) :
    IsOpen {v | d z v < c} := by
  refine (hd.isOpen_iff {v | d z v < c}).2 fun w hw => ⟨c - d z w, ?_, fun v hv => ?_⟩
  · simp only [mem_ofPred_eq] at hw
    linarith
  · have := hd.triangle z w v
    simp only [mem_ofPred_eq] at hw hv ⊢
    linarith

/-- A Euclidean ball around `z` of radius `r` is `d`-open: small `d`-balls around `z` lie inside it. -/
theorem exists_dist_lt_of_ball {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) {z : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ c > 0, ∀ w, d z w < c → w ∈ ball z r :=
  (hd.isOpen_iff (ball z r)).1 isOpen_ball z (mem_ball_self hr)

/-- Small Euclidean distance to `z` forces small `d`-distance to `z`. -/
theorem exists_ball_of_dist_lt {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) {z : ℂ} {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ w, dist w z < r → d z w < c := by
  have hz : z ∈ {v | d z v < c} := by
    rw [mem_ofPred_eq, hd.self_eq_zero z]
    exact hc
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_dist_lt_set hd z c) z hz
  exact ⟨r, hr, fun w hw => hball (mem_ball.2 hw)⟩

/-- The distance `d(z, ·)` to the root changes at unit speed along a length-parametrized curve. -/
theorem dist_root_abs_le {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) {p : ℝ → ℂ} {T : ℝ}
    (hp : IsLengthParametrized d p T) {z : ℂ} {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    |d z (p t) - d z (p s)| ≤ |t - s| := by
  have A := hd.triangle z (p s) (p t)
  have B := hd.triangle z (p t) (p s)
  have C := hd.dist_le_of_lengthParametrized hp hs ht
  have D' := hd.dist_le_of_lengthParametrized hp ht hs
  rw [abs_sub_comm s t] at D'
  rw [abs_le]
  constructor <;> linarith

/-- The map `τ ↦ d(z, p τ)` is `1`-Lipschitz on `[0, T]`. -/
theorem root_dist_lipschitzOn {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) {p : ℝ → ℂ} {T : ℝ}
    (hp : IsLengthParametrized d p T) (z : ℂ) :
    LipschitzOnWith 1 (fun τ => d z (p τ)) (Icc 0 T) := by
  refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [abs_sub_comm s t]
  exact (abs_sub_comm _ _).le.trans (dist_root_abs_le hd hp hs ht)

/-- The weighted cost of a length-parametrized curve dominates the curve length of its `E`-metric, for any symmetric
`E` bounded by the Weyl distance (the toReal variant of `IsEuclideanLengthMetric.curveLength_weyl_le_cost`). -/
theorem curveLength_le_weyl_cost {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ) (f : ℂ → ℝ)
    (hE : ∀ x y, ENNReal.ofReal (E x y) ≤ weylScaling D ξ f x y)
    (hEsymm : ∀ x y, E x y = E y x)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) :
    curveLength E p 0 T ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
  unfold curveLength
  refine iSup_le fun q => ?_
  let F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (ξ * f (p t)))
  have hedge (i : ℕ) :
      ENNReal.ofReal (E (p (q.2.1 (i + 1))) (p (q.2.1 i))) ≤
        ∫⁻ t in Icc (q.2.1 i) (q.2.1 (i + 1)), F t := by
    rw [hEsymm]
    exact (hE _ _).trans (hD.weylScaling_le_segment_cost ξ f hp (q.2.2.2 i).1
      (q.2.2.1 (Nat.le_succ i)) (q.2.2.2 (i + 1)).2)
  calc
    _ ≤ ∑ i ∈ Finset.range q.1, ∫⁻ t in Icc (q.2.1 i) (q.2.1 (i + 1)), F t :=
      Finset.sum_le_sum fun i _ => hedge i
    _ = ∫⁻ t in Icc (q.2.1 0) (q.2.1 q.1), F t :=
      sum_lintegral_Icc_adjacent F q.2.1 q.2.2.1 q.1
    _ ≤ ∫⁻ t in Icc 0 T, F t :=
      lintegral_mono' (Measure.restrict_mono_set volume (Icc_subset_Icc
        (q.2.2.2 0).1 (q.2.2.2 q.1).2)) le_rfl

/-- A continuous curve on `[0, T]` gives a unit-interval path `t ↦ p (T t)` (with its range in `p '' [0, T]`) whose
`E`-length is at most the `E`-length of the curve (the range-tracking form of
`exists_path_pathLength_le_curveLength`). -/
theorem exists_path_range_le {E : ℂ → ℂ → ℝ} {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hp : ContinuousOn p (Icc 0 T)) :
    ∃ P : Path (p 0) (p T), (∀ t : unitInterval, P t = p (T * (t : ℝ))) ∧
      pathLength E P ≤ curveLength E p 0 T := by
  have hcont : Continuous (fun t : unitInterval => p (T * (t : ℝ))) := by
    apply hp.comp_continuous (continuous_const.mul continuous_subtype_val)
    intro t
    change 0 ≤ T * (t : ℝ) ∧ T * (t : ℝ) ≤ T
    constructor
    · exact mul_nonneg hT t.2.1
    · nlinarith [t.2.2]
  let P : Path (p 0) (p T) := {
    toFun := fun t => p (T * (t : ℝ))
    continuous_toFun := hcont
    source' := by simp
    target' := by simp }
  refine ⟨P, fun t => rfl, ?_⟩
  unfold pathLength curveLength
  refine iSup_le fun q => ?_
  let u : ℕ → ℝ := fun i => T * q.2.1 i
  have hu : Monotone u := fun i j hij => mul_le_mul_of_nonneg_left (q.2.2.1 hij) hT
  have humem : ∀ i, u i ∈ Icc (0 : ℝ) T := by
    intro i
    constructor
    · exact mul_nonneg hT (q.2.2.2 i).1
    · have h := (q.2.2.2 i).2
      dsimp [u]
      nlinarith
  have hle := le_iSup (fun r : ℕ × {v : ℕ → ℝ // Monotone v ∧ ∀ i, v i ∈ Icc 0 T} =>
    ∑ i ∈ Finset.range r.1, ENNReal.ofReal (E (p (r.2.1 (i + 1))) (p (r.2.1 i))))
      ⟨q.1, ⟨u, hu, humem⟩⟩
  apply le_trans ?_ hle
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i hi
  simp only [u, P, Path.extend_apply _ (q.2.2.2 (i + 1)), Path.extend_apply _ (q.2.2.2 i)]
  rfl

/-- **Exit data** (Step E). For `d` a length metric, `D` open with `z ∈ D`, and `f` continuous on `D ∖ {z}`, there are
`0 < c0 < c2` and `m > 0` such that a length-parametrized path starting at `d`-distance `< c0` from `z`, of weighted cost
`< m (c2 - c0)`, stays in `D`. Proof: the annulus `{ρ' ≤ |w - z| ≤ ρ} ⊆ D ∖ {z}` is compact, the weight is bounded below
there, and a path reaching `d`-distance `c2` must cross it (`exists_crossing`). -/
theorem exists_exit_data {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) (hfc : ContinuousOn f (D \ {z})) :
    ∃ c0 c2 m : ℝ, 0 < c0 ∧ c0 < c2 ∧ 0 < m ∧
      ∀ (T : ℝ) (p : ℝ → ℂ), IsLengthParametrized d p T → d z (p 0) < c0 →
        ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) < ENNReal.ofReal (m * (c2 - c0)) →
          ∀ τ ∈ Icc 0 T, p τ ∈ D := by
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hD z hz
  obtain ⟨ρ, hρ, hρD⟩ : ∃ ρ > 0, closedBall z ρ ⊆ D :=
    ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεD⟩
  obtain ⟨c2, hc2, hc2ball⟩ := exists_dist_lt_of_ball hd hρ
  obtain ⟨c0, hc0, hc02⟩ : ∃ c0 : ℝ, 0 < c0 ∧ c0 < c2 := ⟨c2 / 2, by positivity, by linarith⟩
  obtain ⟨r, hr, hrball⟩ := exists_ball_of_dist_lt hd hc0
  have hKc : IsCompact (closedBall z ρ \ ball z r) := (ProperSpace.isCompact_closedBall z ρ).diff isOpen_ball
  have hKD : closedBall z ρ \ ball z r ⊆ D \ {z} := by
    intro w hw
    refine ⟨hρD hw.1, fun hwz => hw.2 ?_⟩
    rw [mem_singleton_iff] at hwz
    rw [hwz]
    exact mem_ball_self hr
  have hFc : ContinuousOn (fun w => Real.exp (ξ * f w)) (closedBall z ρ \ ball z r) :=
    ((continuousOn_const (c := ξ)).mul (hfc.mono hKD)).rexp
  obtain ⟨m, hm, hmK⟩ := exists_pos_lower_bound_on_compact hKc hFc (fun w _ => Real.exp_pos _)
  refine ⟨c0, c2, m, hc0, hc02, hm, fun T p hp hx0 hcost => ?_⟩
  have hT : 0 ≤ T := hp.1
  have hcont_g : ContinuousOn (fun τ => d z (p τ)) (Icc 0 T) :=
    (root_dist_lipschitzOn hd hp z).continuousOn
  have hlip : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → d z (p t) ≤ d z (p s) + (t - s) := by
    intro s hs t ht hst
    have h := dist_root_abs_le (z := z) hd hp hs ht
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)] at h
    linarith [le_abs_self (d z (p t) - d z (p s))]
  have hall : ∀ τ ∈ Icc 0 T, d z (p τ) < c2 := by
    intro τ0 hτ0
    by_contra hcon
    have hτ0c : c2 ≤ d z (p τ0) := not_lt.1 hcon
    obtain ⟨t1, ht1, t2, ht2, _, hlen, hint⟩ :=
      exists_crossing hcont_g hlip hx0 hc02 ⟨τ0, hτ0, hτ0c⟩
    have hpK : ∀ τ ∈ Ioo t1 t2, ENNReal.ofReal m ≤ ENNReal.ofReal (Real.exp (ξ * f (p τ))) := by
      intro τ hτ
      apply ENNReal.ofReal_le_ofReal
      obtain ⟨hc0lt, hc2gt⟩ := hint τ hτ
      apply hmK
      refine ⟨mem_closedBall.2 (le_of_lt (mem_ball.1 (hc2ball _ hc2gt))), fun hin => ?_⟩
      exact absurd (hrball _ (mem_ball.1 hin)) (not_lt.2 hc0lt.le)
    have hIoo : ∫⁻ τ in Ioo t1 t2, ENNReal.ofReal m ≤
        ∫⁻ τ in Ioo t1 t2, ENNReal.ofReal (Real.exp (ξ * f (p τ))) :=
      setLIntegral_mono' measurableSet_Ioo hpK
    have hsub : Ioo t1 t2 ⊆ Icc 0 T := Ioo_subset_Icc_self.trans (Icc_subset_Icc ht1.1 ht2.2)
    have hval : ∫⁻ _ in Ioo t1 t2, ENNReal.ofReal m = ENNReal.ofReal m * ENNReal.ofReal (t2 - t1) := by
      rw [setLIntegral_const, Real.volume_Ioo]
    have hlow : ENNReal.ofReal (m * (c2 - c0)) ≤
        ∫⁻ τ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p τ))) := by
      calc ENNReal.ofReal (m * (c2 - c0)) = ENNReal.ofReal m * ENNReal.ofReal (c2 - c0) :=
            ENNReal.ofReal_mul hm.le
        _ ≤ ENNReal.ofReal m * ENNReal.ofReal (t2 - t1) :=
            by gcongr
        _ = ∫⁻ _ in Ioo t1 t2, ENNReal.ofReal m := hval.symm
        _ ≤ ∫⁻ τ in Ioo t1 t2, ENNReal.ofReal (Real.exp (ξ * f (p τ))) := hIoo
        _ ≤ ∫⁻ τ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p τ))) := lintegral_mono_set hsub
    exact absurd hcost (not_lt.2 hlow)
  intro τ hτ
  exact hρD (ball_subset_closedBall (hc2ball _ (hall τ hτ)))

/-- **Root continuity of the internal physical metric** (Steps E-F; the input `he_cont` of
`eq_const_mul_internal_of_local_agreement`). Let `d` be an `IsEuclideanLengthMetric`, `D` open with `z ∈ D`, `f` continuous
on `D ∖ {z}`, and suppose the Weyl distance `weylScaling d ξ f x z` tends to `0` as `x → z` (the ambient continuity input
`RootedPhysicalMetricContinuousAtInsertionFrozen`, instantiated). Then the internal physical metric of `weylPhysicalE d ξ f`
on `D` tends to `0` at `z` within `D`. Proof: for `x` near `z` with `W(x,z) < m (c2 - c0)`, almost optimal paths stay in `D`
(`exists_exit_data`), hence `I_D(x,z) ≤ W(x,z)`; squeeze, then `toReal` continuity at `0`. -/
theorem internalPhysicalMetric_tendsto_root {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) (hfc : ContinuousOn f (D \ {z}))
    (hW : Tendsto (fun x => weylScaling d ξ f x z) (𝓝 z) (𝓝 0)) :
    Tendsto (fun x => internalPhysicalMetric (weylPhysicalE d ξ f) D x z) (𝓝[D] z) (𝓝 0) := by
  obtain ⟨c0, c2, m, hc0, hc02, hm, hexit⟩ := exists_exit_data hd ξ hD hz hfc
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (m * (c2 - c0)) :=
    ENNReal.ofReal_pos.2 (mul_pos hm (by linarith))
  have hkey : ∀ᶠ x in 𝓝 z,
      internalMetric (weylPhysicalE d ξ f) D x z ≤ weylScaling d ξ f x z := by
    have hzU : z ∈ {v | d z v < c0} := by
      rw [mem_ofPred_eq, hd.self_eq_zero z]
      exact hc0
    filter_upwards [(isOpen_dist_lt_set hd z c0).mem_nhds hzU,
      hW.eventually (gt_mem_nhds hη)] with x hxU hxW
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    have h := lt_min hb hxW
    simp only [weylScaling, iInf_lt_iff] at h
    obtain ⟨T, p, hp, hp0, hpT, hcost⟩ := h
    have hx0 : d z (p 0) < c0 := by
      rw [hp0]
      exact hxU
    have hcostη : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) <
        ENNReal.ofReal (m * (c2 - c0)) :=
      lt_of_lt_of_le hcost (min_le_right _ _)
    have hPD := hexit T p hp hx0 hcostη
    obtain ⟨P, hPt, hPle⟩ :=
      exists_path_range_le (E := weylPhysicalE d ξ f) hp.1 hp.2.1
    have hPD' : ∀ t, P t ∈ D := by
      intro t
      rw [hPt t]
      refine hPD _ ⟨mul_nonneg hp.1 t.2.1, ?_⟩
      linarith [mul_le_mul_of_nonneg_left t.2.2 hp.1]
    have hIP : internalMetric (weylPhysicalE d ξ f) D (p 0) (p T) ≤
        pathLength (weylPhysicalE d ξ f) P :=
      iInf₂_le P hPD'
    have hcurve := curveLength_le_weyl_cost hd ξ f
      (fun x y => ENNReal.ofReal_toReal_le) (fun x y => weylPhysicalE_symm hd ξ f x y) hp
    subst hp0
    subst hpT
    calc internalMetric (weylPhysicalE d ξ f) D (p 0) (p T)
        ≤ pathLength (weylPhysicalE d ξ f) P := hIP
      _ ≤ curveLength (weylPhysicalE d ξ f) p 0 T := hPle
      _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) := hcurve
      _ ≤ min b (ENNReal.ofReal (m * (c2 - c0))) := hcost.le
      _ ≤ b := min_le_left _ _
  have hsq : Tendsto (fun x => internalMetric (weylPhysicalE d ξ f) D x z) (𝓝[D] z) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hW.mono_left nhdsWithin_le_nhds) (Eventually.of_forall fun _ => zero_le)
      (nhdsWithin_le_nhds hkey)
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsq
  unfold internalPhysicalMetric
  simpa only [Function.comp_def, ENNReal.toReal_zero] using hreal

end HarmonicBalls
