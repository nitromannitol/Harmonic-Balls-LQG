import HarmonicBalls.Proofs.Sec8.StationaryGoodScales
import HarmonicBalls.Draft.Section6

/-!
# Almost-sure locality and trivial germs

Locality statements give measurable versions only up to null sets. A countable
cofinal family of nested germs combines these versions into one event belonging
to every germ, without assuming the original event is exactly measurable there.
-/

open MeasureTheory Filter Set Finset
open scoped Topology BigOperators

namespace HarmonicBalls

/-- Almost-sure local versions of an event have a common representative in a
countably cofinal, monotone germ. -/
theorem exists_germ_measurable_event_of_ae_local {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ) (A : Set Ω)
    (hA : ∀ ε, 0 < ε → ∃ B : Set Ω, MeasurableSet[germ ε] B ∧ A =ᵐ[P] B) :
    ∃ B : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] B) ∧ A =ᵐ[P] B := by
  classical
  choose E hEm hEeq using fun n => hA (r n) (hr n)
  let B : Set Ω := ⋂ n : ℕ, ⋃ k ≥ n, E k
  have hB (N : ℕ) : B = ⋂ n ≥ N, ⋃ k ≥ n, E k := by
    ext ω
    simp only [B, mem_iInter, mem_iUnion]
    constructor
    · intro h n _
      exact h n
    · intro h n
      obtain ⟨k, hk, hkE⟩ := h (max n N) (le_max_right _ _)
      exact ⟨k, (le_max_left _ _).trans hk, hkE⟩
  refine ⟨B, ?_, ?_⟩
  · intro ε hε
    obtain ⟨N, hN⟩ := hcofinal ε hε
    rw [hB N]
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iInter
    intro hn
    apply MeasurableSet.iUnion
    intro k
    apply MeasurableSet.iUnion
    intro hk
    apply (hgmono ((hrmono (hn.trans hk)).trans hN))
    exact hEm k
  · have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ A ↔ ω ∈ E n) := ae_all_iff.2 (fun n => by
      filter_upwards [hEeq n] with ω hω
      exact Iff.of_eq hω)
    filter_upwards [hall] with ω hω
    apply propext
    simp only [B, mem_iInter, mem_iUnion]
    constructor
    · intro h n
      exact ⟨n, le_rfl, (hω n).1 h⟩
    · intro h
      obtain ⟨k, _, hk⟩ := h 0
      exact (hω k).2 hk

/-- A random variable with an almost-surely equal local version in every
member of a trivial, countably cofinal germ is almost surely constant. -/
theorem ae_eq_const_of_trivial_germ_of_ae_local {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (germ : ℝ → MeasurableSpace Ω)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (L : Ω → ℝ) (hL : Measurable L)
    (hlocal : ∀ ε, 0 < ε → ∃ Lε : Ω → ℝ,
      @Measurable Ω ℝ (germ ε) _ Lε ∧ L =ᵐ[P] Lε)
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1) :
    ∃ c : ℝ, ∀ᵐ ω ∂P, L ω = c := by
  apply ae_eq_const_of_zero_one_law P L hL
  intro S hS
  obtain ⟨B, hB, hBeq⟩ := exists_germ_measurable_event_of_ae_local P germ r hr
    hcofinal hrmono hgmono (L ⁻¹' S) (by
      intro ε hε
      obtain ⟨Lε, hm, heq⟩ := hlocal ε hε
      refine ⟨Lε ⁻¹' S, hm hS, ?_⟩
      filter_upwards [heq] with ω hω
      simp only [Set.mem_preimage, hω])
  rw [measure_congr hBeq]
  exact htrivial B hB

/-- If all sufficiently small-scale coordinates have germ-measurable versions
almost surely, then the limiting initial frequency has a germ-measurable
version at each positive radius. -/
theorem ae_local_initialScaleFrequency {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (germ : ℝ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n)) :
    ∀ ε, 0 < ε → ∃ Lε : Ω → ℝ,
      @Measurable Ω ℝ (germ ε) _ Lε ∧
      (fun ω => limUnder atTop (fun N : ℕ =>
        (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))) =ᵐ[P] Lε := by
  classical
  intro ε hε
  obtain ⟨K, Y, hYm, hYeq⟩ := hlocal ε hε
  let Z : ℕ → Ω → ℝ := fun n ω => if K ≤ n then Y n ω else 0
  have hZm : ∀ n, @Measurable Ω ℝ (germ ε) _ (Z n) := by
    intro n
    by_cases hn : K ≤ n
    · simpa [Z, hn] using hYm n hn
    · simp only [Z, ite_eq_right hn]
      exact measurable_const
  let Lε : Ω → ℝ := fun ω => limUnder atTop (fun N : ℕ =>
    (∑ n ∈ Icc 1 N, Z n ω) / (N : ℝ))
  refine ⟨Lε, ?_, ?_⟩
  · let : MeasurableSpace Ω := germ ε
    apply (StronglyMeasurable.limUnder ?_).measurable
    intro N
    exact ((Finset.measurable_sum _ fun n _ => hZm n).div_const _).stronglyMeasurable
  · have heq : ∀ᵐ ω ∂P, ∀ n, K ≤ n → X n ω = Z n ω := by
      apply ae_all_iff.2
      intro n
      by_cases hn : K ≤ n
      · filter_upwards [hYeq n hn] with ω hω _
        simpa [Z, hn] using hω
      · filter_upwards [] with ω hkn
        exact (hn hkn).elim
    filter_upwards [heq] with ω hω
    apply limUnder_eq_of_sub_tendsto_zero
    exact initialScaleAverage_sub_tendsto_zero_of_tail_eq _ _ K hω

open Classical in
/-- The stationary good-scale frequency estimate remains valid when locality
is only known through almost-surely equal local versions. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_stationary_ae_local
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (q ζ : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hX : ∀ n ω, X n ω = if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0)
    (hXm : ∀ n, Measurable (X n))
    (hBirkhoff : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (hmean : ∀ n, ∫ ω, X n ω ∂P = q) (hq : 1 - ζ < q) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  let L : Ω → ℝ := fun ω => limUnder atTop (fun N : ℕ =>
    (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
  have hLm : Measurable L := by
    apply (StronglyMeasurable.limUnder ?_).measurable
    intro N
    exact ((Finset.measurable_sum _ fun n _ => hXm n).div_const _).stronglyMeasurable
  obtain ⟨c, hc⟩ := ae_eq_const_of_trivial_germ_of_ae_local P germ r hr hcofinal
    hrmono hgmono L hLm (ae_local_initialScaleFrequency P germ X hlocal) htrivial
  have hInt : Integrable (X 1) P := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hXm 1).aestronglyMeasurable
    filter_upwards with ω
    rw [hX]
    split_ifs <;> norm_num
  have hconv := ae_tendsto_initialScaleAverage_of_stationary P X hBirkhoff hXm hInt hstat
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)) atTop (𝓝 c) := by
    filter_upwards [hconv, hc] with ω ⟨d, hd⟩ hω
    have hdc : d = c := hd.limUnder_eq.symm.trans hω
    simpa only [hdc] using hd
  exact ae_eventually_veryGoodComparableScaleCount_of_indicator_limit P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m X c q ζ hX hXm hlim hmean hq

/-- Field restrictions modulo constants are monotone in the domain. -/
theorem fieldSigmaAlgebraModConst_mono {Ω : Type*} (α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) {U V : Set ℂ} (hUV : U ⊆ V) :
    Section6.fieldSigmaAlgebraModConst α₀ hC U ≤ Section6.fieldSigmaAlgebraModConst α₀ hC V := by
  unfold Section6.fieldSigmaAlgebraModConst
  apply iSup_le
  intro φ
  apply iSup_le
  intro hφ
  apply le_iSup_of_le φ
  apply le_iSup_of_le ⟨⟨hφ.1.1, hφ.1.2.1, hφ.1.2.2.trans hUV⟩, hφ.2⟩
  exact le_rfl

/-- Dyadic radii form a countable decreasing cofinal family near zero. -/
theorem dyadicScale_germ_cofinal :
    Antitone dyadicScale ∧ ∀ ε : ℝ, 0 < ε → ∃ n, dyadicScale n ≤ ε := by
  constructor
  · exact pow_right_anti₀ (by norm_num) (by norm_num)
  · intro ε hε
    have ht : Tendsto dyadicScale atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨n, hn⟩ := ((tendsto_order.1 ht).2 ε hε).exists
    exact ⟨n, hn.le⟩

/-- The field modulo constants on concentric disks is an increasing family of
sigma algebras as the radius grows. -/
theorem monotone_fieldSigmaAlgebraModConst_ball {Ω : Type*} (α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (z : ℂ) :
    Monotone (fun ε => Section6.fieldSigmaAlgebraModConst α₀ hC (Metric.ball z ε)) := by
  intro ε δ hεδ
  exact fieldSigmaAlgebraModConst_mono α₀ hC (Metric.ball_subset_ball hεδ)

end HarmonicBalls
