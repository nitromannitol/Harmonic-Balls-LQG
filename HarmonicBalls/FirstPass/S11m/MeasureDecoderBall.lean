import HarmonicBalls.FirstPass.S11m.PatchOpen
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11n.MeasureDecoder
import HarmonicBalls.Draft.Section2

/-!
# Common measure decoder on a ball containing `0`


For a radius `R > 0` the punctured ball `X = B_R(0) \ {0}` is connected (`isPreconnected_ball_diff_zero`). It is covered
by countably many balls `B j = ball (f j) (ρ j)` with `closedBall (f j) (ρ j) ⊆ X`, so that `0 ∉ closedBall` and the
frozen local decoder `LocalLQGDecoderCommonFrozen` (Frozen/S11c.lean) applies to each `B j`. The local kernels are glued by
the deterministic patch of `PatchOpen` (overlap ratios along chains from `0`); the glued measure is `c • μ|_X` a.s., and
`μ {0} = 0` gives `c • μ|_{B_R(0)}`.

Inputs (named hypotheses, not frozen here): `LocalLQGDecoderCommonFrozen` (Frozen/S11c.lean), `LQGMeasureNonatomicAll`
(S11n/MeasureDecoder.lean), `LQGMeasureFullSupportStmt` (Draft/Section2.lean, Fact 2.1, HB p. 9); local finiteness of
the LQG measure comes from `IsLQGLimit` (Defs/LQG.lean).
-/

noncomputable section

open MeasureTheory Set Metric Filter ProbabilityTheory
open scoped ENNReal Topology

universe u

namespace HarmonicBalls.S11m.MeasureDecoderBall

open HarmonicBalls.S11m.PatchOpen

/-- The punctured ball `B_R(0) \ {0}` is preconnected: it is the continuous image of `ℝ × (0, R)` under
`(φ, r) ↦ r e^{iφ}` (polar coordinates). -/
theorem isPreconnected_ball_diff_zero (R : ℝ) : IsPreconnected (ball (0 : ℂ) R \ {0}) := by
  have himg : (fun p : ℝ × ℝ => (p.2 : ℂ) * Complex.exp ((p.1 : ℂ) * Complex.I)) '' (univ ×ˢ Ioo 0 R) =
      ball (0 : ℂ) R \ {0} := by
    ext z
    constructor
    · rintro ⟨⟨φ, r⟩, ⟨-, hr⟩, rfl⟩
      have hn : ‖(r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ = r := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.1.le]
      have hne : (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hn
        exact hr.1.ne hn
      refine ⟨?_, hne⟩
      show (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ∈ ball (0 : ℂ) R
      rw [mem_ball, dist_zero_right, hn]
      exact hr.2
    · intro hz
      have hzb : z ∈ ball (0 : ℂ) R := hz.1
      have hz0 : z ≠ 0 := hz.2
      rw [mem_ball, dist_zero_right] at hzb
      refine ⟨(Complex.arg z, ‖z‖), ⟨mem_univ _, ⟨norm_pos_iff.2 hz0, hzb⟩⟩, ?_⟩
      exact Complex.norm_mul_exp_arg_mul_I z
  rw [← himg]
  exact (isPreconnected_univ.prod isPreconnected_Ioo).image _ (by fun_prop : Continuous _).continuousOn

/-- A countable cover of an open nonempty set `X` by balls whose closures lie in `X`: centres `f j` and radii `ρ j`. -/
theorem exists_valid_cover {X : Set ℂ} (hX : IsOpen X) (hXne : X.Nonempty) :
    ∃ (f : ℕ → ℂ) (ρ : ℕ → ℝ), (∀ j, 0 < ρ j ∧ closedBall (f j) (ρ j) ⊆ X) ∧ X ⊆ ⋃ j, ball (f j) (ρ j) := by
  have hr : ∀ x ∈ X, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ X := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hX x hx
    refine ⟨ε / 2, half_pos hε, fun y hy => hball ?_⟩
    rw [mem_closedBall] at hy
    rw [mem_ball]
    linarith
  choose! r hr0 hrX using hr
  obtain ⟨T, hTX, hTc, hTcov⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin (f := fun x => ball x (r x)) (s := X)
      (fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx)))
  obtain ⟨x0, hx0⟩ := hXne
  obtain ⟨t0, ht0T, -⟩ := mem_iUnion₂.1 (hTcov hx0)
  obtain ⟨g, hg⟩ := hTc.exists_eq_range ⟨t0, ht0T⟩
  have hgX : ∀ j, g j ∈ X := fun j => hTX (by rw [hg]; exact mem_range_self j)
  refine ⟨g, fun j => r (g j), fun j => ⟨hr0 (g j) (hgX j), hrX (g j) (hgX j)⟩, ?_⟩
  intro z hz
  obtain ⟨t, htT, hzt⟩ := mem_iUnion₂.1 (hTcov hz)
  rw [hg] at htT
  obtain ⟨j, rfl⟩ := htT
  exact mem_iUnion.2 ⟨j, hzt⟩

/-- Restriction of a pairing on `B` to the test functions supported in `B' ⊆ B` (literal restriction). -/
def restrictMC {B B' : Set ℂ} (hBB : B' ⊆ B) (ℓ : ModConstTestPairings B) : ModConstTestPairings B' :=
  fun φ => ℓ ⟨φ.1, ⟨φ.2.1.1, φ.2.1.2.1, φ.2.1.2.2.trans hBB⟩, φ.2.2⟩

theorem measurable_restrictMC {B B' : Set ℂ} (hBB : B' ⊆ B) : Measurable (restrictMC hBB) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- The overlap ratio `ν_a(B_a ∩ B_b) / ν_b(B_a ∩ B_b)`. -/
def glueRatio (B : ℕ → Set ℂ) (ν : ℕ → Measure ℂ) (a b : ℕ) : ℝ≥0∞ :=
  ν a (B a ∩ B b) / ν b (B a ∩ B b)

/-- The glued measure: the patch of the local measures `ν j` along the chains `L j` from the base ball `0`. -/
def glueMeasure (B : ℕ → Set ℂ) (L : ℕ → List ℕ) (ν : ℕ → Measure ℂ) : Measure ℂ :=
  patchMeasure B ν (glueRatio B ν) L 0

theorem glueRatio_mul {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j)) (μ : Measure ℂ) (ν : ℕ → Measure ℂ)
    (c : ℕ → ℝ≥0∞) (hc0 : ∀ j, c j ≠ 0) (hcT : ∀ j, c j ≠ ⊤) (hν : ∀ j, ν j = c j • μ.restrict (B j))
    (hfin : ∀ a b, Ov B a b → μ (B a ∩ B b) ≠ 0 ∧ μ (B a ∩ B b) ≠ ⊤) (a b : ℕ) (hab : Ov B a b) :
    glueRatio B ν a b * c b = c a := by
  have hS : MeasurableSet (B a ∩ B b) := ((hopen a).inter (hopen b)).measurableSet
  have hna : ν a (B a ∩ B b) = c a * μ (B a ∩ B b) := by
    rw [hν a, Measure.smul_apply, Measure.restrict_apply hS, Set.inter_eq_left.2 inter_subset_left, smul_eq_mul]
  have hnb : ν b (B a ∩ B b) = c b * μ (B a ∩ B b) := by
    rw [hν b, Measure.smul_apply, Measure.restrict_apply hS, Set.inter_eq_left.2 inter_subset_right, smul_eq_mul]
  obtain ⟨h0, hT⟩ := hfin a b hab
  unfold glueRatio
  rw [hna, hnb, ENNReal.mul_div_mul_right _ _ h0 hT, ENNReal.div_mul_cancel (hc0 b) (hcT b)]

theorem measurable_glueRatio {D : Type*} [MeasurableSpace D] {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j))
    (ν : D → ℕ → Measure ℂ) (hν : ∀ j S, MeasurableSet S → Measurable fun d => ν d j S) (a b : ℕ) :
    Measurable fun d => glueRatio B (ν d) a b := by
  have hS : MeasurableSet (B a ∩ B b) := ((hopen a).inter (hopen b)).measurableSet
  unfold glueRatio
  exact Measurable.div (hν a _ hS) (hν b _ hS)

theorem measurable_chainScale' {D : Type*} [MeasurableSpace D] {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j))
    (ν : D → ℕ → Measure ℂ) (hν : ∀ j S, MeasurableSet S → Measurable fun d => ν d j S) :
    ∀ (l : List ℕ) (a : ℕ), Measurable fun d => chainScale (glueRatio B (ν d)) a l
  | [], a => by simp only [chainScale]; exact measurable_const
  | b :: l, a => by
    simp only [chainScale]
    exact (measurable_glueRatio hopen ν hν a b).mul (measurable_chainScale' hopen ν hν l b)

theorem measurable_glueMeasure {D : Type*} [MeasurableSpace D] {B : ℕ → Set ℂ} (hopen : ∀ j, IsOpen (B j))
    (L : ℕ → List ℕ) (ν : D → ℕ → Measure ℂ) (hν : ∀ j S, MeasurableSet S → Measurable fun d => ν d j S) :
    Measurable fun d => glueMeasure B L (ν d) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  have hfun : (fun d => glueMeasure B L (ν d) s) =
      fun d => ∑' j, chainScale (glueRatio B (ν d)) 0 (L j) * ν d j (s ∩ disj B j) :=
    funext fun d => patchMeasure_apply B _ _ _ _ hs
  rw [hfun]
  exact Measurable.tsum fun j =>
    (measurable_chainScale' hopen ν hν (L j) 0).mul (hν j _ (hs.inter (disj_measurable hopen j)))

/-- Common measure decoder on the cover of `B_R(0) \ {0}` by balls with closures avoiding `0`. -/
theorem measureDecoder_of_cover (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u}) (hFull : LQGMeasureFullSupportStmt.{u}) (R : ℝ) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (f : ℕ → ℂ) (ρ : ℕ → ℝ)
    (hρ : ∀ j, 0 < ρ j ∧ closedBall (f j) (ρ j) ⊆ ball (0 : ℂ) R \ {0})
    (hcov : ball (0 : ℂ) R \ {0} ⊆ ⋃ j, ball (f j) (ρ j)) :
    ∃ Φ : ModConstTestPairings (ball (0 : ℂ) R) → Measure ℂ, Measurable Φ ∧
    ∀ α₀ : ℝ, α₀ < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
        Φ (localModConstField α₀ hC (ball (0 : ℂ) R) ω) = c • (μ ω).restrict (ball (0 : ℂ) R) := by
  have hsubX : ∀ j, ball (f j) (ρ j) ⊆ ball (0 : ℂ) R \ {0} := fun j =>
    ball_subset_closedBall.trans (hρ j).2
  have hsubB : ∀ j, ball (f j) (ρ j) ⊆ ball (0 : ℂ) R := fun j => (hsubX j).trans sdiff_subset
  have hopen : ∀ j, IsOpen (ball (f j) (ρ j)) := fun j => isOpen_ball
  have hne : ∀ j, (ball (f j) (ρ j)).Nonempty := fun j => ⟨f j, mem_ball_self (hρ j).1⟩
  have hnot : ∀ j, (0 : ℂ) ∉ closedBall (f j) (ρ j) := fun j h => ((hρ j).2 h).2 rfl
  choose K _hs hK1 _hK2 using fun j => hLoc γ hγ hγ2 (f j) (ρ j) (hρ j).1 (hnot j)
  choose L hL using fun j =>
    exists_chain (B := fun j => ball (f j) (ρ j)) (isPreconnected_ball_diff_zero R) hopen hsubX hcov hne 0 j
  have hνm : ∀ j, Measurable fun ℓ : ModConstTestPairings (ball (0 : ℂ) R) =>
      K j (restrictMC (hsubB j) ℓ) := fun j => (K j).measurable.comp (measurable_restrictMC (hsubB j))
  refine ⟨fun ℓ => glueMeasure (fun j => ball (f j) (ρ j)) L (fun j => K j (restrictMC (hsubB j) ℓ)), ?_, ?_⟩
  · exact measurable_glueMeasure (D := ModConstTestPairings (ball (0 : ℂ) R)) hopen L
      (fun ℓ j => K j (restrictMC (hsubB j) ℓ)) fun j S hS => (Measure.measurable_coe hS).comp (hνm j)
  · intro α₀ hα Ω _ P _ hC hcirc μ hgff hμ
    have hA : ∀ᵐ ω ∂P, ∀ j, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
        K j (localMeanZeroObs α₀ (ball (f j) (ρ j)) (hC ω)) = c • (μ ω).restrict (ball (f j) (ρ j)) :=
      ae_all_iff.2 fun j => hK1 j α₀ hα Ω P hC hcirc μ hgff hμ
    have hB : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0 := hNonat γ α₀ Ω P hC hcirc hgff hγ hγ2 hα μ hμ
    have hC' : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U :=
      hFull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hgff hμ
    have hD : ∀ᵐ ω ∂P, μ ω (ball (0 : ℂ) R) ≠ ⊤ := by
      have hμ' := hμ
      unfold IsLQGMeasureOfField IsLQGMeasure at hμ'
      filter_upwards [hμ'] with ω hω
      have := hω.isLocallyFiniteMeasure
      exact ne_top_of_le_ne_top ((isCompact_closedBall (0 : ℂ) R).measure_lt_top).ne
        (measure_mono ball_subset_closedBall)
    filter_upwards [hA, hB, hC', hD] with ω hAω hBω hCω hDω
    choose c hc0 hcT hcK using hAω
    have hcne : ∀ j, c j ≠ 0 := fun j => (hc0 j).ne'
    have hcT' : ∀ j, c j ≠ ⊤ := fun j => (hcT j).ne
    have hν : ∀ j, (fun j => K j (restrictMC (hsubB j) (localModConstField α₀ hC (ball (0 : ℂ) R) ω))) j =
        c j • (μ ω).restrict (ball (f j) (ρ j)) := fun j => hcK j
    have hfin : ∀ a b, Ov (fun j => ball (f j) (ρ j)) a b →
        μ ω (ball (f a) (ρ a) ∩ ball (f b) (ρ b)) ≠ 0 ∧ μ ω (ball (f a) (ρ a) ∩ ball (f b) (ρ b)) ≠ ⊤ := by
      intro a b hab
      have hpos := hCω _ ((hopen a).inter (hopen b)) hab
      exact ⟨hpos.ne', ne_top_of_le_ne_top hDω (measure_mono (inter_subset_left.trans (hsubB a)))⟩
    have hR' : ∀ a b, Ov (fun j => ball (f j) (ρ j)) a b →
        glueRatio (fun j => ball (f j) (ρ j))
          (fun j => K j (restrictMC (hsubB j) (localModConstField α₀ hC (ball (0 : ℂ) R) ω))) a b * c b = c a :=
      fun a b hab => glueRatio_mul (B := fun j => ball (f j) (ρ j)) hopen (μ ω) _ c hcne hcT' hν hfin a b hab
    have hsplit := patchMeasure_eq (X := ball (0 : ℂ) R \ {0}) (B := fun j => ball (f j) (ρ j)) hopen hsubX
      hcov (μ ω) c _ hν _ hR' 0 L hL
    have h1 : (ball (0 : ℂ) R \ {0}) \ ball (0 : ℂ) R = ∅ := Set.sdiff_eq_empty.2 fun z hz => hz.1
    have hXeq : (ball (0 : ℂ) R \ {0}) =ᵐ[μ ω] ball (0 : ℂ) R :=
      ae_eq_set.2 ⟨by rw [h1, measure_empty],
        measure_mono_null (fun z hz => by_contra fun h => hz.2 ⟨hz.1, h⟩) (hBω 0)⟩
    refine ⟨c 0, hc0 0, hcT 0, ?_⟩
    show glueMeasure (fun j => ball (f j) (ρ j)) L
        (fun j => K j (restrictMC (hsubB j) (localModConstField α₀ hC (ball (0 : ℂ) R) ω))) =
        c 0 • (μ ω).restrict (ball (0 : ℂ) R)
    unfold glueMeasure
    rw [hsplit, Measure.restrict_congr_set hXeq]

/-- Measure decoder on a ball containing `0`: for
`0 < γ < 2` there is a measurable map `Φ` from the mean-zero pairings on `B_R(0)` to measures such that for every
insertion `α₀ < Q` and every model, almost surely `Φ` of the observation is a positive finite multiple of `μ|_{B_R(0)}`.
The constant is random (it is the normalisation of the decoder); `{0}` is `μ`-null. -/
theorem measureDecoder_ball_zero (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u}) (hFull : LQGMeasureFullSupportStmt.{u}) (R : ℝ) (hR : 0 < R)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ Φ : ModConstTestPairings (ball (0 : ℂ) R) → Measure ℂ, Measurable Φ ∧
    ∀ α₀ : ℝ, α₀ < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
        Φ (localModConstField α₀ hC (ball (0 : ℂ) R) ω) = c • (μ ω).restrict (ball (0 : ℂ) R) := by
  have hXne : (ball (0 : ℂ) R \ {0}).Nonempty := by
    refine ⟨((R / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · exact Complex.ofReal_ne_zero.2 (by linarith : (0 : ℝ) < R / 2).ne'
  obtain ⟨f, ρ, hρ, hcov⟩ := exists_valid_cover (isOpen_ball.sdiff isClosed_singleton) hXne
  exact measureDecoder_of_cover hLoc hNonat hFull R γ hγ hγ2 f ρ hρ hcov

end HarmonicBalls.S11m.MeasureDecoderBall

end
