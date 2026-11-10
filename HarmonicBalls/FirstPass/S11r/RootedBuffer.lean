import HarmonicBalls.FirstPass.S11r.RootedConverse
import HarmonicBalls.FirstPass.S11r.LocalMetricReplacement
import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.S11at.Producers
import HarmonicBalls.FirstPass.S11d.Dyadic
import HarmonicBalls.Proofs.GFF.BackgroundChargeParameter

/-!
# Assembly of the buffered rooted local identification (fp-S11r-rooted-local-ident-e)

Stage 1 (deterministic inputs): a dense countable family of Gaussian rationals (`hXd`), the radii `R` and reference
pairs `pq` of a buffered window, and a measurable countable π-system generating the Borel sets.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- The Gaussian rationals `ℚ + iℚ`, enumerated by `ℕ` through the denumerable pair `ℚ × ℚ`. -/
noncomputable def gaussRatSeq (i : ℕ) : ℂ :=
  ⟨((Denumerable.ofNat (ℚ × ℚ) i).1 : ℝ), ((Denumerable.ofNat (ℚ × ℚ) i).2 : ℝ)⟩

/-- **Density of Gaussian rationals in balls about `0`** (the `hXd` input of the converse window identity). For every
`r > 0`, every `x` with `‖x‖ < r` and every `ε > 0`, some `gaussRatSeq i` lies in `ball 0 r` and within `ε` of `x`. -/
theorem gaussRatSeq_dense : ∀ r : ℝ, 0 < r → ∀ x ∈ ball (0 : ℂ) r, ∀ ε > 0,
    ∃ i : ℕ, ‖gaussRatSeq i‖ < r ∧ dist (gaussRatSeq i) x < ε := by
  intro r hr x hx ε hε
  rw [mem_ball, dist_zero_right] at hx
  obtain ⟨δ, hδpos, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε / 2 ∧ δ ≤ (r - ‖x‖) / 2 :=
    ⟨min (ε / 2) ((r - ‖x‖) / 2), lt_min (half_pos hε) (half_pos (sub_pos.2 hx)), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show x.re - δ < x.re + δ by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x.im - δ < x.im + δ by linarith)
  obtain ⟨i, hi⟩ : ∃ i : ℕ, Denumerable.ofNat (ℚ × ℚ) i = (p, q) := ⟨_, Denumerable.ofNat_encode _⟩
  have hval : gaussRatSeq (i) = ⟨(p : ℝ), (q : ℝ)⟩ := by
    unfold gaussRatSeq; rw [hi]
  have hre : |(p : ℝ) - x.re| < δ := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have him : |(q : ℝ) - x.im| < δ := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have hdist : ‖(⟨(p : ℝ), (q : ℝ)⟩ : ℂ) - x‖ < 2 * δ := by
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    show |(p : ℝ) - x.re| + |(q : ℝ) - x.im| < 2 * δ
    linarith
  refine ⟨i, ?_, ?_⟩
  · rw [hval]
    have h1 : ‖(⟨(p : ℝ), (q : ℝ)⟩ : ℂ)‖ ≤ ‖x‖ + ‖(⟨(p : ℝ), (q : ℝ)⟩ : ℂ) - x‖ := by
      have := norm_le_norm_add_norm_sub' (⟨(p : ℝ), (q : ℝ)⟩ : ℂ) x
      linarith [norm_sub_rev (⟨(p : ℝ), (q : ℝ)⟩ : ℂ) x]
    linarith
  · rw [hval, dist_eq_norm]
    linarith

/-- The radii `R k = δ / (k + 1)` of a window with gap `δ > 0`. -/
noncomputable def windowRadius (δ : ℝ) (k : ℕ) : ℝ := δ / ((k : ℝ) + 1)

theorem windowRadius_tendsto {δ : ℝ} : Tendsto (windowRadius δ) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem windowRadius_pos {δ : ℝ} (hδ : 0 < δ) (k : ℕ) : 0 < windowRadius δ k := by
  unfold windowRadius
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  positivity

theorem windowRadius_le {δ : ℝ} (hδ : 0 < δ) (k : ℕ) : windowRadius δ k ≤ δ := by
  unfold windowRadius
  have : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  exact div_le_self hδ.le this

/-- A countable π-system generating the Borel sets of `ℂ`, consisting of measurable sets (the measurable version of
`exists_countable_piSystem_complex`; the proof is the same, with `hopen` giving measurability). -/
theorem exists_countable_piSystem_measurable :
    ∃ f : ℕ → Set ℂ, (∀ n, MeasurableSet (f n)) ∧ (∀ m n, ∃ k, f k = f m ∩ f n) ∧
      (∃ n, f n = univ) ∧ borel ℂ = MeasurableSpace.generateFrom (Set.range f) := by
  set 𝔅 := TopologicalSpace.countableBasis ℂ with h𝔅
  set Pfam : Set (Set ℂ) := (fun F : Set (Set ℂ) => ⋂₀ F) '' {F | F.Finite ∧ F ⊆ 𝔅} with hPfam
  have hc : Pfam.Countable :=
    (Set.countable_ofPred_finite_subset (TopologicalSpace.countable_countableBasis ℂ)).image _
  have hne : Pfam.Nonempty := ⟨⋂₀ ∅, ∅, ⟨Set.finite_empty, Set.empty_subset _⟩, rfl⟩
  obtain ⟨f, hf⟩ := hc.exists_eq_range hne
  have hfm : ∀ m, f m ∈ Pfam := fun m => by rw [hf]; exact ⟨m, rfl⟩
  have hmem : ∀ s ∈ Pfam, ∃ F : Set (Set ℂ), F.Finite ∧ F ⊆ 𝔅 ∧ s = ⋂₀ F := by
    rintro s ⟨F, ⟨hF, hFB⟩, rfl⟩
    exact ⟨F, hF, hFB, rfl⟩
  have hopen : ∀ s ∈ Pfam, IsOpen s := by
    intro s hs
    obtain ⟨F, hF, hFB, rfl⟩ := hmem s hs
    exact hF.isOpen_sInter fun t ht => (TopologicalSpace.isBasis_countableBasis ℂ).isOpen (hFB ht)
  refine ⟨f, fun n => (hopen (f n) (hfm n)).measurableSet, ?_, ?_, ?_⟩
  · intro m n
    obtain ⟨F, hF, hFB, hFm⟩ := hmem _ (hfm m)
    obtain ⟨G, hG, hGB, hGn⟩ := hmem _ (hfm n)
    have hmem' : f m ∩ f n ∈ Pfam :=
      ⟨F ∪ G, ⟨hF.union hG, Set.union_subset hFB hGB⟩, by
        show ⋂₀ (F ∪ G) = f m ∩ f n
        rw [hFm, hGn, Set.sInter_union]⟩
    rw [hf] at hmem'
    obtain ⟨k, hk⟩ := hmem'
    exact ⟨k, hk⟩
  · have hu : (Set.univ : Set ℂ) ∈ Pfam :=
      ⟨∅, ⟨Set.finite_empty, Set.empty_subset _⟩, Set.sInter_empty⟩
    rw [hf] at hu
    exact hu
  · have hB := TopologicalSpace.isBasis_countableBasis ℂ
    have hsub : TopologicalSpace.countableBasis ℂ ⊆ Pfam := fun B hB' =>
      ⟨{B}, ⟨Set.finite_singleton B, Set.singleton_subset_iff.2 hB'⟩, Set.sInter_singleton B⟩
    rw [← hf]
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le fun s hs => (hopen s hs).measurableSet)
    rw [hB.borel_eq_generateFrom]
    exact MeasurableSpace.generateFrom_mono hsub

/-! ### Stage 2: buffered windows, reference pairs and the base event of one window -/

/-- The dense family of the buffered windows: the Gaussian rationals (`hXd`). -/
noncomputable def bufferX : ℕ → ℂ := gaussRatSeq

/-- The reference radii of a buffered window with buffer gap `bufferRadius uc dc ur dr`. -/
noncomputable def bufferR (uc dc : ℂ) (ur dr : ℝ) : ℕ → ℝ := windowRadius (bufferRadius uc dc ur dr)

/-- The reference pairs `pq k = (R k / 2, 0)` of a buffered window: distinct points of norm `< R k`. -/
noncomputable def bufferPQ (uc dc : ℂ) (ur dr : ℝ) : ℕ → ℂ × ℂ :=
  fun k => (((bufferR uc dc ur dr k / 2 : ℝ) : ℂ), 0)

/-- The reference pairs of a buffered window stay in the window for every root of the root disc. -/
theorem bufferPQ_mem {uc dc : ℂ} {ur dr : ℝ} (hbuf : ur + dist uc dc < dr) {z : ℂ} (hz : z ∈ ball uc ur)
    (k : ℕ) :
    ‖(bufferPQ uc dc ur dr k).1‖ < bufferR uc dc ur dr k ∧ ‖(bufferPQ uc dc ur dr k).2‖ < bufferR uc dc ur dr k ∧
      (bufferPQ uc dc ur dr k).1 ≠ (bufferPQ uc dc ur dr k).2 ∧
      (bufferPQ uc dc ur dr k).1 + z ∈ ball dc dr ∧ (bufferPQ uc dc ur dr k).2 + z ∈ ball dc dr := by
  have hδ : 0 < bufferRadius uc dc ur dr := bufferRadius_pos hbuf
  have hδdef : bufferRadius uc dc ur dr = dr - (ur + dist uc dc) := rfl
  have hR : 0 < bufferR uc dc ur dr k := windowRadius_pos hδ k
  have hRle : bufferR uc dc ur dr k ≤ bufferRadius uc dc ur dr := windowRadius_le hδ k
  rw [mem_ball] at hz
  have hzd : dist z dc < dr - bufferRadius uc dc ur dr := by
    rw [hδdef]
    linarith [dist_triangle z uc dc]
  have ha : ‖(((bufferR uc dc ur dr k / 2 : ℝ) : ℂ))‖ = bufferR uc dc ur dr k / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show ‖(((bufferR uc dc ur dr k / 2 : ℝ) : ℂ))‖ < _
    rw [ha]; linarith
  · show ‖(0 : ℂ)‖ < _
    rw [norm_zero]; exact hR
  · show (((bufferR uc dc ur dr k / 2 : ℝ) : ℂ)) ≠ 0
    exact Complex.ofReal_ne_zero.2 (half_pos hR).ne'
  · rw [mem_ball]
    show dist ((((bufferR uc dc ur dr k / 2 : ℝ) : ℂ)) + z) dc < dr
    have h1 : dist ((((bufferR uc dc ur dr k / 2 : ℝ) : ℂ)) + z) z = bufferR uc dc ur dr k / 2 := by
      rw [dist_eq_norm, add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    linarith [dist_triangle (((bufferR uc dc ur dr k / 2 : ℝ) : ℂ) + z) z dc]
  · rw [mem_ball]
    show dist ((0 : ℂ) + z) dc < dr
    rw [zero_add]
    linarith

/-- **Base event of one buffered window.** The window clauses of the decoder `m` and of the kernel `κ` at the insertion
`α = 0` (`hclause`, `hκ`) give the rooted local identification event a.s. at every root of the root disc `ball uc ur`:
this is `ae_rootedLocalIdent_base` with the explicit reference families `bufferX`, `bufferR`, `bufferPQ`. -/
theorem window_hbase {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {uc dc : ℂ} {ur dr : ℝ} (hbuf : ur + dist uc dc < dr)
    (hD1 : closedBall dc dr ⊆ ball (0 : ℂ) 1)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball dc dr) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (hκ : ∀ᵐ z ∂(volume.restrict (ball uc ur)), ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage 0 (hcirc ω))
        (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          (κ (campbellReferenceObs γ 0 (ball dc dr) (hC ω) z).2).restrict (ball dc dr) =
            ENNReal.ofReal a • (μz ω).restrict (ball dc dr))
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (m : (MeanZeroTest (ball dc dr) → ℝ) → C(↥(ball dc dr ×ˢ ball dc dr : Set (ℂ × ℂ)), ℝ))
    (hclause : ∀ᵐ z ∂(volume.restrict (ball uc ur)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball dc dr ×ˢ ball dc dr : Set (ℂ × ℂ)),
        ENNReal.ofReal (m (campbellReferenceObs γ 0 (ball dc dr) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (rootedWeylMetric 𝔇 ξ γ hC z ω) (ball dc dr) p.1.1 p.1.2)
    (hXi : LQGMetricExponentPositive) (hField : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hU : LQGMetricSatisfiesAxiomsUnivFrozen.{u}) (hLenFr : LQGMetricLengthUnivFrozen.{u})
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (hComp : WeylMetricCompositionContinuousOuterFrozen)
    (hCC : ∀ z : ℂ, LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hνex : ∀ z : ℂ, LQGMeasureExistence P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hDex : ∀ z : ℂ, ∃ D : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ γ (S11c.translatedPairing hC hcirc z) D)
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hIdγ : S11n.LQGCanonicalIdentificationStmt.{u} γ ξ γ Dμ Dd)
    (f : ℕ → Set ℂ) (hfm : ∀ n, MeasurableSet (f n)) (hPos : LQGMeasureSquarePositiveFrozen.{u}) :
    ∀ᵐ z ∂(volume.restrict (ball uc ur)), ∀ᵐ ω ∂P,
      rootedLocalIdentEvent (ball dc dr) κ m Dμ Dd γ z (closedBall 0 (bufferRadius uc dc ur dr))
        (fun n => f n ∩ closedBall 0 (bufferRadius uc dc ur dr)) bufferX (bufferR uc dc ur dr)
        (bufferPQ uc dc ur dr) (S11c.translatedPairing hC hcirc z ω) := by
  have hsub : closedBall uc ur ⊆ ball dc dr := by
    intro w hw
    rw [mem_closedBall] at hw
    rw [mem_ball]
    linarith [dist_triangle w uc dc]
  have hSQ : ∃ Q : Set ℂ, IsClosedDyadicSquare Q ∧ Q ⊆ closedBall 0 (bufferRadius uc dc ur dr) := by
    obtain ⟨-, S₂, -, h2, -, hS₂⟩ := exists_closedDyadicSquare_pair
      (U := ball (0 : ℂ) (bufferRadius uc dc ur dr)) isOpen_ball
      (mem_ball_self (bufferRadius_pos hbuf))
    exact ⟨S₂, h2, hS₂.trans ball_subset_closedBall⟩
  have hSD : ∀ z ∈ ball uc ur, (fun w => w - z) ⁻¹' closedBall 0 (bufferRadius uc dc ur dr) ⊆ ball dc dr := by
    intro z hz w hw
    have hw' : ‖w - z‖ ≤ bufferRadius uc dc ur dr := by simpa using hw
    apply closedBall_bufferRadius_subset hz
    rw [mem_closedBall, dist_eq_norm]
    exact hw'
  have hRlim : Filter.Tendsto (bufferR uc dc ur dr) Filter.atTop (𝓝 0) := windowRadius_tendsto
  have hpq : ∀ z ∈ ball uc ur, ∀ k, ‖(bufferPQ uc dc ur dr k).1‖ < bufferR uc dc ur dr k ∧
      ‖(bufferPQ uc dc ur dr k).2‖ < bufferR uc dc ur dr k ∧ (bufferPQ uc dc ur dr k).1 ≠ (bufferPQ uc dc ur dr k).2 ∧
      (bufferPQ uc dc ur dr k).1 + z ∈ ball dc dr ∧ (bufferPQ uc dc ur dr k).2 + z ∈ ball dc dr :=
    fun z hz k => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := bufferPQ_mem hbuf hz k
      exact ⟨h1, h2, h3, h4, h5⟩
  exact ae_rootedLocalIdent_base hγ0 hγ2 hG hD1 hsub κ hκ h𝔇 m hclause hXi hField hU hLenFr hRootFr hComp
    (fun z => hField Ω P γ ξ γ _ _) hCC hνex Dμ Dd hIdγ hDex (closedBall 0 (bufferRadius uc dc ur dr))
    measurableSet_closedBall (fun n => f n ∩ closedBall 0 (bufferRadius uc dc ur dr))
    (fun n => ⟨(hfm n).inter measurableSet_closedBall, inter_subset_right⟩) hSD hPos
    isBounded_closedBall hSQ bufferX (bufferR uc dc ur dr) (bufferPQ uc dc ur dr) hRlim hpq

/-- **Assembly of the buffered rooted local identification (the binders `hRLI` and `hRLIm` of
`FirstPassS11ai.ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent`).** The buffered windows come from
`exists_buffered_balls` inside the outer window `ball c₂ r₂`; on each window the kernel `κ j` and the decoder `m j` are the
witnesses of `LocalMeasureKernelStmt` and `LocalMetricReplacementStmt` (the frozen clauses for every disk, `hLMK`, `hLMR`),
read at the insertion `α = 0` (base event `window_hbase`) and at `α₀` (window clause, hence the positivity at shifted
observations). The metric length property is `rootedWeylMetric_ae_z` (S11at/Producers.lean). The remaining binders are the
frozen inputs of the base and the consumer's length clause `hLenC`. -/
theorem ae_rootedLocalIdent_assembled {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {γ ξ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hc1 : ball c₁ r₁ ⊆ ball c₂ r₂) (hr₂ : 0 < r₂)
    (hOuter : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    (hLMR : ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLMK : ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hXi : LQGMetricExponentPositive) (hField : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hU : LQGMetricSatisfiesAxiomsUnivFrozen.{u}) (hLenFr : LQGMetricLengthUnivFrozen.{u})
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (hComp : WeylMetricCompositionContinuousOuterFrozen)
    (hCC : ∀ z : ℂ, LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hνex : ∀ z : ℂ, LQGMeasureExistence P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hDex : ∀ z : ℂ, ∃ D : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ γ (S11c.translatedPairing hC hcirc z) D)
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hDμ : Measurable Dμ) (hDd : ∀ x y : ℂ, Measurable fun L : S11n.CanonSpace => Dd L x y)
    (hIdγ : S11n.LQGCanonicalIdentificationStmt.{u} γ ξ γ Dμ Dd) (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hLenC : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P,
        IsEuclideanLengthMetric (Dd (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u)))) :
    ∃ (uc dc : ℕ → ℂ) (ur dr : ℕ → ℝ)
      (κ : (j : ℕ) → ({φ : ℂ → ℝ // IsTestFunction (ball (dc j) (dr j)) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
      (m : (j : ℕ) → (MeanZeroTest (ball (dc j) (dr j)) → ℝ) →
        C(↥(ball (dc j) (dr j) ×ˢ ball (dc j) (dr j) : Set (ℂ × ℂ)), ℝ)),
      (∀ j, ur j + dist (uc j) (dc j) < dr j) ∧ (∀ j, closedBall (dc j) (dr j) ⊆ ball c₂ r₂) ∧
      (∀ j, Measurable (κ j)) ∧ (∀ j, Measurable (m j)) ∧
      (∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (uc j) (ur j) → ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
        ∀ p : ↥(ball (dc j) (dr j) ×ˢ ball (dc j) (dr j) : Set (ℂ × ℂ)),
          ENNReal.ofReal (m j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2 p) =
            ENNReal.ofReal b * internalMetric
              (fun u v : ℂ => (weylScaling (𝔇 (hC ω)) ξ (FirstPassS11atProducers.rootedWeight α₀ γ z) u v).toReal)
              (ball (dc j) (dr j)) p.1.1 p.1.2) ∧
      (∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ (b : ℝ) (u : ℂ → ℝ),
        FirstPassS11ai.AdmissibleRootShift α₀ z b u → ∃ j : ℕ, z ∈ ball (uc j) (ur j) ∧ ∀ᵐ ω ∂P,
          ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ closedBall z ρ ⊆ ball (dc j) (dr j) ∧
            ((κ j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2).map (fun w => w - z)).restrict
                (closedBall 0 ρ) =
              ENNReal.ofReal c • (Dμ (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u))).restrict
                (closedBall 0 ρ)) ∧
      (∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ (b : ℝ) (u : ℂ → ℝ),
        FirstPassS11ai.AdmissibleRootShift α₀ z b u → ∃ j : ℕ, z ∈ ball (uc j) (ur j) ∧ ∀ᵐ ω ∂P,
          ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ closedBall z ρ ⊆ ball (dc j) (dr j) ∧
            ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
              windowDecodedMetric (ball (dc j) (dr j)) (m j)
                  (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2 (x + z) (y + z) =
                c * Dd (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u)) x y) := by
  -- the buffered windows, inside the outer window `ball c₂ r₂` and away from `0`
  have hW0 : ∃ z ∈ ball c₂ r₂, z ≠ 0 := by
    by_cases h : c₂ + ((r₂ / 2 : ℝ) : ℂ) = 0
    · refine ⟨c₂ - ((r₂ / 2 : ℝ) : ℂ), ?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      · intro h2
        have ha : ((r₂ / 2 : ℝ) : ℂ) = 0 := by linear_combination (h - h2) / 2
        have := Complex.ofReal_eq_zero.1 ha
        linarith
    · refine ⟨c₂ + ((r₂ / 2 : ℝ) : ℂ), ?_, h⟩
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
  obtain ⟨uc, dc, ur, dr, hur, hbuf, hWin, hzero, hdens0⟩ := exists_buffered_balls isOpen_ball hW0
  have hdens : ∀ z ∈ ball c₁ r₁, z ≠ 0 → ∀ b : ℝ, 0 < b →
      ∃ j, z ∈ ball (uc j) (ur j) ∧ closedBall (dc j) (dr j) ⊆ ball z b :=
    fun z hz hz0 b hb => hdens0 z (hc1 hz) hz0 b hb
  have hD1 : ∀ j, closedBall (dc j) (dr j) ⊆ ball (0 : ℂ) 1 := fun j =>
    (hWin j).trans (ball_subset_closedBall.trans hOuter)
  have hdrpos : ∀ j, 0 < dr j := fun j => lt_of_le_of_lt (add_nonneg (hur j).le dist_nonneg) (hbuf j)
  have hsubj : ∀ j, closedBall (uc j) (ur j) ⊆ ball (dc j) (dr j) := fun j w hw => by
    rw [mem_closedBall] at hw
    rw [mem_ball]
    linarith [dist_triangle w (uc j) (dc j), hbuf j]
  -- the frozen kernel and decoder of each window (the witnesses are chosen once for all insertions)
  have hK := fun j => hLMK (uc j) (dc j) (ur j) (dr j) hγ0 hγ2 (hur j) (hdrpos j) (hsubj j) (hD1 j) (hzero j)
  choose κ hκm hκ1 hκ2 using hK
  have hM := fun j => hLMR (uc j) (dc j) (ur j) (dr j) hγ0 hγ2 (hur j) (hdrpos j) (hsubj j) (hD1 j) (hzero j) 𝔇 h𝔇
  choose m hmm hm18 hm20 using hM
  obtain ⟨f, hfm, hπ, huniv, hgen⟩ := exists_countable_piSystem_measurable
  have h0 : (0 : ℝ) < lqgQ γ := lqgQ_pos hγ0
  -- base event on each window, at the insertion `0`
  have hbase : ∀ j, ∀ᵐ z ∂(volume.restrict (ball (uc j) (ur j))), ∀ᵐ ω ∂P,
      S11c.translatedPairing hC hcirc z ω ∈ rootedLocalIdentEvent (ball (dc j) (dr j)) (κ j) (m j) Dμ Dd γ z
        (closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j)))
        (fun n => f n ∩ closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j))) bufferX
        (bufferR (uc j) (dc j) (ur j) (dr j)) (bufferPQ (uc j) (dc j) (ur j) (dr j)) := fun j =>
    window_hbase hγ0 hγ2 hG (hbuf j) (hD1 j) (κ j) (hκ2 j 0 h0 Ω P hC hcirc hG) h𝔇 (m j)
      (hm20 j 0 h0 Ω P hC hcirc hG) hXi hField hU hLenFr hRootFr hComp hCC hνex hDex Dμ Dd hIdγ f hfm hPos
  -- the window clauses at the insertion `α₀` and the length property of the rooted metric
  have hwin : ∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (uc j) (ur j) → ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball (dc j) (dr j) ×ˢ ball (dc j) (dr j) : Set (ℂ × ℂ)),
        ENNReal.ofReal (m j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric
            ((fun (z : ℂ) (ω : Ω) (x y : ℂ) => (weylScaling (𝔇 (hC ω)) ξ (FirstPassS11atProducers.rootedWeight α₀ γ z) x y).toReal)
              z ω) (ball (dc j) (dr j)) p.1.1 p.1.2 := fun j =>
    (ae_restrict_iff' (measurableSet_ball : MeasurableSet (ball (uc j) (ur j)))).1 (hm20 j α₀ hα Ω P hC hcirc hG)
  have hEuc := FirstPassS11atProducers.rootedWeylMetric_ae_z hLenFr hField hRootFr P γ ξ α₀ hC hcirc hG 𝔇 h𝔇
    hγ0 hγ2 hα (ball c₁ r₁)
  have hRLI := ae_rootedLocalIdent_buffered (α₀ := α₀) hCM hG uc dc ur dr hbuf hdens Dμ Dd hDμ hDd hfm hπ huniv hgen
    κ m (fun _ => bufferX) (fun j => bufferR (uc j) (dc j) (ur j) (dr j))
    (fun j => bufferPQ (uc j) (dc j) (ur j) (dr j)) hκm hmm hbase
  have hRLIm := ae_rootedLocalIdent_windowConverse_buffered hCM hG uc dc ur dr hbuf hdens Dμ Dd hDμ hDd hfm
    κ m (fun _ => bufferX) (fun j => bufferR (uc j) (dc j) (ur j) (dr j))
    (fun j => bufferPQ (uc j) (dc j) (ur j) (dr j)) (fun _ => gaussRatSeq_dense) hκm hmm hbase
    (fun (z : ℂ) (ω : Ω) (x y : ℂ) => (weylScaling (𝔇 (hC ω)) ξ (FirstPassS11atProducers.rootedWeight α₀ γ z) x y).toReal)
    hEuc hwin hLenC
  exact ⟨uc, dc, ur, dr, κ, m, hbuf, hWin, hκm, hmm, hwin, hRLI, hRLIm⟩

#print axioms gaussRatSeq_dense
#print axioms bufferPQ_mem
#print axioms window_hbase
#print axioms ae_rootedLocalIdent_assembled

end HarmonicBalls
