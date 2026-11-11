import HarmonicBalls.FirstPass.S11r.RootedBufferKernel
import HarmonicBalls.FirstPass.S11r.RootedConverseGuarded

/-!
# Guarded kernel clause of the assembled rooted local identification

`ae_rootedLocalIdent_assembled_kernel` (RootedBufferKernel.lean, kept unchanged) in the guarded form: the length clause `hLenC` is assumed, and the window identity `hRLIm` concluded, only for the
roots `z ∈ A` of an arbitrary set `A`. The window families, the buffered identity `hRLI` (which uses no length clause)
and the kernel clause `hκj` are unchanged. The proof repeats the body of `ae_rootedLocalIdent_assembled_kernel`, with the
guarded converse `ae_rootedLocalIdent_windowConverse_buffered_guarded` in place of the unguarded one.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- **Guarded assembled rooted local identification with the kernel clause.** The conclusion of
`ae_rootedLocalIdent_assembled_kernel`, with the window identity `hRLIm` (the converse) required and concluded only for
the roots `z ∈ A`; the families `uc dc ur dr κ m` and the clauses `hbuf`, `hWin`, `hκm`, `hmm`, `hwin`, `hRLI`, `hκj` are
those of the unguarded theorem. -/
theorem ae_rootedLocalIdent_assembled_kernel_guarded {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
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
    (A : Set ℂ)
    (hLenC : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
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
      (∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
        FirstPassS11ai.AdmissibleRootShift α₀ z b u → ∃ j : ℕ, z ∈ ball (uc j) (ur j) ∧ ∀ᵐ ω ∂P,
          ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ closedBall z ρ ⊆ ball (dc j) (dr j) ∧
            ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
              windowDecodedMetric (ball (dc j) (dr j)) (m j)
                  (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2 (x + z) (y + z) =
                c * Dd (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u)) x y) ∧
      (∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (uc j) (ur j) → ∀ μz : Ω → Measure ℂ,
        IsLQGMeasure P γ (FirstPassS11at.rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          (κ j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2).restrict (ball (dc j) (dr j)) =
            ENNReal.ofReal a • (μz ω).restrict (ball (dc j) (dr j))) := by
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
  -- the guarded window identity: the length clause `hLenC` and the conclusion are for the roots `z ∈ A`
  have hRLIm := ae_rootedLocalIdent_windowConverse_buffered_guarded hCM hG uc dc ur dr hbuf hdens Dμ Dd hDμ hDd hfm
    κ m (fun _ => bufferX) (fun j => bufferR (uc j) (dc j) (ur j) (dr j))
    (fun j => bufferPQ (uc j) (dc j) (ur j) (dr j)) (fun _ => gaussRatSeq_dense) hκm hmm hbase
    (fun (z : ℂ) (ω : Ω) (x y : ℂ) => (weylScaling (𝔇 (hC ω)) ξ (FirstPassS11atProducers.rootedWeight α₀ γ z) x y).toReal)
    hEuc hwin A hLenC
  -- the kernel clause of each window at the insertion `α₀` (second conjunct of `LocalMeasureKernelStmt`)
  have hκA : ∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (uc j) (ur j) → ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (FirstPassS11at.rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κ j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2).restrict (ball (dc j) (dr j)) =
          ENNReal.ofReal a • (μz ω).restrict (ball (dc j) (dr j)) := fun j =>
    (ae_restrict_iff' (measurableSet_ball : MeasurableSet (ball (uc j) (ur j)))).1 (hκ2 j α₀ hα Ω P hC hcirc hG)
  exact ⟨uc, dc, ur, dr, κ, m, hbuf, hWin, hκm, hmm, hwin, hRLI, hRLIm, hκA⟩


end HarmonicBalls
