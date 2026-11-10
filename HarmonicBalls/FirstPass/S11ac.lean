import HarmonicBalls.FirstPass.S11ac.Psi
import HarmonicBalls.FirstPass.S11ac.Cost
import HarmonicBalls.FirstPass.S11ac.Finite
import HarmonicBalls.FirstPass.S11m.MeasureDecoderBall
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11i.Faithful

/-! # The punctured-ball metric decoder (fp-S11ac, owner z6; lead restatement 02:58 UTC)

`metricDecoder_punctured_ball`: for every LQG metric `𝔇`, a measurable decoder `Ψ` of the pairings on `ball 0 R` that
a.s. equals a positive multiple of the internal metric of `𝔇`'s weyl-scaled field on `ball 0 R \ {0}`.
Inputs: `hAx` (`LQGMetricFieldAxiomsUnivFrozen`, Frozen, approved), `hLoc` (the unrooted local metric replacement on
disks of `ball 0 R`, n2's `LocalMetricReplacementStmt` with `ball 0 1` replaced by `ball 0 R`).
-/

namespace HarmonicBalls.S11ac

universe u

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal Classical
open HarmonicBalls.S11m.MeasureDecoderBall (restrictMC measurable_restrictMC)

/-- A countable dense subset of an open set `X` (`X ⊆ closure Q`, `Q` countable). -/
theorem exists_countable_dense_subset_open {X : Set ℂ} (hX : IsOpen X) :
    ∃ Q : Set ℂ, Q.Countable ∧ X ⊆ closure Q := by
  obtain ⟨S, hS, hd⟩ := TopologicalSpace.exists_countable_dense ℂ
  exact ⟨X ∩ S, hS.mono inter_subset_right, hd.open_subset_closure_inter hX⟩

theorem isPathConnected_ball_diff_zero {R : ℝ} (hR : 0 < R) : IsPathConnected (ball (0 : ℂ) R \ {0}) := by
  have hopen : IsOpen (ball (0 : ℂ) R \ {0}) := isOpen_ball.sdiff isClosed_singleton
  rw [← hopen.isConnected_iff_isPathConnected]
  refine ⟨⟨((R / 2 : ℝ) : ℂ), ?_⟩, HarmonicBalls.S11m.MeasureDecoderBall.isPreconnected_ball_diff_zero R⟩
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith

/-- **Punctured-ball metric decoder** (fp-S11ac, lead restatement 02:58 UTC). For every LQG metric `𝔇`, a measurable
decoder `Ψ` of the pairings on `ball 0 R` which a.s. equals a positive multiple of the internal metric of the
weyl-scaled field on `ball 0 R \ {0}`. Inputs: `hAx` (approved frozen field axioms) and `hLoc` (unrooted local metric
replacement on disks of `ball 0 R`). -/
theorem metricDecoder_punctured_ball (hAx : HarmonicBalls.LQGMetricFieldAxiomsUnivFrozen.{u}) (γ ξ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (_hξ : 0 < ξ) (R : ℝ) (hR : 0 < R)
    (hLoc : ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 → ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), 0 < r₁ → 0 < r₂ →
      closedBall c₁ r₁ ⊆ ball c₂ r₂ → closedBall c₂ r₂ ⊆ ball (0 : ℂ) R → (0 : ℂ) ∉ closedBall c₂ r₂ →
      ∃ m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
          ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ,
        Measurable m ∧ ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
            ENNReal.ofReal (m (localMeanZeroObs α (ball c₂ r₂) (hC ω)) p) =
              ENNReal.ofReal b * internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ
                (fun z => -α * Real.log ‖z‖) u v).toReal) (ball c₂ r₂) p.1.1 p.1.2) :
    ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ∃ Ψ : ModConstTestPairings (ball (0 : ℂ) R) → ℂ × ℂ → ℝ, (∀ p : ℂ × ℂ, Measurable fun ℓ => Ψ ℓ p) ∧
        ∀ α₀ : ℝ, α₀ < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p ∈ (ball (0 : ℂ) R \ {0}) ×ˢ (ball (0 : ℂ) R \ {0}),
            ENNReal.ofReal (Ψ (localModConstField α₀ hC (ball (0 : ℂ) R) ω) p) =
              ENNReal.ofReal b * internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ
                (fun z => -α₀ * Real.log ‖z‖) u v).toReal) (ball (0 : ℂ) R \ {0}) p.1 p.2 := by
  intro 𝔇 h𝔇
  set X : Set ℂ := ball (0 : ℂ) R \ {0} with hX
  have hXo : IsOpen X := isOpen_ball.sdiff isClosed_singleton
  have hXpc : IsPathConnected X := isPathConnected_ball_diff_zero hR
  have hXne : X.Nonempty := hXpc.nonempty
  obtain ⟨f, ρ, hρ, hcov⟩ := HarmonicBalls.S11m.MeasureDecoderBall.exists_valid_cover hXo hXne
  set Dp : ℕ → Set ℂ := fun j => ball (f j) (ρ j) with hDp
  have hDpo : ∀ j, IsOpen (Dp j) := fun j => isOpen_ball
  have hDpX : ∀ j, Dp j ⊆ X := fun j => ball_subset_closedBall.trans (hρ j).2
  have hne : ∀ j, (Dp j).Nonempty := fun j => ⟨f j, mem_ball_self (hρ j).1⟩
  have hDpB : ∀ j, Dp j ⊆ ball (0 : ℂ) R := fun j => (hDpX j).trans sdiff_subset
  obtain ⟨Q, hQc, hQd⟩ := exists_countable_dense_subset_open hXo
  obtain ⟨c, r, hpair⟩ := exists_pair_data Dp hDpo
  have hch : ∀ j, ∃ L : List ℕ, OvChain Dp 0 L ∧ lastOr 0 L = j := fun j =>
    exists_ovChain Dp (HarmonicBalls.S11m.MeasureDecoderBall.isPreconnected_ball_diff_zero R) hDpo hDpX hcov hne j
  choose L hL using hch
  have hloc : ∀ j, ∃ m : ({φ : ℂ → ℝ // IsTestFunction (Dp j) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ContinuousMap ↥(Dp j ×ˢ Dp j : Set (ℂ × ℂ)) ℝ, Measurable m ∧ ∀ α : ℝ, α < lqgQ γ →
        ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(Dp j ×ˢ Dp j : Set (ℂ × ℂ)),
            ENNReal.ofReal (m (localMeanZeroObs α (Dp j) (hC ω)) p) =
              ENNReal.ofReal b * internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ
                (fun z => -α * Real.log ‖z‖) u v).toReal) (Dp j) p.1.1 p.1.2 := by
    intro j
    refine hLoc 𝔇 h𝔇 (f j) (f j) (ρ j / 2) (ρ j) (by linarith [(hρ j).1]) (hρ j).1
      (closedBall_subset_ball (by linarith [(hρ j).1])) ((hρ j).2.trans sdiff_subset) ?_
    intro h0
    exact ((hρ j).2 h0).2 (mem_singleton _)
  choose m hm using hloc
  let M : ModConstTestPairings (ball (0 : ℂ) R) → ℕ → ℂ → ℂ → ℝ := fun ℓ j z w =>
    if h : (z, w) ∈ Dp j ×ˢ Dp j then m j (restrictMC (hDpB j) ℓ) ⟨(z, w), h⟩ else 0
  have hMmeas : ∀ (j : ℕ) (z w : ℂ), Measurable fun ℓ => M ℓ j z w := by
    intro j z w
    by_cases h : (z, w) ∈ Dp j ×ˢ Dp j
    · have e : (fun ℓ => M ℓ j z w) = fun ℓ => m j (restrictMC (hDpB j) ℓ) ⟨(z, w), h⟩ := by
        funext ℓ
        simp only [M]
        split_ifs
        rfl
      rw [e]
      exact (ContinuousMap.measurable_eval (⟨(z, w), h⟩ : ↥(Dp j ×ˢ Dp j : Set (ℂ × ℂ)))).comp
        ((hm j).1.comp (measurable_restrictMC (hDpB j)))
    · have e : (fun ℓ => M ℓ j z w) = fun _ => 0 := by
        funext ℓ
        simp only [M]
        split_ifs
        rfl
      rw [e]
      exact measurable_const
  refine ⟨fun ℓ p => psiC Dp M c r L Q p.1 p.2 ℓ, fun p => psiC_measurable hMmeas c r L hQc p.1 p.2, ?_⟩
  intro α₀ hα₀ Ω _ P _ hC hcirc hW
  have hI : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ
      (fun z => -α₀ * Real.log ‖z‖) u v).toReal) :=
    (hAx Ω P γ ξ α₀ hC hcirc hW hγ hγ2 hα₀ 𝔇 h𝔇).1.mono fun ω hω => hω.2
  have hpj : ∀ᵐ ω ∂P, ∀ j, ∃ b : ℝ, 0 < b ∧ ∀ z ∈ Dp j, ∀ w ∈ Dp j,
      ENNReal.ofReal (M (localModConstField α₀ hC (ball (0 : ℂ) R) ω) j z w) =
        ENNReal.ofReal b * internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ
          (fun z => -α₀ * Real.log ‖z‖) u v).toReal) (Dp j) z w := by
    rw [ae_all_iff]
    intro j
    filter_upwards [(hm j).2 α₀ hα₀ Ω P hC hcirc hW] with ω hω
    obtain ⟨b, hb, hbid⟩ := hω
    refine ⟨b, hb, fun z hz w hw => ?_⟩
    have hz' : (z, w) ∈ Dp j ×ˢ Dp j := ⟨hz, hw⟩
    have e : M (localModConstField α₀ hC (ball (0 : ℂ) R) ω) j z w =
        m j (localMeanZeroObs α₀ (Dp j) (hC ω)) ⟨(z, w), hz'⟩ := by
      simp only [M]
      split_ifs
      rfl
    rw [e]
    exact hbid ⟨(z, w), hz'⟩
  filter_upwards [hI, hpj] with ω hD hωj
  choose β hβ hβid using hωj
  refine ⟨β 0, hβ 0, fun p hp => ?_⟩
  exact psiC_identity Dp hDpo M c r hpair L hL hXo hXpc hDpX hcov hQd (localModConstField α₀ hC (ball (0 : ℂ) R) ω)
    hD (fun x y => ENNReal.toReal_nonneg) β hβ hβid hp.1 hp.2

end HarmonicBalls.S11ac
