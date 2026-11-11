import HarmonicBalls.FirstPass.S11h.PinchCertificate11_17
import HarmonicBalls.FirstPass.S11h.Assemble11_17
import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11h.CorridorSup11_17
import HarmonicBalls.FirstPass.S11h.ShiftMetric11_17
import HarmonicBalls.FirstPass.S11h.GreenField11_17
import HarmonicBalls.FirstPass.S11h.MassCoord11_17
import HarmonicBalls.FirstPass.S11h.CoordDistDiam11_17
import HarmonicBalls.FirstPass.S11h.GreenPotential11_17
import HarmonicBalls.FirstPass.S11h.SphereSup11_17
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.Frozen.S11g

/-!
# Lemma 11.17: the field-level certificate `PinchCertificateStmt` from frozen inputs

`PinchCertificateStmt` (Step 17.6, `PinchCertificate11_17.lean`) is proved from the frozen inputs
`LQGMetricFieldAxiomsUnivFrozen` (Fact 2.2, cited), `WeylScalingCompositionFrozen`, `LQGInternalMetricWeylAeMeasurableFrozen`
(open-set decoders), `LQGMassFunctionalMeasurableFrozen` (mass decoders), `InternalMetricClosedEqIInfThickeningFrozen`
(closed-set exhaustion, coordinate 0) and `WeylScaledEuclideanFrozen` (Euclidean property of the Weyl scaling).

The ten coordinates of `pinchScalars` each get a measurable decoder, and the Weyl-shifted values are identified a.s. through
`ae_weylScaling_toReal_eq_fieldMetric_shift`. Written source: corrected paper lines 3726-3756 (Step 17.6); the buffer
geometry is `IsBufferedPinchGeometry` (corrected [C42], `buffer_Q`, `buffer_W`, `closure_T_subset`, `U_nonempty`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

/-- The closed `2δ`-neighbourhood of `Q ∪ W` lies in the open disk of radius `5` (corrected [C42] `buffer_Q`, `buffer_W`). -/
theorem closure_thickening_subset_ball {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    closure (thickening (2 * δ) (Q ∪ W)) ⊆ ball (0 : ℂ) 5 := by
  have hδ := hgeo.delta_pos
  have hsub : thickening (2 * δ) (Q ∪ W) ⊆
      thickening (10 * δ) (closure Q) ∪ thickening (10 * δ) (closure W) := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := mem_thickening_iff.1 hz
    rcases hs with hsQ | hsW
    · exact Or.inl (mem_thickening_iff.2 ⟨s, subset_closure hsQ, by linarith⟩)
    · exact Or.inr (mem_thickening_iff.2 ⟨s, subset_closure hsW, by linarith⟩)
  have hQb : closure (thickening (10 * δ) (closure Q)) ⊆ ball (0 : ℂ) 5 :=
    fun z hz => ((hgeo.buffer_Q hz).1).1
  have hWb : closure (thickening (10 * δ) (closure W)) ⊆ ball (0 : ℂ) 5 :=
    fun z hz => ball_subset_ball (by norm_num) (hgeo.buffer_W hz).2.1
  calc closure (thickening (2 * δ) (Q ∪ W))
      ⊆ closure (thickening (10 * δ) (closure Q) ∪ thickening (10 * δ) (closure W)) := closure_mono hsub
    _ = closure (thickening (10 * δ) (closure Q)) ∪ closure (thickening (10 * δ) (closure W)) := closure_union
    _ ⊆ ball (0 : ℂ) 5 := union_subset hQb hWb

/-- The origin lies in the closed corridor `(B_{2δ}(Q ∪ W))ᶜ`: `Q` lies outside `B_4(0)` and `W` outside `B_1(0)`. -/
theorem zero_mem_corridor {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    (0 : ℂ) ∈ (thickening (2 * δ) (Q ∪ W))ᶜ := by
  intro h0
  obtain ⟨s, hs, hd⟩ := mem_thickening_iff.1 h0
  have hδ' := hgeo.delta_lt
  have hδ := hgeo.delta_pos
  rw [dist_comm] at hd
  rcases hs with hsQ | hsW
  · have h := (hgeo.closure_Q_subset (subset_closure hsQ)).1.2
    rw [mem_closedBall, not_le] at h
    linarith
  · have h := (hgeo.W_subset hsW).2
    rw [mem_closedBall, not_le] at h
    linarith

/-- The sphere `∂B₅(0)` lies outside the closure of the `2δ`-neighbourhood of `Q ∪ W`. -/
theorem sphere_five_subset_compl_closure {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    sphere (0 : ℂ) 5 ⊆ (closure (thickening (2 * δ) (Q ∪ W)))ᶜ := by
  intro z hz hc
  have h1 := mem_sphere_zero_iff_norm.1 hz
  have h2 := mem_ball_zero_iff.1 (closure_thickening_subset_ball hgeo hc)
  linarith

/-- `Q` is not the whole plane (its closure lies in the annulus `𝔸_{4,5}(0)`). -/
theorem Q_ne_univ {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    Q ≠ univ := by
  intro h
  have h6 : (6 : ℂ) ∈ closure Q := subset_closure (by rw [h]; exact mem_univ _)
  have h5 := mem_ball_zero_iff.1 (hgeo.closure_Q_subset h6).1.1
  have h6' : ‖(6 : ℂ)‖ = 6 := by norm_num
  linarith

/-- A sphere of positive radius about `0` in `ℂ` is nonempty. -/
theorem sphere_nonempty_of_pos {r : ℝ} (hr : 0 < r) : (sphere (0 : ℂ) r).Nonempty :=
  ⟨(r : ℂ), by rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hr.le]⟩

/-- A metric coordinate of the pinch scalars, given by a decoder of the metric and its almost sure values at `hC ω`
(through `D ω = fieldMetric 𝔇 ξ α₀ (hC ω)`) and at the Weyl-shifted field (through `hshift`). -/
theorem metric_coord_ae {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ α₀ : ℝ) (f : ℂ → ℝ) (hf : Continuous f)
    (hEuc0 : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (hC ω)))
    (hDeq : ∀ᵐ ω ∂P, D ω = fieldMetric 𝔇 ξ α₀ (hC ω))
    (hshift : ∀ᵐ ω ∂P, (fun u v => (weylScaling (D ω) ξ f u v).toReal) =
      fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f))
    (hEucf : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)))
    (Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞) (F : (ℂ → ℂ → ℝ) → ℝ≥0∞)
    (hΦ : ∀ g : ℂ → ℝ, Continuous g →
      (∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g))) →
      ∀ᵐ ω ∂P, Φ (addFunPairing (hC ω) g) = F (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g))) :
    (∀ᵐ ω ∂P, Φ (hC ω) = F (D ω)) ∧
      (∀ᵐ ω ∂P, Φ (addFunPairing (hC ω) f) = F (fun u v => (weylScaling (D ω) ξ f u v).toReal)) := by
  have hzero : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) 0)) := by
    filter_upwards [hEuc0] with ω h
    rwa [addFunPairing_zero']
  constructor
  · filter_upwards [hΦ 0 continuous_const hzero, hDeq] with ω h0 hD
    rw [addFunPairing_zero'] at h0
    rw [h0, hD]
  · filter_upwards [hΦ f hf hEucf, hshift] with ω hf1 hs
    rw [hf1, hs]

/-- Metric coordinate: an existence of a decoder yields a measurable functional with the unshifted and shifted values. -/
theorem metric_coord {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ α₀ : ℝ) (f : ℂ → ℝ) (hf : Continuous f)
    (hEuc0 : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (hC ω)))
    (hDeq : ∀ᵐ ω ∂P, D ω = fieldMetric 𝔇 ξ α₀ (hC ω))
    (hshift : ∀ᵐ ω ∂P, (fun u v => (weylScaling (D ω) ξ f u v).toReal) =
      fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f))
    (hEucf : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)))
    (F : (ℂ → ℂ → ℝ) → ℝ≥0∞)
    (hEx : ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] Φ ∧
      ∀ g : ℂ → ℝ, Continuous g →
        (∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g))) →
        ∀ᵐ ω ∂P, Φ (addFunPairing (hC ω) g) = F (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g))) :
    ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] Φ ∧
      (∀ᵐ ω ∂P, Φ (hC ω) = F (D ω)) ∧
      (∀ᵐ ω ∂P, Φ (addFunPairing (hC ω) f) = F (fun u v => (weylScaling (D ω) ξ f u v).toReal)) := by
  obtain ⟨Φ, hm, hΦ⟩ := hEx
  obtain ⟨h0, hf'⟩ := metric_coord_ae P hC D 𝔇 ξ α₀ f hf hEuc0 hDeq hshift hEucf Φ F hΦ
  exact ⟨Φ, hm, h0, hf'⟩

/-- `PinchCertificateStmt` (Step 17.6, field-level certificate of the pinch triple), proved from the frozen inputs. -/
theorem pinchCertificateStmt_of_frozen (hComp : WeylScalingCompositionFrozen.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hdec : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hF : LQGMassFunctionalMeasurableFrozen.{u}) (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hN2 : WeylScaledEuclideanFrozen) : PinchCertificateStmt.{u} := by
  unfold PinchCertificateStmt
  intro U V W T Q' Q δ hgeo γ α₀ ξ hγ0 hγ2 hα _hξ f hfd hfc _hcirc hfU hfA M _hM Ω _ P _ hC hcirc μ D
    hGFF hμ hD
  have hf : Continuous f := hfd.continuous
  have hδ : 0 < δ := hgeo.delta_pos
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  obtain ⟨hI, -, -, -⟩ := hAx Ω P γ ξ α₀ hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇
  have hEuc0 : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (hC ω)) :=
    hI.mono fun ω h => h.2
  have hDeq : ∀ᵐ ω ∂P, D ω = fieldMetric 𝔇 ξ α₀ (hC ω) := ae_eq_fieldMetric hDae
  have hshift : ∀ᵐ ω ∂P, (fun u v => (weylScaling (D ω) ξ f u v).toReal) =
      fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f) :=
    ae_weylScaling_toReal_eq_fieldMetric_shift hComp hAx P γ ξ α₀ hC hcirc D hGFF hγ0 hγ2 hα 𝔇 h𝔇 hDeq f hf
  have hEucf : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)) := by
    filter_upwards [hDeq, hEuc0, hshift] with ω hDω hE0 hsh
    rw [← hsh]
    exact hN2 (D ω) ξ f (by rw [hDω]; exact hE0) hf hfc
  -- coordinate 0: the closed-corridor supremum
  obtain ⟨Φ0, hΦ0m, h0a, hfa0⟩ := metric_coord P hC D 𝔇 ξ α₀ f hf hEuc0 hDeq hshift hEucf
    (fun m => ⨆ y ∈ sphere (0 : ℂ) 5, internalMetric m (thickening (2 * δ) (Q ∪ W))ᶜ 0 y)
    (corridorInternalSup_decoder hdec hK1 P hC hcirc 𝔇 hGFF γ ξ α₀ hγ0 hγ2 hα h𝔇
      (thickening (2 * δ) (Q ∪ W))ᶜ (closure (thickening (2 * δ) (Q ∪ W)))ᶜ
      isOpen_thickening.isClosed_compl (zero_mem_corridor hgeo)
      isClosed_closure.isOpen_compl (compl_subset_compl.2 subset_closure)
      (sphere_five_subset_compl_closure hgeo))
  -- coordinate 1: D(Q', ∂Q)
  obtain ⟨Φ1, hΦ1m, h1a, hfa1⟩ := metric_coord P hC D 𝔇 ξ α₀ f hf hEuc0 hDeq hshift hEucf
    (fun m => ENNReal.ofReal (setDist m Q' (frontier Q)))
    (by
      obtain ⟨A', hA'Q, hA'c, hQc⟩ := exists_countable_subset_dense_of_set Q'
      obtain ⟨B', hB'F, hB'c, hFc⟩ := exists_countable_subset_dense_of_set (frontier Q)
      exact exists_field_ofReal_setDist hdec P hC hcirc 𝔇 hGFF γ ξ α₀ hγ0 hγ2 hα h𝔇 Q' (frontier Q) A' B'
        hgeo.isConnected_Q'.nonempty (nonempty_frontier_iff.2 ⟨hgeo.isConnected_Q.nonempty, Q_ne_univ hgeo⟩)
        hA'Q hB'F hQc hFc hA'c hB'c)
  -- coordinate 2: diam^δ(T \ B_{3δ}(W))
  obtain ⟨Φ2, hΦ2m, h2a, hfa2⟩ := metric_coord P hC D 𝔇 ξ α₀ f hf hEuc0 hDeq hshift hEucf
    (fun m => internalDiam m δ (T \ thickening (3 * δ) W))
    (by
      obtain ⟨A', hA'A, hA'c, hAc⟩ := exists_countable_subset_dense_of_set (T \ thickening (3 * δ) W)
      exact exists_field_internalDiam hdec P hC hcirc 𝔇 hGFF γ ξ α₀ hγ0 hγ2 hα h𝔇 δ hδ
        (T \ thickening (3 * δ) W) A' hA'A hAc hA'c)
  -- coordinate 3: D(0, ∂B_δ)
  obtain ⟨Φ3, hΦ3m, h3a, hfa3⟩ := metric_coord P hC D 𝔇 ξ α₀ f hf hEuc0 hDeq hshift hEucf
    (fun m => ENNReal.ofReal (setDist m {0} (sphere 0 δ)))
    (by
      obtain ⟨B', hB'S, hB'c, hSc⟩ := exists_countable_subset_sphere_dense δ
      exact exists_field_ofReal_setDist hdec P hC hcirc 𝔇 hGFF γ ξ α₀ hγ0 hγ2 hα h𝔇 {0} (sphere 0 δ) {0} B'
        (Set.singleton_nonempty _) (sphere_nonempty_of_pos hδ) subset_rfl hB'S subset_closure hSc
        (Set.countable_singleton _) hB'c)
  -- coordinate 4: diam^δ(V)
  obtain ⟨Φ4, hΦ4m, h4a, hfa4⟩ := metric_coord P hC D 𝔇 ξ α₀ f hf hEuc0 hDeq hshift hEucf
    (fun m => internalDiam m δ V)
    (by
      obtain ⟨A', hA'V, hA'c, hVc⟩ := exists_countable_subset_dense_of_set V
      exact exists_field_internalDiam hdec P hC hcirc 𝔇 hGFF γ ξ α₀ hγ0 hγ2 hα h𝔇 δ hδ V A' hA'V hVc hA'c)
  -- coordinate 5: D(∂B_δ, ∂B_{2δ})
  obtain ⟨Φ5, hΦ5m, h5a, hfa5⟩ := metric_coord P hC D 𝔇 ξ α₀ f hf hEuc0 hDeq hshift hEucf
    (fun m => ENNReal.ofReal (setDist m (sphere 0 δ) (sphere 0 (2 * δ))))
    (by
      obtain ⟨A', hA'S, hA'c, hSc⟩ := exists_countable_subset_sphere_dense δ
      obtain ⟨B', hB'S, hB'c, hSc'⟩ := exists_countable_subset_sphere_dense (2 * δ)
      exact exists_field_ofReal_setDist hdec P hC hcirc 𝔇 hGFF γ ξ α₀ hγ0 hγ2 hα h𝔇 (sphere 0 δ)
        (sphere 0 (2 * δ)) A' B' (sphere_nonempty_of_pos hδ) (sphere_nonempty_of_pos (by linarith))
        hA'S hB'S hSc hSc' hA'c hB'c)
  -- coordinate 8: diam^δ(B_{3δ}(W) \ V)
  obtain ⟨Φ8, hΦ8m, h8a, hfa8⟩ := metric_coord P hC D 𝔇 ξ α₀ f hf hEuc0 hDeq hshift hEucf
    (fun m => internalDiam m δ (thickening (3 * δ) W \ V))
    (by
      obtain ⟨A', hA'A, hA'c, hAc⟩ := exists_countable_subset_dense_of_set (thickening (3 * δ) W \ V)
      exact exists_field_internalDiam hdec P hC hcirc 𝔇 hGFF γ ξ α₀ hγ0 hγ2 hα h𝔇 δ hδ
        (thickening (3 * δ) W \ V) A' hA'A hAc hA'c)
  -- coordinate 9: D(∂B_{2δ}, ∂B_{3δ})
  obtain ⟨Φ9, hΦ9m, h9a, hfa9⟩ := metric_coord P hC D 𝔇 ξ α₀ f hf hEuc0 hDeq hshift hEucf
    (fun m => ENNReal.ofReal (setDist m (sphere 0 (2 * δ)) (sphere 0 (3 * δ))))
    (by
      obtain ⟨A', hA'S, hA'c, hSc⟩ := exists_countable_subset_sphere_dense (2 * δ)
      obtain ⟨B', hB'S, hB'c, hSc'⟩ := exists_countable_subset_sphere_dense (3 * δ)
      exact exists_field_ofReal_setDist hdec P hC hcirc 𝔇 hGFF γ ξ α₀ hγ0 hγ2 hα h𝔇 (sphere 0 (2 * δ))
        (sphere 0 (3 * δ)) A' B' (sphere_nonempty_of_pos (by linarith)) (sphere_nonempty_of_pos (by linarith))
        hA'S hB'S hSc hSc' hA'c hB'c)
  -- coordinate 6: M · SG_{3,6}(0), via the annulus Green potential decoder
  obtain ⟨G6, hG6m, hG60, hG6f⟩ := exists_annulusGreenField hF P hC hcirc μ hGFF γ α₀ hγ0 hγ2 hα hμ
    0 3 6 f hf hfA
  -- coordinate 7: μ(U), via the mass decoder (the shift vanishes on U)
  obtain ⟨F7, hF7m, hF7⟩ := exists_mass_open_functional hF P hC hcirc μ hGFF γ α₀ hγ0 hγ2 hα hμ U
    hgeo.isOpen_U
  have h70 : ∀ᵐ ω ∂P, F7 (hC ω) = μ ω U := by
    filter_upwards [hF7 0 continuous_const (fun z _ => rfl)] with ω h
    rwa [addFunPairing_zero'] at h
  have h7f : ∀ᵐ ω ∂P, F7 (addFunPairing (hC ω) f) = (weylShiftPair γ ξ f (μ ω, D ω)).1 U := by
    filter_upwards [hF7 f hf hfU] with ω h
    rw [h]
    exact (withDensity_exp_mass_eq hgeo.isOpen_U.measurableSet γ hfU).symm
  have h60 : ∀ᵐ ω ∂P, ENNReal.ofReal M * G6 (hC ω) =
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω, D ω).1 0 3 6 := by
    filter_upwards [hG60] with ω h
    exact congrArg (fun x => ENNReal.ofReal M * x) h
  have h6f : ∀ᵐ ω ∂P, ENNReal.ofReal M * G6 (addFunPairing (hC ω) f) =
      ENNReal.ofReal M * annulusGreenPotentialSup (weylShiftPair γ ξ f (μ ω, D ω)).1 0 3 6 := by
    filter_upwards [hG6f] with ω h
    exact congrArg (fun x => ENNReal.ofReal M * x) h
  -- assemble the ten coordinates
  refine pinchFieldCertificate_of_versions P γ ξ f U V W T Q' Q δ M hC μ D
    (fun T => ![Φ0 T, Φ1 T, Φ2 T, Φ3 T, Φ4 T, Φ5 T, ENNReal.ofReal M * G6 T, F7 T, Φ8 T, Φ9 T]) ?_ ?_ ?_
  · let _inst : MeasurableSpace ((ℂ → ℝ) → ℝ) := distributionMeasurableSpace
    refine Measurable.of_eval fun i => ?_
    fin_cases i
    · exact hΦ0m
    · exact hΦ1m
    · exact hΦ2m
    · exact hΦ3m
    · exact hΦ4m
    · exact hΦ5m
    · exact hG6m.const_mul _
    · exact hF7m
    · exact hΦ8m
    · exact hΦ9m
  · filter_upwards [h0a, h1a, h2a, h3a, h4a, h5a, h60, h70, h8a, h9a] with ω a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
    funext i
    fin_cases i
    · exact a0
    · exact a1
    · exact a2
    · exact a3
    · exact a4
    · exact a5
    · exact a6
    · exact a7
    · exact a8
    · exact a9
  · filter_upwards [hfa0, hfa1, hfa2, hfa3, hfa4, hfa5, h6f, h7f, hfa8, hfa9] with
      ω b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
    funext i
    fin_cases i
    · exact b0
    · exact b1
    · exact b2
    · exact b3
    · exact b4
    · exact b5
    · exact b6
    · exact b7
    · exact b8
    · exact b9

/-- Lemma 11.17, faithful corrected form (`PinchThirdEventFaithfulStmt`: every `α₀ < Q`, the fixed buffered geometry of
[C42], the amended [C44] geometry, corrected paper lines 3726-3756). Proved from the faithful Lemma 11.16 `h16` (an explicit named hypothesis; no cycle, since 11.16 does not use 11.17), the cited metric axioms
`LQGMetricFieldAxiomsUnivFrozen` (Fact 2.2), the Cameron-Martin transfer `CameronMartinGFFMutualAbsCont`, and the frozen
inputs of `pinchCertificateStmt_of_frozen`. -/
theorem firstPass_11_17_corrected (h16 : PinchSecondEventFaithfulStmt.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hCMGFF : CameronMartinGFFMutualAbsCont.{u})
    (hComp : WeylScalingCompositionFrozen.{u}) (hdec : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hF : LQGMassFunctionalMeasurableFrozen.{u}) (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hN2 : WeylScaledEuclideanFrozen) : PinchThirdEventFaithfulStmt.{u} :=
  firstPass_11_17_of_11_16 h16 (fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc) hCMGFF
    (pinchCertificateStmt_of_frozen hComp hAx hdec hF hK1 hN2)

end HarmonicBalls
