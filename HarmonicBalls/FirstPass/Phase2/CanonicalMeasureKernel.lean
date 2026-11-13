import HarmonicBalls.FirstPass.S11n.MeasureDecoder
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived
import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds

/-!
# The canonical measure decoder as a kernel

`S11n.MeasureDecoder.exists_measureDecoder` patches the local decoders of `LocalLQGDecoderCommonFrozen` (one kernel on
the mean-zero observations of each ball `B n = ball (g n) (‖g n‖ / 2)` of a countable cover of `ℂ \ {0}`) into one
decoder `Dμ`: for every whole-plane GFF model, almost surely `μ ω = a • Dμ (alphaCanon α₀ hC ω)` with `a > 0`. The patch
is `Σ_j ρ_j • ν_j|_{A_j}` (`S11n.PatchMeasure.patchMeasure`), where `ν_j` is the local decoder read on the canonical
field, `A_j` the disjointified cover and `ρ_j` the product of the overlap ratios along a chain from the ball `0`.

This file shows that the patch is a kernel on the canonical space: every term is the s-finite kernel `ν_j` (a local
kernel composed with the measurable restriction of the canonical field) restricted to `A_j`, with the measurable constant
density `ρ_j`, and a countable sum of s-finite kernels is s-finite (`patchKernel`, `patchKernel_apply`). The kernel is
then cut to the measurable set of canonical fields whose decoded measure is finite on the closed balls `B̄_n(0)`
(`truncKernel`), which makes it finite on compact sets at every point and does not change it on the canonical fields of
the models (where the decoded measure is a multiple of the locally finite LQG measure).

Main result: `exists_canonicalMeasureKernel` (no hypotheses): for `0 < γ < 2` and `α₀ < Q` there is an s-finite kernel
`K` from the canonical space to `ℂ`, finite on compact sets, such that for every whole-plane GFF model and every LQG
measure `μ` of the field `h^ℂ - α₀ log|·|`, almost surely `μ ω = a • K (alphaCanon α₀ hC ω)` for some `a > 0`.
-/

noncomputable section

universe u

namespace HarmonicBalls.CanonicalMeasureKernel

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal
open HarmonicBalls.S11n.MeasureDecoder HarmonicBalls.S11n.PatchMeasure

/-- Mean-zero observations of a field on `D`: pairings with the mean-zero test functions supported in `D`. -/
abbrev MeanZeroObs (D : Set ℂ) : Type := {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ

theorem measurable_restrictObs (D : Set ℂ) : Measurable (restrictObs D) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurableSet_disj {B : ℕ → Set ℂ} (hBo : ∀ j, IsOpen (B j)) (j : ℕ) : MeasurableSet (disj B j) :=
  (hBo j).measurableSet.diff (isOpen_iUnion fun i => isOpen_iUnion fun _ => hBo i).measurableSet

/-- A chain product of ratios depending measurably on a parameter is measurable in the parameter. -/
theorem measurable_chainScale {R : S11n.CanonSpace → ℕ → ℕ → ℝ≥0∞} (hR : ∀ a b, Measurable fun ℓ => R ℓ a b) :
    ∀ (l : List ℕ) (a : ℕ), Measurable fun ℓ => chainScale (R ℓ) a l
  | [], a => by simp only [chainScale]; exact measurable_const
  | b :: l, a => by simp only [chainScale]; exact (hR a b).mul (measurable_chainScale hR l b)

/-- The local decoders read on (the restrictions of) a canonical field. -/
def localPatchMeasures (B : ℕ → Set ℂ) (K : ∀ n, Kernel (MeanZeroObs (B n)) ℂ) (ℓ : S11n.CanonSpace) (n : ℕ) :
    Measure ℂ :=
  K n (restrictObs (B n) ℓ)

/-- The weight `ρ_j` of the patch: the product of the overlap ratios along the chain `L j` from the ball `0`. -/
def patchScale (B : ℕ → Set ℂ) (K : ∀ n, Kernel (MeanZeroObs (B n)) ℂ) (L : ℕ → List ℕ) (j : ℕ)
    (ℓ : S11n.CanonSpace) : ℝ≥0∞ :=
  chainScale (ratioOf B (localPatchMeasures B K ℓ)) 0 (L j)

theorem measurable_patchScale {B : ℕ → Set ℂ} (hBo : ∀ j, IsOpen (B j)) (K : ∀ n, Kernel (MeanZeroObs (B n)) ℂ)
    (L : ℕ → List ℕ) (j : ℕ) : Measurable (patchScale B K L j) := by
  refine measurable_chainScale (R := fun ℓ => ratioOf B (localPatchMeasures B K ℓ)) (fun a b => ?_) (L j) 0
  have hs : MeasurableSet (B a ∩ B b) := ((hBo a).inter (hBo b)).measurableSet
  exact ((Kernel.measurable_coe (K a) hs).comp (measurable_restrictObs _)).div
    ((Kernel.measurable_coe (K b) hs).comp (measurable_restrictObs _))

/-- The patch of the local decoders as a kernel on the canonical space: `Σ_j ρ_j • ν_j|_{A_j}`, with the weight `ρ_j`
replaced by `0` where it is infinite (so that every term is an s-finite kernel); on the canonical fields of the models
all weights are finite (`patchKernel_apply_of_ne_top`). -/
def patchKernel (B : ℕ → Set ℂ) (hBo : ∀ j, IsOpen (B j)) (K : ∀ n, Kernel (MeanZeroObs (B n)) ℂ)
    [∀ n, IsSFiniteKernel (K n)] (L : ℕ → List ℕ) : Kernel S11n.CanonSpace ℂ :=
  Kernel.sum fun j => Kernel.withDensity
    (((K j).comap (restrictObs (B j)) (measurable_restrictObs _)).restrict (measurableSet_disj hBo j))
    (fun ℓ _ => ((patchScale B K L j ℓ).toNNReal : ℝ≥0∞))

instance isSFiniteKernel_patchKernel (B : ℕ → Set ℂ) (hBo : ∀ j, IsOpen (B j))
    (K : ∀ n, Kernel (MeanZeroObs (B n)) ℂ) [∀ n, IsSFiniteKernel (K n)] (L : ℕ → List ℕ) :
    IsSFiniteKernel (patchKernel B hBo K L) := by
  unfold patchKernel
  exact Kernel.isSFiniteKernel_sum (hκs := fun j => Kernel.IsSFiniteKernel.withDensity _ fun _ _ => ENNReal.coe_ne_top)

/-- The patch kernel at a canonical field with finite weights is the patch of the local decoders read on that field. -/
theorem patchKernel_apply_of_ne_top (B : ℕ → Set ℂ) (hBo : ∀ j, IsOpen (B j)) (K : ∀ n, Kernel (MeanZeroObs (B n)) ℂ)
    [∀ n, IsSFiniteKernel (K n)] (L : ℕ → List ℕ) {ℓ : S11n.CanonSpace} (h : ∀ j, patchScale B K L j ℓ ≠ ⊤) :
    patchKernel B hBo K L ℓ = patchMeasure B (localPatchMeasures B K ℓ) L 0 := by
  rw [patchKernel, Kernel.sum_apply, patchMeasure]
  congr 1
  funext j
  rw [Kernel.withDensity_apply (f := fun ℓ _ => ((patchScale B K L j ℓ).toNNReal : ℝ≥0∞)) _
    (((measurable_patchScale hBo K L j).ennreal_toNNReal.coe_nnreal_ennreal).comp measurable_fst),
    Kernel.restrict_apply, Kernel.comap_apply, withDensity_const, ENNReal.coe_toNNReal (h j)]
  rfl

/-- Canonical fields at which a kernel gives finite mass to every closed ball `B̄_n(0)`. -/
def finiteBallSet (κ : Kernel S11n.CanonSpace ℂ) : Set S11n.CanonSpace :=
  {ℓ | ∀ n : ℕ, κ ℓ (closedBall 0 n) < ⊤}

theorem measurableSet_finiteBallSet (κ : Kernel S11n.CanonSpace ℂ) : MeasurableSet (finiteBallSet κ) := by
  have h : finiteBallSet κ = ⋂ n : ℕ, {ℓ | κ ℓ (closedBall 0 n) < ⊤} := by
    ext ℓ
    simp [finiteBallSet]
  rw [h]
  exact MeasurableSet.iInter fun n =>
    measurableSet_lt (Kernel.measurable_coe κ measurableSet_closedBall) measurable_const

open Classical in
/-- A kernel cut to `finiteBallSet κ` (and `0` elsewhere). -/
def truncKernel (κ : Kernel S11n.CanonSpace ℂ) : Kernel S11n.CanonSpace ℂ :=
  Kernel.piecewise (measurableSet_finiteBallSet κ) κ 0

instance isSFiniteKernel_truncKernel (κ : Kernel S11n.CanonSpace ℂ) [IsSFiniteKernel κ] :
    IsSFiniteKernel (truncKernel κ) := by
  unfold truncKernel
  infer_instance

theorem isFiniteMeasureOnCompacts_truncKernel (κ : Kernel S11n.CanonSpace ℂ) (ℓ : S11n.CanonSpace) :
    IsFiniteMeasureOnCompacts (truncKernel κ ℓ) := by
  classical
  unfold truncKernel
  rw [Kernel.piecewise_apply]
  split_ifs with h
  · refine ⟨fun S hS => ?_⟩
    obtain ⟨r, hr⟩ := hS.isBounded.subset_closedBall 0
    obtain ⟨n, hn⟩ := exists_nat_ge r
    exact (measure_mono (hr.trans (closedBall_subset_closedBall hn))).trans_lt (h n)
  · rw [zero_apply]
    infer_instance

theorem truncKernel_apply_of_mem {κ : Kernel S11n.CanonSpace ℂ} {ℓ : S11n.CanonSpace} (h : ℓ ∈ finiteBallSet κ) :
    truncKernel κ ℓ = κ ℓ := by
  classical
  rw [truncKernel, Kernel.piecewise_apply]
  split_ifs
  rfl

/-- The canonical measure decoder as a kernel, from the local decoders, full support and non-atomicity. -/
theorem exists_canonicalMeasureKernel_of (hK : LocalLQGDecoderCommonFrozen.{u})
    (hI1 : LQGMeasureFullSupportStmt.{u}) (hNA : LQGMeasureNonatomicAll.{u})
    (γ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) :
    ∃ K : Kernel S11n.CanonSpace ℂ, IsSFiniteKernel K ∧ (∀ ℓ, IsFiniteMeasureOnCompacts (K ℓ)) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ μ ω = ENNReal.ofReal a • K (alphaCanon α₀ hC ω) := by
  obtain ⟨g, hg, hcov⟩ := exists_centres
  have hpos : ∀ n, 0 < ‖g n‖ / 2 := fun n => half_pos (norm_pos_iff.2 (hg n))
  have hnotmem : ∀ n, (0 : ℂ) ∉ closedBall (g n) (‖g n‖ / 2) := by
    intro n h
    rw [Metric.mem_closedBall, dist_zero_left] at h
    linarith [norm_pos_iff.2 (hg n)]
  choose K hKs using fun n => hK γ hγ0 hγ2 (g n) (‖g n‖ / 2) (hpos n) (hnotmem n)
  have : ∀ n, IsSFiniteKernel (K n) := fun n => (hKs n).1
  obtain ⟨L, hL⟩ := exists_chains hg hcov
  have hBo : ∀ j, IsOpen (ball (g j) (‖g j‖ / 2)) := fun j => isOpen_ball
  refine ⟨truncKernel (patchKernel (fun n => ball (g n) (‖g n‖ / 2)) hBo K L), inferInstance,
    isFiniteMeasureOnCompacts_truncKernel _, ?_⟩
  intro Ω _ P hC hcirc μ hG hμ
  have : IsProbabilityMeasure P := hG.isProbabilityMeasure
  have hA : ∀ᵐ ω ∂P, ∀ n, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      K n (localMeanZeroObs α₀ (ball (g n) (‖g n‖ / 2)) (hC ω)) =
        c • (μ ω).restrict (ball (g n) (‖g n‖ / 2)) := by
    rw [ae_all_iff]
    intro n
    exact (hKs n).2.1 α₀ hα Ω P hC hcirc μ hG hμ
  have hN : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0 :=
    hNA γ α₀ Ω P hC hcirc hG hγ0 hγ2 hα μ hμ
  have hI : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U :=
    hI1 γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hG hμ
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  filter_upwards [hA, hN, hI, hμ'] with ω hcst hnull hpos' hlim
  choose c hc using hcst
  have hloc : IsLocallyFiniteMeasure (μ ω) := hlim.isLocallyFiniteMeasure
  have hν : ∀ n, K n (restrictObs (ball (g n) (‖g n‖ / 2)) (alphaCanon α₀ hC ω)) =
      c n • (μ ω).restrict (ball (g n) (‖g n‖ / 2)) := fun n => (hc n).2.2
  have hfin : ∀ a b, Ov (fun n => ball (g n) (‖g n‖ / 2)) a b →
      μ ω (ball (g a) (‖g a‖ / 2) ∩ ball (g b) (‖g b‖ / 2)) ≠ 0 ∧
        μ ω (ball (g a) (‖g a‖ / 2) ∩ ball (g b) (‖g b‖ / 2)) ≠ ⊤ := by
    intro a b hab
    refine ⟨(hpos' _ (isOpen_ball.inter isOpen_ball) hab).ne', ?_⟩
    have hfinS : μ ω (ball (g a) (‖g a‖ / 2) ∩ ball (g b) (‖g b‖ / 2)) ≤
        μ ω (closedBall (g a) (‖g a‖ / 2)) :=
      measure_mono (inter_subset_left.trans Metric.ball_subset_closedBall)
    exact ne_top_of_le_ne_top (isCompact_closedBall _ _).measure_lt_top.ne hfinS
  have hmain := patchMeasure_identity (B := fun n => ball (g n) (‖g n‖ / 2))
    (fun n => isOpen_ball) hcov (μ ω) (hnull 0)
    (fun n => K n (restrictObs (ball (g n) (‖g n‖ / 2)) (alphaCanon α₀ hC ω)))
    c (fun n => (hc n).1.ne') (fun n => (hc n).2.1.ne) hν hfin 0 L hL
  have hc0ne : c 0 ≠ 0 := (hc 0).1.ne'
  have hc0top : c 0 ≠ ⊤ := (hc 0).2.1.ne
  have hρ : ∀ j, patchScale (fun n => ball (g n) (‖g n‖ / 2)) K L j (alphaCanon α₀ hC ω) ≠ ⊤ := by
    intro j hj
    have hchain := chainScale_edge
      (ratioOf (fun n => ball (g n) (‖g n‖ / 2))
        (fun n => K n (restrictObs (ball (g n) (‖g n‖ / 2)) (alphaCanon α₀ hC ω))))
      (fun n => ball (g n) (‖g n‖ / 2)) c (L j) 0 (hL j).1
      (fun x y hxy => ratioOf_edge (fun n => isOpen_ball) (μ ω) _ c (fun n => (hc n).1.ne')
        (fun n => (hc n).2.1.ne) hν hfin x y hxy)
    rw [(hL j).2] at hchain
    have hj' : chainScale (ratioOf (fun n => ball (g n) (‖g n‖ / 2))
        (fun n => K n (restrictObs (ball (g n) (‖g n‖ / 2)) (alphaCanon α₀ hC ω)))) 0 (L j) = ⊤ := hj
    rw [hj', ENNReal.top_mul (hc j).1.ne'] at hchain
    exact hc0top hchain.symm
  have hpatch : patchKernel (fun n => ball (g n) (‖g n‖ / 2)) hBo K L (alphaCanon α₀ hC ω) = c 0 • μ ω := by
    rw [patchKernel_apply_of_ne_top _ _ _ _ hρ, hmain]
    rfl
  have hmem : alphaCanon α₀ hC ω ∈ finiteBallSet (patchKernel (fun n => ball (g n) (‖g n‖ / 2)) hBo K L) := by
    intro n
    rw [hpatch, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc0top) (isCompact_closedBall _ _).measure_lt_top
  refine ⟨(c 0).toReal⁻¹, inv_pos.2 (ENNReal.toReal_pos hc0ne hc0top), ?_⟩
  rw [truncKernel_apply_of_mem hmem, hpatch, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hc0ne hc0top),
    ENNReal.ofReal_toReal hc0top, smul_smul, ENNReal.inv_mul_cancel hc0ne hc0top, one_smul]

/-- The canonical measure decoder as a kernel (hCanonX lemma B6), with no hypotheses: the local decoders
(`localLQGDecoderCommonFrozen_derived`), full support (`lqgMeasureFullSupportStmt_holds`) and non-atomicity
(`lqgMeasureNonatomicAll_holds`) of the LQG measure are theorems. -/
theorem exists_canonicalMeasureKernel (γ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) :
    ∃ K : Kernel S11n.CanonSpace ℂ, IsSFiniteKernel K ∧ (∀ ℓ, IsFiniteMeasureOnCompacts (K ℓ)) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ μ ω = ENNReal.ofReal a • K (alphaCanon α₀ hC ω) :=
  exists_canonicalMeasureKernel_of LocalDecoderCommon.localLQGDecoderCommonFrozen_derived
    lqgMeasureFullSupportStmt_holds lqgMeasureNonatomicAll_holds γ α₀ hγ0 hγ2 hα

end HarmonicBalls.CanonicalMeasureKernel

end
