import Mathlib
import HarmonicBalls.FirstPass.S11ah.LQGDecoder
import HarmonicBalls.FirstPass.S11r.RootedLocality
import HarmonicBalls.FirstPass.S11r.RootedLocalBall
import HarmonicBalls.FirstPass.S11r.InternalSubdomain
import HarmonicBalls.FirstPass.S11m.WeylLengthCompact
import HarmonicBalls.FirstPass.S11m.Finiteness
import HarmonicBalls.Steps.Sec11.InternalMetricNear
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import HarmonicBalls.Steps.Sec11.InternalMetricPaths

/-!
# Proof of the cutoff transfer R1 (fp-S11ah-11-13-steps-4-5c, owner n4; wave 32)

`CutoffInternalLengthStmt ξ α` (`S11ah/LQGDecoder.lean`) is the deterministic statement R1 of
`notes/fp-gaps/CHATGPT-n1-n2-11-13-inputs.md` section 3.1. This file proves it, so it is no longer a named input.

Route (section 3.2 of that note, with the repository lemmas it uses):

* Step 1 (cutoff): a smooth `f = χ · (-α log‖·‖)` with `χ = φ (1 - ψ)`, `χ = 1` on a neighbourhood of `closure V`
  and `χ = 0` near `0`; item 1 is `HarmonicBalls.weylScaling_continuous_compactSupport_length` (S11m/WeylLengthCompact).
* Step 2 (finiteness on `V`): `RootedLocal.weylScaling_eq_near` gives local equality of the weights, hence the local
  finiteness hypothesis of `RootedLocal.weylScaling_ne_top_of_connected`.
* Step 3 (equality of internal metrics on `V`): `RootedLocal.internalMetric_weylScaling_eq_of_eventuallyEq` (n2).
* Step 4 (length metric on `V`): `isLengthMetricOn_internalReal`, the internal distance of a Euclidean length metric
  on an open set is a Euclidean length metric there, built from the repository's internal-metric lemmas
  (`internalMetric_internalMetric_toReal_of_finite`, `internalMetric_eq_of_near`, triangle and symmetry).
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal ContDiff

noncomputable section

namespace FirstPassS11ah

/-- The internal distance of a Euclidean length metric `I` on an open set `V` is an `IsLengthMetricOn V` metric. -/
theorem isLengthMetricOn_internalReal {I : ℂ → ℂ → ℝ} (hI : IsEuclideanLengthMetric I) {V : Set ℂ}
    (hVo : IsOpen V) (hfin : ∀ x ∈ V, ∀ y ∈ V, internalMetric I V x y ≠ ⊤) :
    IsLengthMetricOn V (internalReal I V) := by
  have hnonneg : ∀ x y, 0 ≤ I x y := fun x y => RootedLocal.nonneg_of_length hI x y
  have hcont := hI.continuousOn_internalMetric_pair hnonneg hVo
  have hanti : ∀ x ∈ V, ∀ y ∈ V, ENNReal.ofReal (I x y) ≤ internalMetric I V x y := fun x _ y _ => by
    rw [hI.ofReal_eq_internalMetric x y]
    exact internalMetric_anti I (subset_univ V) x y
  refine
    { self_eq_zero := fun z hz => ?_
      eq_of_eq_zero := fun z hz w hw h => ?_
      symm := fun z hz w hw => ?_
      triangle := fun x hx y hy z hz => ?_
      continuousOn := ?_
      isOpen_iff := fun U hUV => ?_
      ofReal_eq_internalMetric := fun z hz w hw => ?_ }
  · show (internalMetric I V z z).toReal = 0
    rw [hI.internalMetric_self_of_mem_open hnonneg hVo hz]
    rfl
  · have h0 : internalMetric I V z w = 0 := ((ENNReal.toReal_eq_zero_iff _).1 h).resolve_right (hfin z hz w hw)
    have h1 : ENNReal.ofReal (I z w) ≤ 0 := h0 ▸ hanti z hz w hw
    have h2 : I z w = 0 := le_antisymm (ENNReal.ofReal_eq_zero.1 (nonpos_iff_eq_zero.1 h1))
      (RootedLocal.nonneg_of_length hI z w)
    exact hI.eq_of_eq_zero z w h2
  · show (internalMetric I V z w).toReal = (internalMetric I V w z).toReal
    rw [hI.internalMetric_symm V z w]
  · show (internalMetric I V x z).toReal ≤ (internalMetric I V x y).toReal + (internalMetric I V y z).toReal
    rw [← ENNReal.toReal_add (hfin x hx y hy) (hfin y hy z hz)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin x hx y hy, hfin y hy z hz⟩)
      (hI.internalMetric_triangle V x y z)
  · exact ENNReal.continuousOn_toReal.comp hcont (fun p hp => hfin p.1 hp.1 p.2 hp.2)
  · rw [hI.isOpen_iff U]
    constructor
    · intro h z hz
      obtain ⟨ε, hε, h'⟩ := h z hz
      refine ⟨ε, hε, fun w hw hlt => h' w ?_⟩
      have hle : I z w ≤ (internalMetric I V z w).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal (hfin z (hUV hz) w hw)).1 (hanti z (hUV hz) w hw)
      have hlt' : (internalMetric I V z w).toReal < ε := hlt
      linarith
    · intro h z hz
      obtain ⟨ε, hε, hεU⟩ := h z hz
      obtain ⟨r, hr, hrV⟩ := (hI.isOpen_iff V).1 hVo z (hUV hz)
      obtain ⟨δ, hδ, hδloc⟩ := hI.internalMetric_eq_of_near hnonneg hVo (hUV hz)
      refine ⟨min ε (min δ r), lt_min hε (lt_min hδ hr), fun w hw => ?_⟩
      have hwr : I z w < r := lt_of_lt_of_le hw (le_trans (min_le_right _ _) (min_le_right _ _))
      have hwδ : I z w < δ := lt_of_lt_of_le hw (le_trans (min_le_right _ _) (min_le_left _ _))
      have hwε : I z w < ε := lt_of_lt_of_le hw (min_le_left _ _)
      apply hεU w (hrV w hwr)
      show (internalMetric I V z w).toReal < ε
      rw [hδloc w hwδ, ENNReal.toReal_ofReal (hnonneg z w)]
      exact hwε
  · show ENNReal.ofReal (internalMetric I V z w).toReal = internalMetric (fun u v => (internalMetric I V u v).toReal) V z w
    rw [internalMetric_internalMetric_toReal_of_finite hI (subset_refl V) hfin z w]
    exact ENNReal.ofReal_toReal (hfin z hz w hw)

/-- **Smooth cutoff of `-α log‖·‖` near a compact set avoiding `0`** (R1 step 1). Let `R` bound `K`, and let `ρ` satisfy
`ρ < ‖z‖` on `K`. Then `f = χ · (-α log‖·‖)` with `χ = φ (1 - ψ)`, where `φ` is `1` on `closedBall 0 (R+1)` and vanishes
off `ball 0 (R+2)`, and `ψ` is `1` on `closedBall 0 (ρ/4)` and vanishes off `ball 0 (ρ/2)`. -/
theorem exists_smooth_cutoff_log (α : ℝ) {K : Set ℂ} (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) (hKne : K.Nonempty) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ ∀ᶠ x in 𝓝ˢ K, f x = -α * Real.log ‖x‖ := by
  obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hKne continuous_norm.continuousOn
  have hz0ne : z0 ≠ 0 := fun h => hK0 (h ▸ hz0)
  obtain ⟨ρ, hρ, hKρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ K, ρ < ‖z‖ :=
    ⟨‖z0‖ / 2, half_pos (norm_pos_iff.2 hz0ne), fun z hz => by
      have h := isMinOn_iff.1 hmin z hz
      have := norm_pos_iff.2 hz0ne
      linarith⟩
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let R : ℝ := |R0|
  have hKR : ∀ z ∈ K, ‖z‖ < R + 1 := fun z hz => by
    have h := hR0 hz
    rw [mem_closedBall, dist_zero_right] at h
    have := le_abs_self R0
    linarith
  let φ : ContDiffBump (0 : ℂ) :=
    { rIn := R + 1, rOut := R + 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let ψ : ContDiffBump (0 : ℂ) :=
    { rIn := ρ / 4, rOut := ρ / 2, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  let χ : ℂ → ℝ := fun z => φ z * (1 - ψ z)
  let G : ℂ → ℝ := fun z => -α * Real.log ‖z‖
  let f : ℂ → ℝ := fun z => χ z * G z
  have hχsm : ContDiff ℝ ∞ χ := φ.contDiff.mul (contDiff_const.sub ψ.contDiff)
  have hχc : HasCompactSupport χ := φ.hasCompactSupport.mul_right
  have hχ0 : ∀ z : ℂ, ‖z‖ < ρ / 4 → χ z = 0 := fun z hz => by
    have h1 : ψ z = 1 := ψ.one_of_mem_closedBall (by
      rw [mem_closedBall, dist_zero_right]; exact hz.le)
    show φ z * (1 - ψ z) = 0
    rw [h1, sub_self, mul_zero]
  let O : Set ℂ := {z : ℂ | ‖z‖ < R + 1} ∩ {z : ℂ | ρ / 2 < ‖z‖}
  have hOo : IsOpen O := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const continuous_norm)
  have hKO : K ⊆ O := fun z hz => ⟨hKR z hz, lt_trans (half_lt_self hρ) (hKρ z hz)⟩
  have hχ1 : ∀ z ∈ O, χ z = 1 := fun z hz => by
    have h1 : φ z = 1 := φ.one_of_mem_closedBall (by
      rw [mem_closedBall, dist_zero_right]; exact (show ‖z‖ ≤ R + 1 from hz.1.le))
    have h2 : ψ z = 0 := ψ.zero_of_le_dist (by
      rw [dist_zero_right]; exact (show ρ / 2 ≤ ‖z‖ from hz.2.le))
    show φ z * (1 - ψ z) = 1
    rw [h1, h2, sub_zero, one_mul]
  have hfc : HasCompactSupport f := hχc.mul_right
  have hfsm : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x‖ < ρ / 4
    · have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
        show χ y * G y = 0
        rw [hχ0 y hy, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp only [norm_zero] at hx
        linarith
      have hlog : ContDiffAt ℝ ∞ (fun z : ℂ => Real.log ‖z‖) x :=
        (contDiffAt_norm (𝕜 := ℝ) hx0).log (norm_ne_zero_iff.2 hx0)
      have hG : ContDiffAt ℝ ∞ G x := (contDiffAt_const (c := -α)).mul hlog
      exact hχsm.contDiffAt.mul hG
  refine ⟨f, ⟨hfsm, hfc, subset_univ _⟩, ?_⟩
  refine Filter.eventually_of_mem (hOo.mem_nhdsSet.2 hKO) (fun x hx => ?_)
  show χ x * (-α * Real.log ‖x‖) = -α * Real.log ‖x‖
  rw [hχ1 x hx, one_mul]

/-- **R1 is proved**: `CutoffInternalLengthStmt ξ α` for every `ξ, α`. Items 1-4 of
`notes/fp-gaps/CHATGPT-n1-n2-11-13-inputs.md` section 3.1; the proof is the route of its section 3.2. -/
theorem cutoffInternalLengthStmt (ξ α : ℝ) : CutoffInternalLengthStmt ξ α := by
  intro d hd V hVo hVc hVcpt h0
  obtain ⟨f, hfT, hfeq⟩ := exists_smooth_cutoff_log α hVcpt h0 hVc.nonempty.closure
  have hf : Continuous f := hfT.1.continuous
  have hfc : HasCompactSupport f := hfT.2.1
  have hfg : ∀ x ∈ V, f =ᶠ[𝓝 x] (fun z : ℂ => -α * Real.log ‖z‖) := fun x hx =>
    Filter.Eventually.filter_mono (nhds_le_nhdsSet (subset_closure hx)) hfeq
  -- Items 1 and 3 for the cutoff, from the repository lemmas.
  obtain ⟨hfinW, hEL⟩ := weylScaling_continuous_compactSupport_length d ξ f hd hf hfc
  have hfin' : ∀ u v, weylScaling d ξ f u v ≠ ⊤ := fun u v => (hfinW u v).ne
  have hEq3 : ∀ x ∈ V, ∀ y ∈ V, internalMetric (weylLogReal d ξ α) V x y =
      internalMetric (fun u v => (weylScaling d ξ f u v).toReal) V x y := fun x _ y _ =>
    RootedLocal.internalMetric_weylScaling_eq_of_eventuallyEq hd hf hfc hVo hVc hfg
  -- Item 2: finiteness of the logarithmic weight on `V` (local equality with the cutoff, then connectedness).
  have hWgfin : ∀ x ∈ V, ∀ y ∈ V, weylScaling d ξ (fun z : ℂ => -α * Real.log ‖z‖) x y ≠ ⊤ := by
    have hloc : ∀ x ∈ V, ∃ t > 0, ∀ a b, d x a < t → d x b < t →
        weylScaling d ξ (fun z : ℂ => -α * Real.log ‖z‖) a b ≠ ⊤ := by
      intro x hx
      obtain ⟨ρ, hρ, hρf⟩ := Metric.eventually_nhds_iff.1 (hfg x hx)
      obtain ⟨t, ht, heq, hne⟩ := RootedLocal.weylScaling_eq_near hd hf hρ hρf
      refine ⟨t, ht, fun a b ha hb => ?_⟩
      rw [← heq a b ha hb]
      exact hne a b ha hb
    intro x hx y hy
    exact RootedLocal.weylScaling_ne_top_of_connected hd hVo hVc.isPreconnected hloc hx hy
  -- Item 4: the internal distance of the global Euclidean length metric `W_f` on `V`.
  have hEfin : ∀ x ∈ V, ∀ y ∈ V,
      internalMetric (fun u v => (weylScaling d ξ f u v).toReal) V x y ≠ ⊤ := fun x hx y hy =>
    HarmonicBalls.S11m.internalMetric_ne_top_of_isConnected hEL hVo hVc hx hy
  have hE := isLengthMetricOn_internalReal hEL hVo hEfin
  have hG : IsLengthMetricOn V (internalReal (weylLogReal d ξ α) V) :=
    hE.congr_of_eqOn fun x hx y hy => (congrArg ENNReal.toReal (hEq3 x hx y hy)).symm
  have hGfin : ∀ x ∈ V, ∀ y ∈ V, internalMetric (weylLogReal d ξ α) V x y ≠ ⊤ := fun x hx y hy => by
    rw [hEq3 x hx y hy]
    exact hEfin x hx y hy
  exact ⟨⟨f, hfT, hfeq, hfin', hEL, hEq3⟩, hWgfin, hGfin, hG⟩

end FirstPassS11ah

end
