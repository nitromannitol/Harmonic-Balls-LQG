import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_8
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6

/-!
# Large-scale crossings for natural LQG scaling

The argument is adapted from Leonardo Bonanno, lean-formalizations, module
`LQGMetric.Papers.DFGPS.L3_8` at commit `fdb5cad`, itself following
Dubédat, Falconet, Gwynne, Pfeffer and Sun, Lemma 3.8. For the natural
power-law scaling constants, the scaling estimate follows directly from
monotonicity of real powers.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

open LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS.L38 LQGMetric.GM.Tight

variable {γ : ℝ} {D : DistC → ContMetric}

/-- Natural scaling gives arbitrarily large metric distances across annuli
of arbitrarily large radii. -/
theorem ae_far_crossing_power (hγ0 : 0 < γ)
    (hD : IsWeakLQGMetric γ D (fun r => r ^ (xiGamma γ * Q γ))) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWPGFF h P) :
    ∀ᵐ ω ∂P, ∀ N R : ℝ, ∃ ρ : ℝ, R ≤ ρ ∧ ∀ x y : ℂ, ‖x‖ ≤ ρ → 3 / 2 * ρ ≤ ‖y‖ →
      N ≤ (D (h ω)).1 (x, y) := by
  let c : ℝ → ℝ := fun r => r ^ (xiGamma γ * Q γ)
  change IsWeakLQGMetric γ D c at hD
  set ξ := xiGamma γ with hξdef
  have hξ : 0 < ξ := GM.xiGamma_pos hγ0
  have hQ : 0 < Q γ := by unfold Q; positivity
  set κ := ξ * Q γ / 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hscal : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
      δ ^ (ξ * Q γ + κ) ≤ c (δ * r) / c r ∧
        c (δ * r) / c r ≤ δ ^ (ξ * Q γ - κ) := by
    intro δ hδ r hr
    dsimp only [c]
    rw [Real.mul_rpow hδ.1.le hr.le, mul_div_cancel_right₀ _
      (Real.rpow_pos_of_pos hr _).ne']
    constructor
    · exact Real.rpow_le_rpow_of_exponent_ge hδ.1 hδ.2.le (by linarith)
    · exact Real.rpow_le_rpow_of_exponent_ge hδ.1 hδ.2.le (by linarith)
  let δ₀ : ℝ := 1
  have hδ₀ : 0 < δ₀ := zero_lt_one
  obtain ⟨p, hp0, hp1, HA⟩ := ae_frequently_crossing LQGMetric.LM.lmLem3_1a
  obtain ⟨s, hs, Hev⟩ := exists_crossing_event hD (ε := ENNReal.ofReal (1 - p))
    (ENNReal.ofReal_pos.2 (by linarith))
  have hwp := hh.1
  choose E hEm hEc hEae using fun ρ : {ρ : ℝ // 0 < ρ} => Hev P h hwp ρ.1 ρ.2
  have hEp : ∀ ρ, ENNReal.ofReal p ≤ P (E ρ) := fun ρ => by
    have h1 : (1 : ℝ≥0∞) ≤ P (E ρ) + P (E ρ)ᶜ := by
      rw [← measure_univ (μ := P)]
      exact (measure_mono (union_compl_self (E ρ)).symm.subset).trans (measure_union_le _ _)
    have h2 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
      rw [← ENNReal.ofReal_add hp0.le (by linarith)]; simp
    rw [← h2] at h1
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1
      (h1.trans (add_le_add le_rfl (hEc ρ).le))
  set L := Real.log 8 with hLdef
  have hL : 0 < L := Real.log_pos (by norm_num)
  set aG := κ * L / (2 * ξ) with haG
  have haG0 : 0 < aG := by positivity
  have hc1 : 0 < c 1 := hD.tightness.1 1 one_pos
  obtain ⟨m₁, hm₁⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num)).eventually (gt_mem_nhds hδ₀)).exists_forall_of_atTop
  have hEall : ∀ᵐ ω ∂P, ∀ j : ℕ, ω ∈ E ⟨8 ^ j, by positivity⟩ →
      ∀ u ∈ sphere (0 : ℂ) (8 ^ j / 4), ∀ v ∈ sphere (0 : ℂ) (3 * 8 ^ j / 8),
        ENNReal.ofReal (s * c (8 ^ j) * Real.exp (ξ * circleAvg (h ω) (8 ^ j) 0)) ≤
          (D (h ω)).internal (annulus 0 (1 / 8 * 8 ^ j) (1 / 2 * 8 ^ j)) u v :=
    ae_all_iff.2 fun j => hEae ⟨8 ^ j, by positivity⟩
  filter_upwards [HA P h hh E hEm hEp, ae_eventually_circleAvg_good P h hwp haG0, hh.2,
    hD.length P h (isGFFPlusCont_of_wp hwp), hEall] with ω hfreq hgood hnorm hlen hcross
  intro N R
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hgood
  set S := max N 0 / c 1 with hSdef
  set m : ℕ := ⌈S / (s * (κ * L / 2))⌉₊ with hmdef
  have hmS : S < s * Real.exp (κ * L / 2 * m) := by
    have h1 : S / (s * (κ * L / 2)) ≤ m := Nat.le_ceil _
    have h2 : S ≤ s * (κ * L / 2) * m := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    have h3 := Real.add_one_le_exp (κ * L / 2 * m)
    nlinarith
  obtain ⟨m₂, hm₂⟩ := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 8)).eventually
    (eventually_ge_atTop (4 * R)) |>.exists_forall_of_atTop
  obtain ⟨j, hj, hjE⟩ := hfreq (max (max m₁ (m + 1)) (max j₀ m₂))
  have hjm₁ : m₁ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hjm : m + 1 ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hjj₀ : j₀ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj
  have hjm₂ : m₂ ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj
  have h8j : (0 : ℝ) < 8 ^ j := by positivity
  refine ⟨8 ^ j / 4, by linarith [hm₂ j hjm₂], fun x y hx hy => ?_⟩
  have hU : {w : ℂ | 8 ^ j / 4 ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ 3 * 8 ^ j / 8} ⊆
      (annulus 0 (1 / 8 * 8 ^ j) (1 / 2 * 8 ^ j) : Set ℂ) := fun w hw => by
    show 1 / 8 * 8 ^ j < ‖w - 0‖ ∧ ‖w - 0‖ < 1 / 2 * (8 : ℝ) ^ j
    constructor <;> linarith [hw.1, hw.2]
  have hlow := le_of_forall_internal_crossing (y := y) hlen (by linarith) hU
    (by rw [sub_zero]; exact hx) (by rw [sub_zero]; linarith) (hcross j hjE)
  refine le_trans ?_ hlow
  set δ : ℝ := ((8 : ℝ) ^ j)⁻¹ with hδdef
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < δ₀ := by
    have := hm₁ j hjm₁
    rwa [one_div, inv_pow] at this
  have hsc := (hscal δ ⟨hδpos, hδlt⟩ (8 ^ j) h8j).2
  have hδr : δ * 8 ^ j = 1 := by rw [hδdef]; field_simp
  rw [hδr, show ξ * Q γ - κ = κ by rw [hκdef]; ring, div_le_iff₀ (hD.tightness.1 _ h8j),
    Real.rpow_def_of_pos hδpos, hδdef, Real.log_inv, Real.log_pow] at hsc
  have hg := hj₀ j hjj₀
  rw [mul_one] at hg
  have key := final_ineq_S24e (j := (j : ℝ)) (m := (m : ℝ)) hs hc1 hξ (by positivity)
    (by exact_mod_cast (Nat.le_succ m).trans hjm) (by rw [← hLdef] at hsc; convert hsc using 3)
    (by rw [haG] at hg; exact hg) hmS
  rw [hnorm, mul_zero, Real.exp_zero, mul_one, hSdef, div_mul_cancel₀ _ hc1.ne'] at key
  exact (le_max_left N 0).trans key.le

end HarmonicBalls
