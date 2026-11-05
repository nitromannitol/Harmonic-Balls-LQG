import HarmonicBalls.Steps.Sec11.PinchLocalEdgeCover
import HarmonicBalls.Steps.Sec11.PinchShortEdgeContraction
import HarmonicBalls.Steps.Sec11.WeylLocalLower
import HarmonicBalls.Steps.Sec11.WeylLocality

/-! # Local comparisons and internal Weyl metrics -/

namespace HarmonicBalls

open Set Filter
open scoped ENNReal Topology

/-- Arbitrarily accurate local comparisons of length metrics imply an exact
comparison of their internal distances. -/
theorem IsEuclideanLengthMetric.internalMetric_le_of_local_exp_comparison
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {U : Set ℂ} (hU : IsOpen U)
    (hlocal : ∀ ε > (0 : ℝ), ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∀ y z,
      D x y < r → D x z < r → E y z ≤ Real.exp ε * D y z)
    (x y : ℂ) : internalMetric E U x y ≤ internalMetric D U x y := by
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp ε)) (𝓝[>] 0) (𝓝 1) := by
    have hcont := (ENNReal.continuous_ofReal.comp Real.continuous_exp).tendsto (0 : ℝ)
    change Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp ε)) (𝓝 (0 : ℝ))
      (𝓝 (ENNReal.ofReal (Real.exp 0))) at hcont
    simpa only [Real.exp_zero, ENNReal.ofReal_one] using hcont.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have ht' := ENNReal.Tendsto.mul_const ht (b := internalMetric D U x y) (Or.inl one_ne_zero)
  have ht'' : Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp ε) * internalMetric D U x y)
      (𝓝[>] 0) (𝓝 (internalMetric D U x y)) := by
    simpa only [one_mul] using ht'
  apply ge_of_tendsto ht''
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hD.internalMetric_le_const_mul_of_short_edges hE hEnonneg hU (Real.exp_pos ε)
    (fun p hp => hD.path_short_edge_comparison_of_local (Real.exp ε) (hlocal ε hε) p hp) x y

/-- Locally equal length metrics remain arbitrarily close after the same
bounded continuous nonpositive Weyl shift. -/
theorem IsEuclideanLengthMetric.weylScaling_local_exp_comparison_of_local_eq
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ c : ℝ} (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (hf : Continuous f) (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    (hscaledE : IsEuclideanLengthMetric (fun x y => (weylScaling E ξ f x y).toReal))
    {U : Set ℂ} (hlocal : ∀ x ∈ U, ∃ W : Set ℂ, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, ∀ z ∈ W, D y z = E y z)
    {ε : ℝ} (hε : 0 < ε) (x : ℂ) (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ y z,
      (weylScaling E ξ f x y).toReal < r → (weylScaling E ξ f x z).toReal < r →
      (weylScaling D ξ f y z).toReal ≤ Real.exp ε * (weylScaling E ξ f y z).toReal := by
  obtain ⟨W, hW, hxW, heq⟩ := hlocal x hx
  obtain ⟨rD, hrD, hDcomp⟩ := hD.weylScaling_local_comparison hξ f hf hl hu x
    (show 0 < ε / 2 by linarith)
  obtain ⟨rE, hrE, hEcomp⟩ := hE.weylScaling_local_comparison hξ f hf hl hu x
    (show 0 < ε / 2 by linarith)
  let V : Set ℂ := W ∩ {y | D y x < rD} ∩ {y | E y x < rE}
  have hV : IsOpen V := (hW.inter (isOpen_lt (hD.continuous_left x) continuous_const)).inter
    (isOpen_lt (hE.continuous_left x) continuous_const)
  have hxV : x ∈ V := by
    simp only [V, mem_inter_iff, mem_ofPred_eq, hD.self_eq_zero, hE.self_eq_zero]
    exact ⟨⟨hxW, hrD⟩, hrE⟩
  obtain ⟨r, hr, hrV⟩ := (hscaledE.isOpen_iff V).mp hV x hxV
  refine ⟨r, hr, ?_⟩
  intro y z hy hz
  have hyV := hrV y hy
  have hzV := hrV z hz
  have hDy : D x y < rD := by simpa only [hD.symm x y, mem_ofPred_eq] using hyV.1.2
  have hDz : D x z < rD := by simpa only [hD.symm x z, mem_ofPred_eq] using hzV.1.2
  have hEy : E x y < rE := by simpa only [hE.symm x y, mem_ofPred_eq] using hyV.2
  have hEz : E x z < rE := by simpa only [hE.symm x z, mem_ofPred_eq] using hzV.2
  have hden := (hEcomp y z hEy hEz).1
  have hnum := (hDcomp y z hDy hDz).2
  have hdist := heq y hyV.1.1 z hzV.1.1
  have hexp : Real.exp (ξ * f x + ε / 2) =
      Real.exp ε * Real.exp (ξ * f x - ε / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (weylScaling D ξ f y z).toReal ≤ Real.exp (ξ * f x + ε / 2) * D y z := hnum
    _ = Real.exp ε * (Real.exp (ξ * f x - ε / 2) * E y z) := by
      rw [hdist, hexp]
      ring
    _ ≤ Real.exp ε * (weylScaling E ξ f y z).toReal :=
      mul_le_mul_of_nonneg_left hden (Real.exp_nonneg ε)

/-- The internal metric after a common Weyl shift depends only on the
local values of the underlying length metric. -/
theorem IsEuclideanLengthMetric.weylScaling_internalMetric_eq_of_local_eq
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ c : ℝ} (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (hf : Continuous f) (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    (hscaledD : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal))
    (hscaledE : IsEuclideanLengthMetric (fun x y => (weylScaling E ξ f x y).toReal))
    {U : Set ℂ} (hU : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ W : Set ℂ, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, ∀ z ∈ W, D y z = E y z) (x y : ℂ) :
    internalMetric (fun a b => (weylScaling D ξ f a b).toReal) U x y =
      internalMetric (fun a b => (weylScaling E ξ f a b).toReal) U x y := by
  have hnonnegD (a b : ℂ) : 0 ≤ (weylScaling D ξ f a b).toReal := ENNReal.toReal_nonneg
  have hnonnegE (a b : ℂ) : 0 ≤ (weylScaling E ξ f a b).toReal := ENNReal.toReal_nonneg
  apply le_antisymm
  · exact hscaledE.internalMetric_le_of_local_exp_comparison hscaledD hnonnegD hU
      (fun ε hε x hx => hD.weylScaling_local_exp_comparison_of_local_eq hE hξ f hf hl hu
        hscaledE hlocal hε x hx) x y
  · apply hscaledD.internalMetric_le_of_local_exp_comparison hscaledE hnonnegE hU
    intro ε hε x hx
    apply hE.weylScaling_local_exp_comparison_of_local_eq hD hξ f hf hl hu hscaledD _ hε x hx
    intro a ha
    obtain ⟨W, hW, haW, heq⟩ := hlocal a ha
    exact ⟨W, hW, haW, fun b hb c hc => (heq b hb c hc).symm⟩

/-- If two Weyl weights agree on an open set, the resulting metrics agree
on a neighborhood of every point of that set. -/
theorem IsEuclideanLengthMetric.weylScaling_locally_eq_of_eqOn
    {D E F : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hF : IsEuclideanLengthMetric F)
    (ξ : ℝ) (f g : ℂ → ℝ)
    (hEscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hFscale : ∀ x y, ENNReal.ofReal (F x y) = weylScaling D ξ g x y)
    {U : Set ℂ} (hU : IsOpen U) (hfg : ∀ z ∈ U, f z = g z)
    (x : ℂ) (hx : x ∈ U) : ∃ W : Set ℂ, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, ∀ z ∈ W, E y z = F y z := by
  obtain ⟨rF, hrF, hEF⟩ := hD.weylScaling_le_of_eqOn_near hF ξ f g hEscale hFscale
    hU hfg hx
  obtain ⟨rE, hrE, hFE⟩ := hD.weylScaling_le_of_eqOn_near hE ξ g f hFscale hEscale
    hU (fun z hz => (hfg z hz).symm) hx
  let W : Set ℂ := {y | E y x < rE} ∩ {y | F y x < rF}
  have hW : IsOpen W := (isOpen_lt (hE.continuous_left x) continuous_const).inter
    (isOpen_lt (hF.continuous_left x) continuous_const)
  have hxW : x ∈ W := by
    simp only [W, mem_inter_iff, mem_ofPred_eq, hE.self_eq_zero, hF.self_eq_zero]
    exact ⟨hrE, hrF⟩
  refine ⟨W, hW, hxW, ?_⟩
  intro y hy z hz
  have hEy : E x y < rE := by simpa only [hE.symm x y, mem_ofPred_eq] using hy.1
  have hEz : E x z < rE := by simpa only [hE.symm x z, mem_ofPred_eq] using hz.1
  have hFy : F x y < rF := by simpa only [hF.symm x y, mem_ofPred_eq] using hy.2
  have hFz : F x z < rF := by simpa only [hF.symm x z, mem_ofPred_eq] using hz.2
  exact le_antisymm (hEF y z hFy hFz) (hFE y z hEy hEz)

/-- Locality survives a second bounded continuous nonpositive Weyl shift. -/
theorem IsEuclideanLengthMetric.internalMetric_weylScaling_twice_eq_of_eqOn
    {D E F : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hF : IsEuclideanLengthMetric F)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f g k : ℂ → ℝ)
    (hk : Continuous k) (hl : ∀ z, c ≤ k z) (hu : ∀ z, k z ≤ 0)
    (hEscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hFscale : ∀ x y, ENNReal.ofReal (F x y) = weylScaling D ξ g x y)
    (hEk : IsEuclideanLengthMetric (fun x y => (weylScaling E ξ k x y).toReal))
    (hFk : IsEuclideanLengthMetric (fun x y => (weylScaling F ξ k x y).toReal))
    {U : Set ℂ} (hU : IsOpen U) (hfg : ∀ z ∈ U, f z = g z) (x y : ℂ) :
    internalMetric (fun a b => (weylScaling E ξ k a b).toReal) U x y =
      internalMetric (fun a b => (weylScaling F ξ k a b).toReal) U x y := by
  apply hE.weylScaling_internalMetric_eq_of_local_eq hF hξ k hk hl hu hEk hFk hU
  exact fun z hz => hD.weylScaling_locally_eq_of_eqOn hE hF ξ f g hEscale hFscale hU hfg z hz

#print axioms IsEuclideanLengthMetric.weylScaling_locally_eq_of_eqOn
#print axioms IsEuclideanLengthMetric.internalMetric_weylScaling_twice_eq_of_eqOn

#print axioms IsEuclideanLengthMetric.weylScaling_local_exp_comparison_of_local_eq
#print axioms IsEuclideanLengthMetric.weylScaling_internalMetric_eq_of_local_eq

#print axioms IsEuclideanLengthMetric.internalMetric_le_of_local_exp_comparison

end HarmonicBalls
