import HarmonicBalls.Draft.Section11

/-!
# Section 11: the local events of [C44] and their inclusions

Corrected paper, correction [C44]. `internalMetric D O x y` is `D(x, y; O)` and `internalDiam D δ X` is `diam^δ_D(X)`.

The quantities of note section 2.4 are `d_i = diam_D(K_i; O_i)` with the closures `K₀ = closure (T \ B_{3δ}(W))`,
`K₁ = closure V`, `K₂ = closure (B_{3δ}(W) \ V)` and `O_i = B_δ(K_i)`. Since `B_δ(closure X) = B_δ(X)`
(`Metric.thickening_closure`), `d_i = internalDiam D δ K_i`.

The stronger events `E₁ = {L > A, a₀ > d₀}`, `E₂(M) = {a₁ > d₁, μ(U) > M S}`, `E₃ = {a₂ > d₂}` (note eq. (3.1)) imply the
events `Ẽ₁`, `Ẽ₂(M)`, `Ẽ₃` of the corrected paper (`pinchFirstEvent`, `pinchSecondEvent`, `pinchThirdEvent`) on every
metric `D` with `0 ≤ D`. This holds almost surely by `IsLQGMetricOfField`. Only monotonicity is used. The inclusion
`D(Q̄', ∂Q) ≤ D(Q', ∂Q)` needs no continuity of `D`, so the equality (3.4) is not needed.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- The component `Ω_geom` containing `0` of `B₇ \ (closure (B_{2δ}(Q)) ∪ closure (B_{2δ}(W)))` (note section 2.1,
corrected paper lines 3189-3201). It is deterministic. -/
noncomputable def pinchOmegaGeom (W Q : Set ℂ) (δ : ℝ) : Set ℂ :=
  connectedComponentIn (ball (0 : ℂ) 7 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0

/-- `A = sup_{x ∈ ∂B₅} D(0, x; Ω_geom)` (note section 2.4). -/
noncomputable def pinchLocalA (D : ℂ → ℂ → ℝ) (W Q : Set ℂ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ sphere (0 : ℂ) 5, internalMetric D (pinchOmegaGeom W Q δ) 0 x

/-- `L = D(Q̄', ∂Q)` (note section 2.4). -/
noncomputable def pinchLocalL (D : ℂ → ℂ → ℝ) (Q' Q : Set ℂ) : ℝ :=
  setDist D (closure Q') (frontier Q)

/-- The local first event `E₁ = {L > A, a₀ > d₀}` (note eq. (3.1)), with `a₀ = D(0, ∂B_δ)` and
`d₀ = diam^δ_D(K₀)`, `K₀ = closure (T \ B_{3δ}(W))`. -/
def pinchFirstEventLocal (D : ℂ → ℂ → ℝ) (W T Q' Q : Set ℂ) (δ : ℝ) : Prop :=
  pinchLocalA D W Q δ < ENNReal.ofReal (pinchLocalL D Q' Q) ∧
    internalDiam D δ (closure (T \ thickening (3 * δ) W)) < ENNReal.ofReal (setDist D {0} (sphere 0 δ))

/-- The local second event `E₂(M) = {a₁ > d₁, μ(U) > M S}` (note eq. (3.1)), with `a₁ = D(∂B_δ, ∂B_{2δ})`,
`d₁ = diam^δ_D(K₁)`, `K₁ = closure V`, and `S = annulusGreenPotentialSup μ 0 3 6`. -/
def pinchSecondEventLocal (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U V : Set ℂ) (δ M : ℝ) : Prop :=
  internalDiam D δ (closure V) < ENNReal.ofReal (setDist D (sphere 0 δ) (sphere 0 (2 * δ))) ∧
    ENNReal.ofReal M * annulusGreenPotentialSup μ 0 3 6 < μ U

/-- The local third event `E₃ = {a₂ > d₂}` (note eq. (3.1)), with `a₂ = D(∂B_{2δ}, ∂B_{3δ})`, `d₂ = diam^δ_D(K₂)`,
`K₂ = closure (B_{3δ}(W) \ V)`. -/
def pinchThirdEventLocal (D : ℂ → ℂ → ℝ) (V W : Set ℂ) (δ : ℝ) : Prop :=
  internalDiam D δ (closure (thickening (3 * δ) W \ V)) <
    ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))

/-- Note equation (3.3): `Ω_geom ⊆ (B_{2δ}(Q ∪ W))ᶜ`. -/
theorem pinchOmegaGeom_subset (W Q : Set ℂ) (δ : ℝ) :
    pinchOmegaGeom W Q δ ⊆ (thickening (2 * δ) (Q ∪ W))ᶜ := by
  intro z hz
  unfold pinchOmegaGeom at hz
  have hF := connectedComponentIn_subset _ _ hz
  rw [thickening_union, mem_compl_iff, mem_union]
  rintro (h | h)
  · exact hF.2 (mem_union_left _ (subset_closure h))
  · exact hF.2 (mem_union_right _ (subset_closure h))

/-- The supremum in the first conjunct of `pinchFirstEvent` is at most `A`, by antitonicity of the internal metric in
its domain and (3.3). -/
theorem pinchLocal_sup_le (D : ℂ → ℂ → ℝ) (W Q : Set ℂ) (δ : ℝ) :
    (⨆ x ∈ sphere (0 : ℂ) 5, internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) ≤ pinchLocalA D W Q δ :=
  iSup₂_mono fun x _ => internalMetric_anti D (pinchOmegaGeom_subset W Q δ) 0 x

/-- For a nonnegative `D` and a positive `setDist D (closure A) B`, passing from `closure A` to `A` does not decrease
the distance: the infimum over the smaller set is at least the infimum over the closure. -/
theorem setDist_closure_le (D : ℂ → ℂ → ℝ) (hD : ∀ u v, 0 ≤ D u v) (A B : Set ℂ)
    (hpos : 0 < setDist D (closure A) B) : setDist D (closure A) B ≤ setDist D A B := by
  unfold setDist at hpos ⊢
  have hne : (image2 D (closure A) B).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, Real.sInf_empty] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨hcl, hB⟩ := image2_nonempty_iff.mp hne
  have hAne : A.Nonempty := closure_nonempty_iff.mp hcl
  have hbdd : BddBelow (image2 D (closure A) B) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, _, y, _, rfl⟩
    exact hD x y
  exact csInf_le_csInf hbdd (image2_nonempty_iff.mpr ⟨hAne, hB⟩) (image2_subset subset_closure Subset.rfl)

/-- `diam^δ_D(X) ≤ diam^δ_D(closure X)`: the two internal domains agree (`Metric.thickening_closure`), and the endpoint
set grows. -/
theorem internalDiam_le_closure (D : ℂ → ℂ → ℝ) (δ : ℝ) (X : Set ℂ) :
    internalDiam D δ X ≤ internalDiam D δ (closure X) := by
  unfold internalDiam
  rw [thickening_closure]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
  exact le_iSup₂_of_le x (subset_closure hx) (le_iSup₂_of_le y (subset_closure hy) le_rfl)

/-- Note equation (3.2), first event: on a nonnegative metric, `E₁ ⊆ Ẽ₁` (`pinchFirstEvent`). -/
theorem pinchFirstEventLocal_subset (D : ℂ → ℂ → ℝ) (hD : ∀ u v, 0 ≤ D u v) (W T Q' Q : Set ℂ) (δ : ℝ)
    (h : pinchFirstEventLocal D W T Q' Q δ) : pinchFirstEvent D W T Q' Q δ := by
  obtain ⟨hA, hd⟩ := h
  have hL : 0 < pinchLocalL D Q' Q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hA)
  have hLQ : pinchLocalL D Q' Q ≤ setDist D Q' (frontier Q) :=
    setDist_closure_le D hD Q' (frontier Q) hL
  refine ⟨?_, (internalDiam_le_closure D δ _).trans_lt hd⟩
  calc (⨆ x ∈ sphere (0 : ℂ) 5, internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x)
      ≤ pinchLocalA D W Q δ := pinchLocal_sup_le D W Q δ
    _ < ENNReal.ofReal (pinchLocalL D Q' Q) := hA
    _ ≤ ENNReal.ofReal (setDist D Q' (frontier Q)) := ENNReal.ofReal_le_ofReal hLQ

/-- Note equation (3.2), second event: `E₂(M) ⊆ Ẽ₂(M)` (`pinchSecondEvent`), for every metric. -/
theorem pinchSecondEventLocal_subset (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U V : Set ℂ) (δ M : ℝ)
    (h : pinchSecondEventLocal μ D U V δ M) : pinchSecondEvent μ D U V δ M :=
  ⟨(internalDiam_le_closure D δ V).trans_lt h.1, h.2⟩

/-- Note equation (3.2), third event: `E₃ ⊆ Ẽ₃` (`pinchThirdEvent`), for every metric. -/
theorem pinchThirdEventLocal_subset (D : ℂ → ℂ → ℝ) (V W : Set ℂ) (δ : ℝ)
    (h : pinchThirdEventLocal D V W δ) : pinchThirdEvent D V W δ :=
  (internalDiam_le_closure D δ _).trans_lt h

#print axioms pinchFirstEventLocal_subset
#print axioms pinchSecondEventLocal_subset
#print axioms pinchThirdEventLocal_subset

end HarmonicBalls
