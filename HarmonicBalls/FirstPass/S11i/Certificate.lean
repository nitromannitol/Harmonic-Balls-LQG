import HarmonicBalls.FirstPass.S11i.Crossing
import HarmonicBalls.Draft.Section11

/-!
# The common local certificate and its inclusion (Lemma 11.13, steps 2 and 4)

Steps 2 and 4 of the written proof, with the explicit common rule [C43]: for the scale-one sets
`U, V, W, T, Q', Q`, a buffer `η > 0`, a domain `O_*` (Step 1; the buffers are not part of
`IsPinchPointConfiguration`), and `M`, the certificate `𝓔_r^f(z; M) = E₁ ∩ E₂ ∩ E₃` is defined by transporting every set
by `w ↦ z + r w` (`r` is the Euclidean radius). The metric is not rescaled.

Proved here (deterministic, for any length metric `D`):
* `certificate_subset_pinchPointEvent`: `𝓔_r(z; M) ⊆ pinchPointEvent μ D U T Q' Q M r z`
  (Draft `HarmonicBalls/Draft/Section11.lean`, eq:pinch-point-event), i.e. Step 4.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace FirstPassS11i

open HarmonicBalls

variable {D : ℂ → ℂ → ℝ}

/-- `K₀ = closure (T \ B_{3η}(W))` (Step 2, scale one). -/
def certK0 (T W : Set ℂ) (η : ℝ) : Set ℂ := closure (T \ thickening (3 * η) W)

/-- `K₁ = closure V` (Step 2, scale one). -/
def certK1 (V : Set ℂ) : Set ℂ := closure V

/-- `K₂ = closure (B_{3η}(W) \ V)` (Step 2, scale one). -/
def certK2 (V W : Set ℂ) (η : ℝ) : Set ℂ := closure (thickening (3 * η) W \ V)

/-- The certificate `𝓔_r^f(z; M) = E₁ ∩ E₂ ∩ E₃` (Step 2, rule [C43]), for the domain `Ostar` (`O_*`), transported to the
centre `z` and Euclidean radius `r`:
* `E₁`: `A < L` and `d₀ < a₀`, where `L = D(closure Q'_r(z), ∂Q_r(z))`,
  `A = sup_{x ∈ ∂B_{5r}(z)} D(z, x; O_*)`, `a₀ = D(z, ∂B_{rη}(z))`, `d₀ = diam_D(K₀; B_{rη}(K₀))`;
* `E₂`: `d₁ < a₁` with `a₁ = D(∂B_{rη}(z), ∂B_{2rη}(z))`, `d₁ = diam_D(K₁; B_{rη}(K₁))`, and
  `M × SG_{3r,6r}(z) < μ(U_r(z))`;
* `E₃`: `d₂ < a₂` with `a₂ = D(∂B_{2rη}(z), ∂B_{3rη}(z))`, `d₂ = diam_D(K₂; B_{rη}(K₂))`. -/
def CertificateEvent (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ) (η M r : ℝ) (z : ℂ) : Prop :=
  ((⨆ x ∈ sphere z (5 * r), internalMetric D (rescaledSet Ostar r z) z x) <
      ENNReal.ofReal (setDist D (closure (rescaledSet Q' r z)) (frontier (rescaledSet Q r z))) ∧
    internalDiam D (r * η) (rescaledSet (certK0 T W η) r z) <
      ENNReal.ofReal (setDist D {z} (sphere z (r * η)))) ∧
  (internalDiam D (r * η) (rescaledSet (certK1 V) r z) <
      ENNReal.ofReal (setDist D (sphere z (r * η)) (sphere z (2 * r * η))) ∧
    ENNReal.ofReal M * annulusGreenPotentialSup μ z (3 * r) (6 * r) < μ (rescaledSet U r z)) ∧
  internalDiam D (r * η) (rescaledSet (certK2 V W η) r z) <
      ENNReal.ofReal (setDist D (sphere z (2 * r * η)) (sphere z (3 * r * η)))

lemma ofReal_le_internalMetric (hD : IsEuclideanLengthMetric D) (O : Set ℂ) (x y : ℂ) :
    ENNReal.ofReal (D x y) ≤ internalMetric D O x y := by
  rw [hD.ofReal_eq_internalMetric]
  unfold internalMetric
  exact le_iInf₂ fun P _ => iInf₂_le P (fun t => mem_univ (P t))

lemma ofReal_le_internalDiam (hD : IsEuclideanLengthMetric D) {δ : ℝ} {A : Set ℂ} {x y : ℂ}
    (hx : x ∈ A) (hy : y ∈ A) : ENNReal.ofReal (D x y) ≤ internalDiam D δ A := by
  unfold internalDiam
  exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (ofReal_le_internalMetric hD _ x y))

lemma sphere_nonempty_of_pos {z : ℂ} {s : ℝ} (hs : 0 < s) : (sphere z s).Nonempty :=
  ⟨z + s, by simp [hs.le]⟩

/-- Each point of `T` lies in `K₀ ∪ K₁ ∪ K₂` (scale one). -/
lemma mem_certK_cover {T V W : Set ℂ} {η : ℝ} {t : ℂ} (ht : t ∈ T) :
    t ∈ certK0 T W η ∨ t ∈ certK1 V ∨ t ∈ certK2 V W η := by
  by_cases hB : t ∈ thickening (3 * η) W
  · by_cases hV : t ∈ V
    · exact Or.inr (Or.inl (subset_closure hV))
    · exact Or.inr (Or.inr (subset_closure ⟨hB, hV⟩))
  · exact Or.inl (subset_closure ⟨ht, hB⟩)

/-- Transported version of `mem_certK_cover`: `rescaledSet T r z ⊆ K₀ ∪ K₁ ∪ K₂` at scale `r`. -/
lemma rescaled_mem_certK_cover {T V W : Set ℂ} {η r : ℝ} {z x : ℂ} (hx : x ∈ rescaledSet T r z) :
    x ∈ rescaledSet (certK0 T W η) r z ∨ x ∈ rescaledSet (certK1 V) r z ∨
      x ∈ rescaledSet (certK2 V W η) r z := by
  unfold rescaledSet at hx ⊢
  obtain ⟨t, ht, rfl⟩ := hx
  rcases mem_certK_cover (V := V) (W := W) (η := η) ht with h | h | h
  · exact Or.inl (mem_image_of_mem _ h)
  · exact Or.inr (Or.inl (mem_image_of_mem _ h))
  · exact Or.inr (Or.inr (mem_image_of_mem _ h))

/-- The certificate implies the pinch-point event (Step 4 of the proof). -/
theorem certificate_subset_pinchPointEvent (hD : IsEuclideanLengthMetric D) (μ : Measure ℂ)
    {Ostar U V W T Q' Q : Set ℂ} {η M r : ℝ} {z : ℂ} (hη : 0 < η) (hr : 0 < r) (h3η : 3 * η < 5)
    (hQ' : (rescaledSet Q' r z).Nonempty) (hF : (frontier (rescaledSet Q r z)).Nonempty)
    (hK02 : (certK0 T W η ∩ certK2 V W η).Nonempty) (hK21 : (certK2 V W η ∩ certK1 V).Nonempty)
    (hE : CertificateEvent μ D Ostar U V W T Q' Q η M r z) :
    pinchPointEvent μ D U T Q' Q M r z := by
  obtain ⟨⟨E1a, E1b⟩, ⟨E2a, E2b⟩, E3⟩ := hE
  have hrη : 0 < r * η := mul_pos hr hη
  have hr1 : r * η < 2 * r * η := by nlinarith
  have hr2 : 2 * r * η < 3 * r * η := by nlinarith
  have hr3 : 3 * r * η < 5 * r := by nlinarith
  have hL : setDist D (closure (rescaledSet Q' r z)) (frontier (rescaledSet Q r z)) ≤
      setDist D (rescaledSet Q' r z) (frontier (rescaledSet Q r z)) := by
    unfold setDist
    refine csInf_le_csInf ⟨0, ?_⟩ (hQ'.image2 hF) ?_
    · rintro _ ⟨a, -, b, -, rfl⟩
      exact dist_nonneg_of_lengthMetric hD a b
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact mem_image2_of_mem (subset_closure ha) hb
  refine ⟨?_, ?_, E2b⟩
  · calc (⨆ x ∈ sphere z (5 * r), ENNReal.ofReal (D z x))
        ≤ ⨆ x ∈ sphere z (5 * r), internalMetric D (rescaledSet Ostar r z) z x :=
          iSup₂_mono fun x _ => ofReal_le_internalMetric hD _ z x
      _ < ENNReal.ofReal (setDist D (closure (rescaledSet Q' r z)) (frontier (rescaledSet Q r z))) := E1a
      _ ≤ ENNReal.ofReal (setDist D (rescaledSet Q' r z) (frontier (rescaledSet Q r z))) :=
          ENNReal.ofReal_le_ofReal hL
  · obtain ⟨p, hp0, hp2⟩ := hK02
    obtain ⟨q, hq2, hq1⟩ := hK21
    have hp0' : (r : ℂ) * p + z ∈ rescaledSet (certK0 T W η) r z := mem_image_of_mem _ hp0
    have hp2' : (r : ℂ) * p + z ∈ rescaledSet (certK2 V W η) r z := mem_image_of_mem _ hp2
    have hq2' : (r : ℂ) * q + z ∈ rescaledSet (certK2 V W η) r z := mem_image_of_mem _ hq2
    have hq1' : (r : ℂ) * q + z ∈ rescaledSet (certK1 V) r z := mem_image_of_mem _ hq1
    have hchain : ∀ x ∈ rescaledSet T r z, ∀ y ∈ rescaledSet T r z,
        ENNReal.ofReal (D x y) ≤
          internalDiam D (r * η) (rescaledSet (certK0 T W η) r z) +
          internalDiam D (r * η) (rescaledSet (certK1 V) r z) +
          internalDiam D (r * η) (rescaledSet (certK2 V W η) r z) := by
      intro x hx y hy
      exact ofReal_dist_le_chain hD (fun a ha b hb => ofReal_le_internalDiam hD ha hb)
        (fun a ha b hb => ofReal_le_internalDiam hD ha hb) (fun a ha b hb => ofReal_le_internalDiam hD ha hb)
        hp0' hp2' hq2' hq1' (rescaled_mem_certK_cover hx) (rescaled_mem_certK_cover hy)
    have hsum := ENNReal.add_lt_add (ENNReal.add_lt_add E1b E2a) E3
    have hnn : ENNReal.ofReal (setDist D {z} (sphere z (r * η))) +
        ENNReal.ofReal (setDist D (sphere z (r * η)) (sphere z (2 * r * η))) +
        ENNReal.ofReal (setDist D (sphere z (2 * r * η)) (sphere z (3 * r * η))) =
        ENNReal.ofReal (setDist D {z} (sphere z (r * η)) + setDist D (sphere z (r * η)) (sphere z (2 * r * η))
          + setDist D (sphere z (2 * r * η)) (sphere z (3 * r * η))) := by
      rw [ENNReal.ofReal_add, ENNReal.ofReal_add]
      all_goals first
        | exact setDist_nonneg hD (singleton_nonempty z) (sphere_nonempty_of_pos hrη)
        | exact setDist_nonneg hD (sphere_nonempty_of_pos hrη) (sphere_nonempty_of_pos (by linarith))
        | exact setDist_nonneg hD (singleton_nonempty z) (sphere_nonempty_of_pos hrη)
        | exact add_nonneg (setDist_nonneg hD (singleton_nonempty z) (sphere_nonempty_of_pos hrη))
            (setDist_nonneg hD (sphere_nonempty_of_pos hrη) (sphere_nonempty_of_pos (by linarith)))
        | exact setDist_nonneg hD (sphere_nonempty_of_pos (by linarith)) (sphere_nonempty_of_pos (by linarith))
    have hcross : setDist D {z} (sphere z (r * η)) + setDist D (sphere z (r * η)) (sphere z (2 * r * η))
        + setDist D (sphere z (2 * r * η)) (sphere z (3 * r * η)) ≤ setDist D {z} (sphere z (5 * r)) := by
      apply le_setDist_of_forall (singleton_nonempty z) (sphere_nonempty_of_pos (by linarith))
      intro x hx y hy
      rw [mem_singleton_iff.mp hx]
      exact crossing_dist_ge hD hrη hr1 hr2 hr3 (mem_sphere.mp hy)
    calc (⨆ x ∈ rescaledSet T r z, ⨆ y ∈ rescaledSet T r z, ENNReal.ofReal (D x y))
        ≤ _ := iSup₂_le fun x hx => iSup₂_le fun y hy => hchain x hx y hy
      _ < _ := hsum
      _ = _ := hnn
      _ ≤ ENNReal.ofReal (setDist D {z} (sphere z (5 * r))) := ENNReal.ofReal_le_ofReal hcross

end FirstPassS11i
