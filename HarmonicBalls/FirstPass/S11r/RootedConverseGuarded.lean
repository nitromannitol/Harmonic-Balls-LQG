import HarmonicBalls.FirstPass.S11r.RootedConverse

/-!
# Guarded converse of the rooted metric identification on buffered windows

The guarded form of `ae_rootedLocalIdent_windowConverse_buffered` (RootedConverse.lean). The length-metric clause `hLenC` is assumed only for the roots `z ∈ A`, and the window identity is concluded
only for the roots `z ∈ A`, for an arbitrary set `A`. The unguarded converse is the case `A = univ` and is kept unchanged.
The proof is that of the unguarded converse, with the guard `z ∈ A` carried through `filter_upwards`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Guarded converse of the rooted metric identification on buffered windows.** Same hypotheses as
`ae_rootedLocalIdent_windowConverse_buffered`, except that the length clause `hLenC` is required only for the roots in
`A`, and the conclusion (the almost-sure window identity for every admissible root shift) holds for almost every root
`z` in `ball c₁ r₁` with `z ∈ A`. -/
theorem ae_rootedLocalIdent_windowConverse_buffered_guarded {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {α₀ γ : ℝ} {c₁ : ℂ} {r₁ : ℝ}
    (uc dc : ℕ → ℂ) (ur dr : ℕ → ℝ) (hbuf : ∀ j, ur j + dist (uc j) (dc j) < dr j)
    (hdens : ∀ z ∈ ball c₁ r₁, z ≠ 0 → ∀ b : ℝ, 0 < b →
      ∃ j, z ∈ ball (uc j) (ur j) ∧ closedBall (dc j) (dr j) ⊆ ball z b)
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hDμ : Measurable Dμ) (hDd : ∀ x y : ℂ, Measurable fun L : S11n.CanonSpace => Dd L x y)
    {f : ℕ → Set ℂ} (hfm : ∀ n, MeasurableSet (f n))
    (κ : (j : ℕ) → ({φ : ℂ → ℝ // IsTestFunction (ball (dc j) (dr j)) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : (j : ℕ) → (MeanZeroTest (ball (dc j) (dr j)) → ℝ) →
      C(↥(ball (dc j) (dr j) ×ˢ ball (dc j) (dr j) : Set (ℂ × ℂ)), ℝ))
    (X : ℕ → ℕ → ℂ) (R : ℕ → ℕ → ℝ) (pq : ℕ → ℕ → ℂ × ℂ)
    (hXd : ∀ j, ∀ r : ℝ, 0 < r → ∀ x ∈ ball (0 : ℂ) r, ∀ ε > 0, ∃ i, ‖X j i‖ < r ∧ dist (X j i) x < ε)
    (hκm : ∀ j, Measurable (κ j)) (hmm : ∀ j, Measurable (m j))
    (hbase : ∀ j, ∀ᵐ z ∂(volume.restrict (ball (uc j) (ur j))), ∀ᵐ ω ∂P,
      S11c.translatedPairing hC hcirc z ω ∈ rootedLocalIdentEvent (ball (dc j) (dr j)) (κ j) (m j) Dμ Dd γ z
        (closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j)))
        (fun n => f n ∩ closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j))) (X j) (R j) (pq j))
    (E : ℂ → Ω → ℂ → ℂ → ℝ) (hEuc : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E z ω))
    (hwin : ∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (uc j) (ur j) → ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball (dc j) (dr j) ×ˢ ball (dc j) (dr j) : Set (ℂ × ℂ)),
        ENNReal.ofReal (m j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (E z ω) (ball (dc j) (dr j)) p.1.1 p.1.2)
    (A : Set ℂ)
    (hLenC : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P,
        IsEuclideanLengthMetric (Dd (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u)))) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u →
        ∃ j, z ∈ ball (uc j) (ur j) ∧ ∀ᵐ ω ∂P, ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧
          closedBall z ρ ⊆ ball (dc j) (dr j) ∧
          ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
            windowDecodedMetric (ball (dc j) (dr j)) (m j)
                (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2 (x + z) (y + z) =
              c * Dd (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u)) x y := by
  have hz0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))
  have hshift : ∀ j, ∀ᵐ z ∂(volume.restrict (ball (uc j) (ur j))), ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P,
        addFunPairing (S11c.translatedPairing hC hcirc z ω) u ∈
          rootedLocalIdentEvent (ball (dc j) (dr j)) (κ j) (m j) Dμ Dd γ z
            (closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j)))
            (fun n => f n ∩ closedBall 0 (bufferRadius (uc j) (dc j) (ur j) (dr j))) (X j) (R j) (pq j) :=
    fun j => ae_rootedLocalIdent_shifted_all P hCM hG (α₀ := α₀) (κ j) (m j) Dμ Dd _ _ (X j) (R j) (pq j)
      (hκm j) (hmm j) hDμ hDd measurableSet_closedBall (fun n => (hfm n).inter measurableSet_closedBall) (hbase j)
  have hA := ae_all_iff.2 fun j =>
    (ae_restrict_iff' (measurableSet_ball : MeasurableSet (ball (uc j) (ur j)))).1 (hshift j)
  have hW := ae_all_iff.2 hwin
  filter_upwards [ae_restrict_of_ae hA, ae_restrict_of_ae hW, hEuc, hLenC,
    ae_restrict_of_ae hz0, ae_restrict_mem measurableSet_ball] with z hAz hWz hEz hLz hz0' hzball
  intro hzA b u hadm
  obtain ⟨j, hzj, hbj⟩ := hdens z hzball hz0' b hadm.1
  refine ⟨j, hzj, ?_⟩
  have hzD : z ∈ ball (dc j) (dr j) := by
    rw [mem_ball] at hzj ⊢
    calc dist z (dc j) ≤ dist z (uc j) + dist (uc j) (dc j) := dist_triangle _ _ _
      _ < ur j + dist (uc j) (dc j) := by linarith
      _ < dr j := hbuf j
  have hDsub : ball (dc j) (dr j) ⊆ ball z b := ball_subset_closedBall.trans hbj
  filter_upwards [hAz j hzj b u hadm, hWz j hzj, hEz, hLz hzA b u hadm] with ω hωA hωW hωE hωL
  obtain ⟨bw, hbw, hclw⟩ := hωW
  have hobs : rootedLocalObs γ (ball (dc j) (dr j)) z (addFunPairing (S11c.translatedPairing hC hcirc z ω) u) =
      (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2 :=
    funext fun ψ => rootedLocalObs_shifted_eq hC hcirc γ α₀ (ball (dc j) (dr j)) z ω b u hadm hDsub ψ
  obtain ⟨-, hmet⟩ := hωA
  obtain ⟨c, ρ, hc, hρ, hρD, hid⟩ := windowDecoded_eq_const_mul_of_rootedMetricIdent isOpen_ball hzD
    (m j) (Dd) (addFunPairing (S11c.translatedPairing hC hcirc z ω) u) hωL hωL.continuous_pair
    (X j) (R j) (pq j) (hXd j) hmet (fun k hne h1 h2 => by
      rw [hobs]
      exact windowDecodedMetric_pos_of_clause (m j) _ hωE hbw hclw h1 h2
        (fun h => hne (add_right_cancel h)))
  refine ⟨c, ρ, hc, hρ, hρD, fun x hx y hy => ?_⟩
  rw [← hobs]
  exact hid x hx y hy


end HarmonicBalls
