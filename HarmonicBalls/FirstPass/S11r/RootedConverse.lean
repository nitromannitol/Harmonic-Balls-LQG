import HarmonicBalls.FirstPass.S11r.RootedLocalIdent
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic

/-!
# Converse of the rooted metric identification on buffered windows (fp-S11r-rooted-local-ident-d)

* `internalMetric_pos_of_isEuclideanLengthMetric`: the internal metric of a Euclidean length metric is positive off the
  diagonal (the internal metric dominates `ofReal (E x y)` by the triangle inequality; Duplantier-Sheffield Fact 2.2).
* `windowDecodedMetric_pos_of_clause`: the `hpos` input of `windowDecoded_eq_const_mul_of_rootedMetricIdent`, from a
  window clause `decoder = b * internalMetric` with `b > 0`.
* `ae_rootedLocalIdent_windowConverse_buffered`: the almost-sure window identity for every admissible root shift, in the
  form of the binder `hRLIm` of `FirstPassS11ai.ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Internal metric positivity.** For a Euclidean length metric `E` and distinct points `x ≠ y`, the internal metric
`internalMetric E U x y` (infimum of `E`-lengths of paths in `U`) is positive: it is at least the infimum over all paths,
which is `ofReal (E x y) > 0`. -/
theorem internalMetric_pos_of_isEuclideanLengthMetric {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E)
    (U : Set ℂ) {x y : ℂ} (hxy : x ≠ y) : 0 < internalMetric E U x y := by
  have hnn : 0 ≤ E x y := by
    have h1 := hE.triangle x y x
    rw [hE.self_eq_zero, hE.symm y x] at h1
    linarith
  have hpos : 0 < E x y := lt_of_le_of_ne hnn (fun h => hxy (hE.eq_of_eq_zero x y h.symm))
  have hle : internalMetric E univ x y ≤ internalMetric E U x y := by
    unfold internalMetric
    exact le_iInf₂ fun P _ => iInf₂_le P (fun t => Set.mem_univ _)
  have hu : 0 < internalMetric E univ x y := by
    rw [← hE.ofReal_eq_internalMetric]
    exact ENNReal.ofReal_pos.2 hpos
  exact lt_of_lt_of_le hu hle

open Classical in
/-- **Positivity of the decoded window metric (`hpos`).** If the decoder `m` read at `φ` satisfies the window clause
`ofReal (m φ p) = ofReal b * internalMetric E D p` on the window `D × D` with `b > 0`, for a Euclidean length metric `E`,
then the decoded window metric is positive at every pair of distinct points of `D`. -/
theorem windowDecodedMetric_pos_of_clause {D : Set ℂ} (m : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ))
    (φ : MeanZeroTest D → ℝ) {E : ℂ → ℂ → ℝ} {b : ℝ} (hE : IsEuclideanLengthMetric E) (hb : 0 < b)
    (hcl : ∀ p : ↥(D ×ˢ D), ENNReal.ofReal (m φ p) = ENNReal.ofReal b * internalMetric E D p.1.1 p.1.2)
    {x y : ℂ} (hx : x ∈ D) (hy : y ∈ D) (hxy : x ≠ y) : 0 < windowDecodedMetric D m φ x y := by
  have hpair : (x, y) ∈ D ×ˢ D := ⟨hx, hy⟩
  have hval : windowDecodedMetric D m φ x y = m φ ⟨(x, y), hpair⟩ := by
    simp only [windowDecodedMetric, hpair, dite_true]
  have hpv : 0 < ENNReal.ofReal (m φ ⟨(x, y), hpair⟩) := by
    rw [hcl ⟨(x, y), hpair⟩]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hb).ne'
      (internalMetric_pos_of_isEuclideanLengthMetric hE D hxy).ne'
  rw [hval]
  exact ENNReal.ofReal_pos.1 hpv

/-- **Converse window identity for the rooted metric (almost-sure form, buffered windows).**
For each buffer index `j`, the rooted local identification of the unshifted field holds on the window `ball (dc j) (dr j)`
(`hbase`), the decoders `m j` satisfy the window clause at the observation `campbellReferenceObs γ α₀` (`hwin`, which gives
the positivity of the decoded window metric at the shifted observations), the countable families `X j` are dense in every
ball about `0` (`hXd`), and `Dd` is a.s. a Euclidean length metric on every admissible shift (`hLenC`). Then for almost
every root `z` in `ball c₁ r₁`, every admissible shift `(b, u)` and almost every `ω`, there is a buffer index `j` with
`z ∈ ball (uc j) (ur j)` and constants `c, ρ > 0` with `closedBall z ρ ⊆ ball (dc j) (dr j)` and the window identity
`windowDecodedMetric (ball (dc j) (dr j)) (m j) (campbellReferenceObs γ α₀ _ (hC ω) z).2 (x + z) (y + z) = c * Dd (shifted) x y`
on `closedBall 0 ρ`. No sign input is needed: the window identity is `windowDecoded_eq_const_mul_of_rootedMetricIdent`. -/
theorem ae_rootedLocalIdent_windowConverse_buffered {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
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
    (hLenC : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ (b : ℝ) (u : ℂ → ℝ),
      FirstPassS11ai.AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P,
        IsEuclideanLengthMetric (Dd (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u)))) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ (b : ℝ) (u : ℂ → ℝ),
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
  intro b u hadm
  obtain ⟨j, hzj, hbj⟩ := hdens z hzball hz0' b hadm.1
  refine ⟨j, hzj, ?_⟩
  have hzD : z ∈ ball (dc j) (dr j) := by
    rw [mem_ball] at hzj ⊢
    calc dist z (dc j) ≤ dist z (uc j) + dist (uc j) (dc j) := dist_triangle _ _ _
      _ < ur j + dist (uc j) (dc j) := by linarith
      _ < dr j := hbuf j
  have hDsub : ball (dc j) (dr j) ⊆ ball z b := ball_subset_closedBall.trans hbj
  filter_upwards [hAz j hzj b u hadm, hWz j hzj, hEz, hLz b u hadm] with ω hωA hωW hωE hωL
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

#print axioms internalMetric_pos_of_isEuclideanLengthMetric
#print axioms windowDecodedMetric_pos_of_clause
#print axioms ae_rootedLocalIdent_windowConverse_buffered

end HarmonicBalls
