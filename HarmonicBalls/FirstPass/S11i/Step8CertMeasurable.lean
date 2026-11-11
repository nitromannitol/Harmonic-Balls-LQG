import HarmonicBalls.FirstPass.S11i.CertCanonMeasurable
import HarmonicBalls.FirstPass.S11n
import HarmonicBalls.Proofs.Sec11.PuncturedMetricExhaustionLocality

/-!
# Measurability of the certificate event on the canonical space

Step 5 of the measurability chain: the event
`CertificateEvent (K L) (d L) Ostar U V W T Q' Q η M r z` is measurable in `(L, z) ∈ CanonSpace × ℂ`, where `K` is the
canonical measure decoder and `d` the canonical metric decoder of `LQGCanonicalDecodersMeasurableExistStmt`
(`FirstPass/Frozen/S11n.lean`). The metric decoder is a Euclidean length metric only on a measurable set `G`, so the
statement is the `G`-restricted form.

The clause-by-clause proof is already in the repository for an arbitrary parameter space:
* `FirstPassS11i.measurableSet_certificateEvent` (`CertMeasurable.lean`): the event is measurable when the metric is a
  Euclidean length metric for every parameter (the sup over the sphere, the internal diameters, the set distances and the
  annular Green potential are each handled there);
* `FirstPassS11i.measurableSet_certificateEvent_on` (`CertCanonMeasurable.lean`): the same on a measurable set `G` where
  the decoder is a length metric (the modification off `G` is the Euclidean `dist`).

This file specialises the latter to `Ω = S11n.CanonSpace` and adds the one case split that the lemma does not make:
if `0 ∉ Ostar` or `sphere 0 5 ⊄ Ostar`, the first clause of `CertificateEvent` fails for every parameter, because the
internal metric with an endpoint outside the open set is `⊤` (`internalMetric_eq_top_of_not_mem_endpoints`), so the
event is empty.

Extra hypotheses (each used by the proof): `hOstar : IsOpen Ostar` (open-set route for the internal metric),
`hU : MeasurableSet U` (the mass clause `μ (rescaledSet U r z)`), `hη : 0 < η` and `hr : 0 < r` (radii, used by the affine
homeomorphism and the thickenings), and the measurable set `G` on which the decoder is a length metric (the frozen form).
The support clause `(K L).support = univ` of the frozen form is not needed for measurability and is not assumed.
`_hK` (finiteness of `K L` on compacts) is kept to match the frozen interface; it is not used.
-/

open MeasureTheory Filter Topology Set Metric FirstPassS11i HarmonicBalls
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iStep8Transfer

/-- If `0 ∉ Ostar` or the unit sphere is not contained in `Ostar`, then no parameter satisfies `CertificateEvent`: the
first clause `⨆ x ∈ ∂B_{5r}(z), D_h(z, x; rescaled Ostar) < ...` equals `⊤`, because some internal metric in the
supremum has an endpoint outside the rescaled set. -/
lemma not_certificateEvent_of_not_subset {μ : Measure ℂ} {D : ℂ → ℂ → ℝ}
    {Ostar U V W T Q' Q : Set ℂ} {η M r : ℝ} (hr : 0 < r)
    (h : ¬((0 : ℂ) ∈ Ostar ∧ sphere (0 : ℂ) 5 ⊆ Ostar)) (z : ℂ) :
    ¬ CertificateEvent μ D Ostar U V W T Q' Q η M r z := by
  intro hE
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have key : ∃ x ∈ sphere z (5 * r), internalMetric D (rescaledSet Ostar r z) z x = ⊤ := by
    by_cases hz : z ∈ rescaledSet Ostar r z
    · obtain ⟨y0, hy0, hy0z⟩ := hz
      have hy0z' : (r : ℂ) * y0 + z = z := hy0z
      have h0 : (0 : ℂ) ∈ Ostar := by
        have hmul : (r : ℂ) * y0 = 0 := by linear_combination hy0z'
        rcases mul_eq_zero.mp hmul with h' | h'
        · exact absurd h' hr0
        · rw [h'] at hy0
          exact hy0
      have hsub : ¬ sphere (0 : ℂ) 5 ⊆ Ostar := fun hs => h ⟨h0, hs⟩
      obtain ⟨y, hy, hyO⟩ := not_subset.mp hsub
      refine ⟨(r : ℂ) * y + z, ?_, internalMetric_eq_top_of_not_mem_endpoints _ _ _ _ (Or.inr ?_)⟩
      · rw [mem_sphere_iff_norm, add_sub_cancel_right, norm_mul, mem_sphere_zero_iff_norm.mp hy,
          Complex.norm_real, Real.norm_of_nonneg hr.le]
        ring
      · rintro ⟨y', hy', heq⟩
        have hyy : y' = y := by
          have h1 : (r : ℂ) * y' = (r : ℂ) * y := by linear_combination heq
          exact mul_left_cancel₀ hr0 h1
        exact hyO (hyy ▸ hy')
    · obtain ⟨x, hx⟩ := sphere_nonempty_of_pos (z := z) (s := 5 * r) (by positivity)
      exact ⟨x, hx, internalMetric_eq_top_of_not_mem_endpoints _ _ _ _ (Or.inl hz)⟩
  obtain ⟨x, hx, htop⟩ := key
  have hle : (⊤ : ℝ≥0∞) ≤ ⨆ x ∈ sphere z (5 * r), internalMetric D (rescaledSet Ostar r z) z x := by
    rw [← htop]
    exact le_iSup₂ (f := fun x (_ : x ∈ sphere z (5 * r)) => internalMetric D (rescaledSet Ostar r z) z x) x hx
  unfold CertificateEvent at hE
  exact not_top_lt (lt_of_le_of_lt hle hE.1.1)

/-- **Step 5: measurability of the certificate event on the canonical space.** For a canonical measure decoder `K` and a
canonical metric decoder `d` (measurable as a map into `C(ℂ × ℂ, ℝ)`), the set of pairs `(L, z)` with
`CertificateEvent (K L) (d L) Ostar U V W T Q' Q η M r z` is measurable, restricted to the measurable set `G` on which
`d L` is a Euclidean length metric. -/
theorem measurableSet_certificateEvent_canonical
    (K : ProbabilityTheory.Kernel S11n.CanonSpace ℂ) [ProbabilityTheory.IsSFiniteKernel K]
    (_hK : ∀ L, IsFiniteMeasureOnCompacts (K L))
    (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (hd : Measurable d)
    (Ostar U V W T Q' Q : Set ℂ) (η M r : ℝ)
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G)
    (hmet : ∀ L ∈ G, IsEuclideanLengthMetric (fun x y => d L (x, y)))
    (hOstar : IsOpen Ostar) (hU : MeasurableSet U) (hη : 0 < η) (hr : 0 < r) :
    MeasurableSet ({p : S11n.CanonSpace × ℂ |
        CertificateEvent (K p.1) (fun x y => d p.1 (x, y)) Ostar U V W T Q' Q η M r p.2} ∩ (G ×ˢ univ)) := by
  by_cases h : (0 : ℂ) ∈ Ostar ∧ sphere (0 : ℂ) 5 ⊆ Ostar
  · have hm := measurableSet_certificateEvent_on (Ostar := Ostar) (U := U) (V := V) (W := W) (T := T)
      (Q' := Q') (Q := Q) (η := η) (M := M) (r := r) K hd hG hmet hOstar h.1 h.2 hU hη hr
    have heq : {p : S11n.CanonSpace × ℂ |
          CertificateEvent (K p.1) (fun x y => d p.1 (x, y)) Ostar U V W T Q' Q η M r p.2} ∩ (G ×ˢ univ)
        = {p : S11n.CanonSpace × ℂ | p.1 ∈ G ∧
          CertificateEvent (K p.1) (fun x y => d p.1 (x, y)) Ostar U V W T Q' Q η M r p.2} := by
      ext p
      exact ⟨fun hp => ⟨hp.2.1, hp.1⟩, fun hp => ⟨hp.2, hp.1, trivial⟩⟩
    rw [heq]
    exact hm
  · have heq : {p : S11n.CanonSpace × ℂ |
          CertificateEvent (K p.1) (fun x y => d p.1 (x, y)) Ostar U V W T Q' Q η M r p.2} ∩ (G ×ˢ univ)
        = ∅ := by
      ext p
      exact ⟨fun hp => absurd hp.1 (not_certificateEvent_of_not_subset hr h p.2), fun hp => False.elim hp⟩
    rw [heq]
    exact MeasurableSet.empty

end HarmonicBalls.FirstPassS11iStep8Transfer
