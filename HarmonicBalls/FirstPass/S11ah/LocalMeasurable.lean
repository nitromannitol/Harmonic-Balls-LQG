import Mathlib
import HarmonicBalls.FirstPass.S11i.CertMeasurable
import HarmonicBalls.FirstPass.S11ah.Cutoff
import HarmonicBalls.FirstPass.S11ah.LengthTransport

/-!
# Local-domain measurability of the certificate event

The local decoders `m_D` give a metric only on a disc `B = ball c R`. The whole-plane
`FirstPassS11i.measurableSet_certificateEvent` needs a length metric on all of `ℂ`. This file proves the local-domain
version through the radial lift (`S11ah/Radial.lean`, `S11ah/LengthTransport.lean`):

* `localCertSet c R κ D ...`: the set of `(ω, z)` at which the certificate event holds for the metric `D ω`, read
  through the lift at some admissible radius `radialSeq R j` whose disc contains `closedBall z (7 r)`;
* `measurableSet_localCertSet`: it is measurable (no locality needed: a countable union of measurable pieces);
* `localCertSet_eq_of_locality`: under the named locality hypothesis `CertificateEventLocality` (taken as a hypothesis here), the membership does not depend on the admissible lift.

The buffered containments of the sets `Ostar, U, V, W, T, Q', Q` in `B_7` are not reproved here; they enter only
through `CertificateEventLocality`.
-/

open MeasureTheory Metric Set Filter Topology ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace FirstPassS11ah

/-- Admissible radii `ρ_j = R - R/(j+2)` for the lift onto `ball c R`: positive, below `R`, increasing to `R`. -/
def radialSeq (R : ℝ) (j : ℕ) : ℝ := R - R / ((j : ℝ) + 2)

lemma radialSeq_pos {R : ℝ} (hR : 0 < R) (j : ℕ) : 0 < radialSeq R j := by
  unfold radialSeq
  have h1 : R / ((j : ℝ) + 2) ≤ R / 2 :=
    div_le_div_of_nonneg_left hR.le (by norm_num) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  linarith

lemma radialSeq_lt {R : ℝ} (hR : 0 < R) (j : ℕ) : radialSeq R j < R := by
  unfold radialSeq
  have : 0 < R / ((j : ℝ) + 2) := div_pos hR (by positivity)
  linarith

/-- A compact disc inside `ball c R` lies inside `ball c (radialSeq R j)` for some `j`. -/
lemma exists_radialSeq_of_closedBall_subset {c z : ℂ} {R s : ℝ} (_hR : 0 < R) (hs : 0 ≤ s)
    (h : closedBall z s ⊆ ball c R) : ∃ j : ℕ, closedBall z s ⊆ ball c (radialSeq R j) := by
  have hK : IsCompact (closedBall z s) := isCompact_closedBall z s
  have hne : (closedBall z s).Nonempty := ⟨z, mem_closedBall_self hs⟩
  obtain ⟨x0, hx0, hmax⟩ :=
    hK.exists_isMaxOn hne (continuous_id.dist continuous_const).continuousOn
  have hMR : dist x0 c < R := by
    have := h hx0
    rwa [mem_ball] at this
  have hRM : 0 < R - dist x0 c := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (R / (R - dist x0 c))
  refine ⟨n, fun x hx => ?_⟩
  rw [mem_ball]
  have hxM : dist x c ≤ dist x0 c := isMaxOn_iff.1 hmax x hx
  have h1 : R / ((n : ℝ) + 2) < R - dist x0 c := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hRM] at hn
    nlinarith
  unfold radialSeq
  linarith

lemma radialLift_eq_self_of_le {c : ℂ} {ρ R : ℝ} (hρ : 0 < ρ) {x : ℂ} (hx : ‖x - c‖ ≤ ρ) :
    radialLift c ρ R x = x := by
  unfold radialLift
  rw [radialOut_of_le hρ hx]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The local certificate event: `(ω, z)` such that, for some admissible radius `ρ_j` with
`closedBall z (7 r) ⊆ ball c ρ_j`, the certificate event of the lifted metric `liftMetric c ρ_j R (D ω)` holds at
`(z, r)`. -/
def localCertSet (c : ℂ) (R : ℝ) (κ : Kernel Ω ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M r : ℝ) : Set (Ω × ℂ) :=
  {p | ∃ j : ℕ, closedBall p.2 (7 * r) ⊆ ball c (radialSeq R j) ∧
      FirstPassS11i.CertificateEvent (κ p.1) (liftMetric c (radialSeq R j) R (D p.1))
        Ostar U V W T Q' Q η M r p.2}

/-- **Named hypothesis (locality; lemma name pending).** Under the buffered containments of `Ostar, U, V, W, T, Q', Q`
in `B_7`, the certificate event at `(z, r)` depends only on
the metric on `closedBall z (7 r)`. Taken as a hypothesis, not proved here. -/
def CertificateEventLocality (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) : Prop :=
  ∀ (μ : Measure ℂ) (r : ℝ), 0 < r → ∀ (z : ℂ) (D D' : ℂ → ℂ → ℝ),
    (∀ x ∈ closedBall z (7 * r), ∀ y ∈ closedBall z (7 * r), D x y = D' x y) →
    (FirstPassS11i.CertificateEvent μ D Ostar U V W T Q' Q η M r z ↔
      FirstPassS11i.CertificateEvent μ D' Ostar U V W T Q' Q η M r z)

/-- **Measurability of the local certificate event (local-domain version of
`FirstPassS11i.measurableSet_certificateEvent`).** For a family of local length metrics `D ω` on the disc
`ball c R`, measurable in `ω` at each pair of points of the disc, the set `localCertSet` is measurable in `(ω, z)`. -/
theorem measurableSet_localCertSet {c : ℂ} {R : ℝ} (hR : 0 < R) (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    {D : Ω → ℂ → ℂ → ℝ} (hDm : ∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D ω x y)
    (hD : ∀ ω, IsLengthMetricOn (ball c R) (D ω))
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η) {r : ℝ} (hr : 0 < r) :
    MeasurableSet (localCertSet c R κ D Ostar U V W T Q' Q η M r) := by
  have hset : localCertSet c R κ D Ostar U V W T Q' Q η M r
      = ⋃ j : ℕ, ({p : Ω × ℂ | closedBall p.2 (7 * r) ⊆ ball c (radialSeq R j)} ∩
          {p : Ω × ℂ | FirstPassS11i.CertificateEvent (κ p.1) (liftMetric c (radialSeq R j) R (D p.1))
            Ostar U V W T Q' Q η M r p.2}) := by
    ext p
    simp only [localCertSet, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  rw [hset]
  refine MeasurableSet.iUnion fun j => MeasurableSet.inter ?_ ?_
  · exact ((isOpen_setOf_closedBall_subset isOpen_ball (7 * r)).measurableSet).preimage measurable_snd
  · have hρ : 0 < radialSeq R j := radialSeq_pos hR j
    have hρR : radialSeq R j < R := radialSeq_lt hR j
    exact FirstPassS11i.measurableSet_certificateEvent κ
      (D := fun ω => liftMetric c (radialSeq R j) R (D ω))
      (measurable_liftMetric_family hρ hρR hDm hD)
      (fun ω => continuous_liftMetric hρ hρR (hD ω))
      (fun ω => isEuclideanLengthMetric_liftMetric hρ hρR (hD ω))
      (fun ω x y => (hD ω).nonneg (radialLift_mem hρ hρR x) (radialLift_mem hρ hρR y))
      hOstar h0 hsph hU hη hr

/-- Under the locality hypothesis, membership in `localCertSet` at a point whose `7r`-disc lies in `ball c R` is
the certificate event for any admissible lift. -/
theorem localCertSet_iff_of_locality {c : ℂ} {R : ℝ} (hR : 0 < R) (κ : Kernel Ω ℂ)
    (D : Ω → ℂ → ℂ → ℝ)
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} (hloc : CertificateEventLocality Ostar U V W T Q' Q η M)
    {r : ℝ} (hr : 0 < r) (p : Ω × ℂ) (hp : closedBall p.2 (7 * r) ⊆ ball c R) :
    p ∈ localCertSet c R κ D Ostar U V W T Q' Q η M r
      ↔ ∀ j : ℕ, closedBall p.2 (7 * r) ⊆ ball c (radialSeq R j) →
          FirstPassS11i.CertificateEvent (κ p.1) (liftMetric c (radialSeq R j) R (D p.1))
            Ostar U V W T Q' Q η M r p.2 := by
  -- the lifts at two admissible radii agree with `D p.1` on `closedBall p.2 (7r)`
  have agree : ∀ j k : ℕ, closedBall p.2 (7 * r) ⊆ ball c (radialSeq R j) →
      closedBall p.2 (7 * r) ⊆ ball c (radialSeq R k) →
      ∀ x ∈ closedBall p.2 (7 * r), ∀ y ∈ closedBall p.2 (7 * r),
        liftMetric c (radialSeq R j) R (D p.1) x y = liftMetric c (radialSeq R k) R (D p.1) x y := by
    intro j k hj hk x hx y hy
    have hxj : ‖x - c‖ ≤ radialSeq R j := by
      have := hj hx
      rw [mem_ball, dist_eq_norm] at this
      exact this.le
    have hyj : ‖y - c‖ ≤ radialSeq R j := by
      have := hj hy
      rw [mem_ball, dist_eq_norm] at this
      exact this.le
    have hxk : ‖x - c‖ ≤ radialSeq R k := by
      have := hk hx
      rw [mem_ball, dist_eq_norm] at this
      exact this.le
    have hyk : ‖y - c‖ ≤ radialSeq R k := by
      have := hk hy
      rw [mem_ball, dist_eq_norm] at this
      exact this.le
    unfold liftMetric
    rw [radialLift_eq_self_of_le (radialSeq_pos hR j) hxj, radialLift_eq_self_of_le (radialSeq_pos hR j) hyj,
      radialLift_eq_self_of_le (radialSeq_pos hR k) hxk, radialLift_eq_self_of_le (radialSeq_pos hR k) hyk]
  constructor
  · rintro ⟨j₀, hj₀, hE₀⟩ j hj
    exact (hloc (κ p.1) r hr p.2 (liftMetric c (radialSeq R j₀) R (D p.1))
      (liftMetric c (radialSeq R j) R (D p.1)) (agree j₀ j hj₀ hj)).1 hE₀
  · intro H
    obtain ⟨j₀, hj₀⟩ := exists_radialSeq_of_closedBall_subset hR (by linarith) hp
    exact ⟨j₀, hj₀, H j₀ hj₀⟩

/-- The local certificate indicator (J) for a metric given on the disc `ball c R` (Step 4, formula (J), read through
the lift): `1` when `closedBall z (7 r_n) ⊆ ball c R` and the local certificate event holds at `(z, r_n)`, else `0`,
with `r_n = certScale n`. -/
def localCertLoc (c : ℂ) (R : ℝ) (κ : Kernel Ω ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (n : ℕ) (p : Ω × ℂ) : ℝ := by
  classical
  exact if closedBall p.2 (7 * certScale n) ⊆ ball c R then
    (if p ∈ localCertSet c R κ D Ostar U V W T Q' Q η M (certScale n) then 1 else 0) else 0

/-- Joint measurability of the local certificate indicator in `(ω, z)`: no locality is used (the indicator is a
countable union of measurable pieces, see `measurableSet_localCertSet`). -/
theorem measurable_localCertLoc {c : ℂ} {R : ℝ} (hR : 0 < R) (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    {D : Ω → ℂ → ℂ → ℝ} (hDm : ∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D ω x y)
    (hD : ∀ ω, IsLengthMetricOn (ball c R) (D ω))
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η) (n : ℕ) :
    Measurable (localCertLoc c R κ D Ostar U V W T Q' Q η M n) := by
  classical
  have hr : 0 < certScale n := certScale_pos n
  have hS : MeasurableSet (localCertSet c R κ D Ostar U V W T Q' Q η M (certScale n)) :=
    measurableSet_localCertSet hR κ hDm hD hOstar h0 hsph hU hη hr
  have hA : MeasurableSet {p : Ω × ℂ | closedBall p.2 (7 * certScale n) ⊆ ball c R} :=
    ((isOpen_setOf_closedBall_subset isOpen_ball (7 * certScale n)).measurableSet).preimage measurable_snd
  unfold localCertLoc
  exact Measurable.ite hA (Measurable.ite hS measurable_const measurable_const) measurable_const

end FirstPassS11ah

end
