import HarmonicBalls.FirstPass.S11i.CanonicalFailure
import HarmonicBalls.FirstPass.S11i.RootedFrequencyShift

/-!
# Step 8: the canonical failure set is measurable (fp-S11i-step8-canonical-failure, z11)

Steps 6-9 of the measurability chain of `notes/fp-gaps/CHATGPT-n3-hT.md` (sections 6-9, lines 174-317).

For a pairing `T : (ℂ → ℝ) → ℝ` and a root `z : ℂ`, the canonical field is `canonFieldOf α₀ T` (the pairings of
`h^α₀ = h^ℂ - α₀ log|·|` modulo constants; `alphaCanon α₀ hC ω = canonFieldOf α₀ (hC ω)`, `alphaCanon_eq_canonFieldOf`).
`canonicalWindowFreq` is the canonical window frequency: `N⁻¹` times the number of `n ∈ [N+1, 2N]` whose certificate
event holds at radius `2⁻ⁿ`, for the canonical measure `K L` and the canonical metric `d L`, `L` being the canonical
field. `canonicalFailure` is the set of pairs `(T, z)` at which that frequency does not converge to `q`.

The failure set is measurable for the product of the pairing σ-algebra `pairingSigmaAlgebra (fun T => T) univ` and the
Borel σ-algebra of `ℂ`. Measurability of the certificate events on `CanonSpace × ℂ` enters only through the hypothesis
`hcert` (to be supplied by `measurableSet_certificateEvent_canonical`). No new input.
-/

namespace HarmonicBalls.FirstPassS11iStep8Transfer

open MeasureTheory Set Filter Topology
open FirstPassS11i

/-- Canonical window frequency (chat 191 §6, §9): `N⁻¹` times the number of `n ∈ [N+1, 2N]` for which the certificate
event of the canonical measure `K L` and the canonical metric `d L` holds at radius `2⁻ⁿ` and root `z`. -/
noncomputable def canonicalWindowFreq (K : S11n.CanonSpace → Measure ℂ) (d : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (L : S11n.CanonSpace) (z : ℂ) (N : ℕ) : ℝ :=
  (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      CertificateEvent (K L) (d L) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ)

/-- Canonical failure set (chat 191 §6, §8): the pairs `(T, z)` of a pairing `T` and a root `z` at which the canonical
window frequency along the canonical field `Φ T` does not converge to `q`. -/
def canonicalFailure (K : S11n.CanonSpace → Measure ℂ) (d : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (q : ℝ) (Φ : ((ℂ → ℝ) → ℝ) → S11n.CanonSpace) :
    Set (((ℂ → ℝ) → ℝ) × ℂ) :=
  {p | ¬ Tendsto (fun N : ℕ => canonicalWindowFreq K d Ostar U V W T Q' Q η M (Φ p.1) p.2 N) atTop (𝓝 q)}

/-- The canonical field of `h^α` depends on the model only through the pairing `hC ω` of `h^ℂ`: `alphaCanon α hC ω`
is the pairing `canonFieldOf α (hC ω)` (both are `φ ↦ (h^ℂ, φ) - α ∫ φ(x) log|x| dx` on mean-zero test functions). -/
theorem alphaCanon_eq_canonFieldOf {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    alphaCanon α hC ω = canonFieldOf α (hC ω) :=
  rfl

/-- The canonical field map `T ↦ canonFieldOf α T` is measurable from the pairing σ-algebra of the identity
(`pairingSigmaAlgebra (fun T => T) univ`, which is the σ-algebra `distributionMeasurableSpace` of the pairing
functionals) to the canonical space. -/
theorem measurable_canonFieldOf_pairing (α : ℝ) :
    Measurable[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ, inferInstance] (canonFieldOf α) :=
  measurable_canonFieldOf α

open Classical in
/-- Counting in the window `[N+1, 2N]`: the cardinality of the `n` in the window with `P n` is the sum of the
indicators of `P n`. -/
theorem ncard_window_eq_sum (P : ℕ → Prop) (N : ℕ) :
    ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℝ) =
      ∑ n ∈ Finset.Icc (N + 1) (2 * N), if P n then (1 : ℝ) else 0 := by
  have hset : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n} =
      ((Finset.Icc (N + 1) (2 * N)).filter P : Set ℕ) := by
    ext n
    simp [Finset.mem_Icc, and_assoc]
  rw [hset, Set.ncard_coe_finset, Finset.card_filter]
  push_cast
  rfl

/-- **Measurability of the canonical failure set (steps 6-9 of the chain, chat 191 §6-§9).** Let `Φ` be a measurable map
from the pairing σ-algebra of the identity to the canonical space, and assume the certificate events of the canonical
decoders are measurable on `CanonSpace × ℂ` (`hcert`, step 5). Then the set of `(T, z)` at which the canonical window
frequency does not converge to `q` is measurable for the product of the pairing σ-algebra and the Borel σ-algebra of `ℂ`. -/
theorem measurableSet_canonicalFailure (K : S11n.CanonSpace → Measure ℂ) (d : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (q : ℝ) (Φ : ((ℂ → ℝ) → ℝ) → S11n.CanonSpace)
    (hΦ : Measurable[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ, inferInstance] Φ)
    (hcert : ∀ n : ℕ, MeasurableSet {p : S11n.CanonSpace × ℂ |
      CertificateEvent (K p.1) (d p.1) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) p.2}) :
    MeasurableSet[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance]
      (canonicalFailure K d Ostar U V W T Q' Q η M q Φ) := by
  classical
  set m : MeasurableSpace (((ℂ → ℝ) → ℝ) × ℂ) :=
    (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance with hm
  -- the map `(T, z) ↦ (Φ T, z)` is measurable
  have hmap : Measurable[m, inferInstance] (fun p : ((ℂ → ℝ) → ℝ) × ℂ => (Φ p.1, p.2)) :=
    (hΦ.comp measurable_fst).prodMk measurable_snd
  -- step 6: each certificate event is measurable on the pairing × ℂ
  have hE : ∀ n : ℕ, MeasurableSet[m] {p : ((ℂ → ℝ) → ℝ) × ℂ |
      CertificateEvent (K (Φ p.1)) (d (Φ p.1)) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) p.2} :=
    fun n => hmap (hcert n)
  -- step 7: each window frequency is measurable (finite sum of indicators, divided by `N`)
  have hF : ∀ N : ℕ, Measurable[m] (fun p : ((ℂ → ℝ) → ℝ) × ℂ =>
      canonicalWindowFreq K d Ostar U V W T Q' Q η M (Φ p.1) p.2 N) := by
    intro N
    have heq : ∀ p : ((ℂ → ℝ) → ℝ) × ℂ, canonicalWindowFreq K d Ostar U V W T Q' Q η M (Φ p.1) p.2 N =
        (∑ n ∈ Finset.Icc (N + 1) (2 * N),
          if CertificateEvent (K (Φ p.1)) (d (Φ p.1)) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) p.2
          then (1 : ℝ) else 0) / (N : ℝ) := by
      intro p
      unfold canonicalWindowFreq
      rw [ncard_window_eq_sum]
    have hfun : (fun p : ((ℂ → ℝ) → ℝ) × ℂ =>
        canonicalWindowFreq K d Ostar U V W T Q' Q η M (Φ p.1) p.2 N) =
        fun p => (∑ n ∈ Finset.Icc (N + 1) (2 * N),
          if CertificateEvent (K (Φ p.1)) (d (Φ p.1)) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) p.2
          then (1 : ℝ) else 0) / (N : ℝ) :=
      funext heq
    rw [hfun]
    exact Measurable.div_const (Finset.measurable_sum _ fun n _ => Measurable.ite (hE n) measurable_const
      measurable_const) _
  -- step 8-9: the non-convergence set is measurable (countable intersections and unions of the sets
  -- `{|avg N - q| ≤ 1/(m+1)}`, as in `measurableSet_not_tendsto_real`)
  exact @HarmonicBalls.FirstPassS11iCanonFailure.measurableSet_not_tendsto_real
    (((ℂ → ℝ) → ℝ) × ℂ) m (fun N p => canonicalWindowFreq K d Ostar U V W T Q' Q η M (Φ p.1) p.2 N) hF q

/-- The canonical failure set along the canonical field `canonFieldOf α₀` of the insertion `α₀` (the Φ of
`alphaCanon α₀`, `alphaCanon_eq_canonFieldOf`) is measurable under the same hypotheses on the certificate events. -/
theorem measurableSet_canonicalFailure_alpha (K : S11n.CanonSpace → Measure ℂ) (d : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (q α₀ : ℝ)
    (hcert : ∀ n : ℕ, MeasurableSet {p : S11n.CanonSpace × ℂ |
      CertificateEvent (K p.1) (d p.1) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) p.2}) :
    MeasurableSet[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance]
      (canonicalFailure K d Ostar U V W T Q' Q η M q (canonFieldOf α₀)) :=
  measurableSet_canonicalFailure K d Ostar U V W T Q' Q η M q (canonFieldOf α₀)
    (measurable_canonFieldOf_pairing α₀) hcert

end HarmonicBalls.FirstPassS11iStep8Transfer
