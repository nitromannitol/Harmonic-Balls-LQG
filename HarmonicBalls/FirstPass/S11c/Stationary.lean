import HarmonicBalls.FirstPass.S11c.Vague
import HarmonicBalls.FirstPass.S11c.Event

/-!
# Proposition 11.7, stationarity of the scale events under the normalized dilation (fp-S11c, owner n1)

FIRST-PASS NEW (deterministic). If `m` is the γ-LQG limit of a circle profile `h` and `m'` is the γ-LQG limit of the
normalized dilated profile `h'_e(z) = h_e(z/2) - c` (`T` of `continuousCircleDilation`, which subtracts the value at
`(1/2, 0)`), then the cone-mass event at the origin at dyadic scale `2^{-n}` for `m'` is the event at scale `2^{-(n+1)}`
for `m`: `E_n(m') ↔ E_{n+1}(m)`. The proof: uniqueness of the LQG limit (`IsLQGLimit.unique`), identification of `m'` with
`4·2^{γ²/2}e^{-γc} · push_{2·} m` (`isLQGLimit_dilate`), and the dilation covariance of the event
(`coneMassEvent_map_smul_two`). The scale index `dyadicScale n = (2⁻¹)^n` moves to `dyadicScale (n+1)` because
`dyadicScale n / 2 = dyadicScale (n+1)`, and the centre `0` is fixed.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

theorem coneMassEvent_of_isLQGLimit_dilate {γ c : ℝ} {hε : ℝ → ℂ → ℝ} (hmeas : ∀ e, Measurable (hε e))
    {m m' : Measure ℂ} (hm : IsLQGLimit γ hε m)
    (hm' : IsLQGLimit γ (fun e z => hε (e / 2) (z / 2) - c) m')
    {Q : Set ℂ} (hQ : IsCone Q) (M : ℝ) (n : ℕ) :
    coneMassEvent m' Q M (dyadicScale n) 0 ↔ coneMassEvent m Q M (dyadicScale (n + 1)) 0 := by
  have hK : 0 < 4 * 2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * c)) := by positivity
  have hm'eq : m' = ENNReal.ofReal (4 * 2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * c))) •
      m.map (fun w : ℂ => (2 : ℝ) • w) :=
    IsLQGLimit.unique hm' (isLQGLimit_dilate hmeas hm)
  rw [hm'eq]
  refine (coneMassEvent_map_smul_two m hQ hK 0 (dyadicScale n)).trans ?_
  rw [dyadicScale_half, zero_div]

/-- The normalized dilation of a circle profile, `T h (e, z) = h(e/2, z/2) - h(1/2, 0)` (the affine pull-back of
`continuousCircleDilation`, Proofs/GFF/ContinuousCircleDilationMixing.lean:19, in the profile coordinates). -/
noncomputable def normalizedDilation (hε : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun e z => hε (e / 2) (z / 2) - hε (1 / 2) 0

lemma normalizedDilation_measurable {hε : ℝ → ℂ → ℝ} (hmeas : ∀ e, Measurable (hε e)) (e : ℝ) :
    Measurable (normalizedDilation hε e) :=
  ((hmeas (e / 2)).comp (measurable_id.div_const 2)).sub_const _

/-- Iterated stationarity: the scale events of the `k`-fold normalized dilation at scale `2^{-j}` are the scale events of
the original limit at scale `2^{-(j+k)}`, that is `E_j(T^k h) = E_{j+k}(h)` (paper Lemma 11.7, `T` the dilation). -/
theorem coneMassEvent_iterate_dilate {γ : ℝ} {Q : Set ℂ} (hQ : IsCone Q) (M : ℝ) (k : ℕ) :
    ∀ (hε : ℝ → ℂ → ℝ), (∀ e, Measurable (hε e)) → ∀ {m mk : Measure ℂ},
      IsLQGLimit γ hε m → IsLQGLimit γ ((normalizedDilation)^[k] hε) mk →
      ∀ j : ℕ, (coneMassEvent mk Q M (dyadicScale j) 0 ↔ coneMassEvent m Q M (dyadicScale (j + k)) 0) := by
  induction k with
  | zero =>
    intro hε hmeas m mk hm hmk j
    rw [Function.iterate_zero_apply] at hmk
    have hmk' : mk = m := IsLQGLimit.unique hmk hm
    rw [hmk', Nat.add_zero]
  | succ k ih =>
    intro hε hmeas m mk hm hmk j
    have hG : IsLQGLimit γ (normalizedDilation hε)
        (ENNReal.ofReal (4 * 2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * hε (1 / 2) 0))) •
          m.map (fun w : ℂ => (2 : ℝ) • w)) :=
      isLQGLimit_dilate (c := hε (1 / 2) 0) hmeas hm
    rw [Function.iterate_succ_apply] at hmk
    have h1 := ih (normalizedDilation hε) (normalizedDilation_measurable hmeas) hG hmk j
    have h2 := coneMassEvent_of_isLQGLimit_dilate (c := hε (1 / 2) 0) hmeas hm hG hQ M (j + k)
    exact h1.trans (h2.trans (by rw [show j + k + 1 = j + (k + 1) by omega]))

end HarmonicBalls
