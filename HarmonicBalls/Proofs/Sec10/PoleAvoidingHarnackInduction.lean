import HarmonicBalls.Proofs.Sec10.PoleAvoidingLowMass
import HarmonicBalls.Proofs.Sec10.PoleAvoidingInnerBall
import HarmonicBalls.Proofs.Sec10.PoleAvoidingAnnulusAssembly
import HarmonicBalls.Proofs.Sec10.PoleAvoidingAnnulusHarnack
import HarmonicBalls.Proofs.Sec6.GreenMono

/-! # Harnack induction for a component avoiding the pole -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped ENNReal

/-- The deterministic Harnack induction applies to a local component that
omits the pole, with component versions of the annular mass and odometer
bounds and with shell decay supplied explicitly. -/
theorem pole_avoiding_component_harnack_core
    {μ : Measure ℂ} {β : ℝ} (hβ : 0 < β) {z x₀ : ℂ} {t ρ : ℝ} (hρ : 0 < ρ)
    {Λ : Set ℂ} (hΛ : Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball x₀ ρ)) (hzΛ : z ∉ Λ)
    {N₀ : ℕ} {a b C₁m C₁p C₂m C₂p C₃ C' C₄ c α : ℝ}
    (ha : 0 < a) (h1m : 0 < C₁m) (hC₄ : 0 < C₄) (hc : 0 < c) (h2p : 0 < C₂p)
    (hv1 : annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))
    (hv2 : annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p))
    (hmass : μ (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ))
    (hα1 : α ≤ a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * C₁m)
    (hbpow : ∀ j : ℕ, b ^ (C' * C₃ * ((N₀ : ℝ) + j)) = (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + j))))
    (hb0 : 0 ≤ b)
    (hN₀ : max C₄ 1 * (2 : ℝ) ^ (-(2 * β * N₀)) * c * C₂p / C₁m ≤
      a * (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)))
    (h68 : ∀ r : ℝ, 0 < r → ∀ w : ℂ, annulus w r (7 * r) ⊆ ball x₀ ρ →
      μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤
        ENNReal.ofReal C₄ * ⨆ x ∈ annulus w r (7 * r) ∩ Λ, odometerExt μ z t x)
    (h610 : (⨆ x ∈ annulus x₀ (ρ / 2) (7 / 8 * ρ) ∩ Λ, odometerExt μ z t x) ≤
        ENNReal.ofReal c * annulusGreenPotentialSup μ x₀ (ρ / 4) ρ)
    (hE : annulusGreenPotentialSup μ x₀ (ρ / 4) ρ ≤ annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ))
    (h613 : ∀ j : ℕ, (∀ r : ℝ, 0 < r → ∀ w ∈ ball (0 : ℂ) 1,
        annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ j) →
        μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤
          ENNReal.ofReal a * annulusBallMassSize μ β ρ x₀ * ENNReal.ofReal (shellScale N₀ j ^ β)) →
      ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1)), odometerExt μ z t x ≤
        ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + j))) *
          ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ j), odometerExt μ z t x)
    (hD : ∀ d ∈ Ioo (ρ / 2) ρ, Λ ∩ annulus x₀ (ρ / 2) d = ∅ → Λ ∩ closedBall x₀ (ρ / 2) = ∅) :
    Λ ∩ closedBall x₀ (ρ / 2) = ∅ := by
  set M := annulusBallMassSize μ β ρ x₀ with hMdef
  set A' := annulus x₀ (ρ / 4) (2 * ρ) with hA'def
  obtain ⟨hY0, hYt, hM0, hMt, hMlo, -⟩ := ratio_facts h1m hv1
  have hSG : annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) ≤ ENNReal.ofReal C₂p * μ A' :=
    (ENNReal.div_le_iff hY0 hYt).1 hv2.2
  have hΛsub : Λ ⊆ cluster μ 1 z t ∩ ball x₀ ρ := by
    obtain ⟨y, -, rfl⟩ := hΛ; exact connectedComponentIn_subset _ _
  have hAA : annulus x₀ (ρ / 2) ρ ⊆ A' := annulus_subset_annulus (by linarith) (by linarith)
  have hC4' : 0 < max C₄ 1 := lt_max_of_lt_right one_pos
  -- the main case: the iteration of Lemmas 6.13 and 6.8
  set C₄' := max C₄ 1 with hC4'def
  set V : ℕ → ℝ≥0∞ := fun j =>
    ⨆ x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ j), odometerExt μ z t x with hVdef
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℝ, ∀ j, k j = a * shellScale N₀ j ^ β := ⟨_, fun _ => rfl⟩
  have hk' : ∀ j, k j = a * (2 : ℝ) ^ (-(((N₀ : ℝ) + j) * β)) := fun j => by rw [hk, shellScale_rpow]
  have hkpos : ∀ j, 0 ≤ k j := fun j => by rw [hk']; positivity
  have hKform : ∀ j, ENNReal.ofReal a * M * ENNReal.ofReal (shellScale N₀ j ^ β) =
      ENNReal.ofReal (k j) * M := fun j => by
    rw [hk, ENNReal.ofReal_mul ha.le]; ring
  have hsub_ρ : ∀ j, annulus x₀ (ρ / 2) (shellOuterRadius ρ j) ⊆ annulus x₀ (ρ / 2) ρ :=
    fun j => annulus_subset_annulus le_rfl (by linarith [shellOuterRadius_le hρ j])
  have hann : ∀ (w : ℂ) (r : ℝ), 0 < r → annulus w (3 * r) (5 * r) ⊆ annulus w r (7 * r) :=
    fun w r hr => annulus_subset_annulus (by linarith) (by linarith)
  have hV0 : V 0 ≤ ENNReal.ofReal c * (ENNReal.ofReal C₂p * μ A') := by
    refine le_trans ?_ (h610.trans (mul_le_mul_right (hE.trans hSG) _))
    exact biSup_mono fun x hx =>
      ⟨annulus_subset_annulus le_rfl (shellOuterRadius_le hρ 0) hx.2, hx.1⟩
  have hmass0 : ∀ r : ℝ, 0 < r → ∀ w ∈ ball (0 : ℂ) 1,
      annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ 0) →
      μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ ENNReal.ofReal a * M * ENNReal.ofReal (shellScale N₀ 0 ^ β) := by
    intro r hr w _ hsub
    rw [hKform, hk']
    calc μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ μ (Λ ∩ annulus x₀ (ρ / 2) ρ) :=
          measure_mono (inter_subset_inter_right _ ((hann w r hr).trans (hsub.trans (hsub_ρ 0))))
      _ ≤ ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ) := hmass
      _ ≤ ENNReal.ofReal α * μ A' := mul_le_mul_right (measure_mono hAA) _
      _ ≤ ENNReal.ofReal (a * (2 : ℝ) ^ (-((N₀ : ℝ) * β))) * (ENNReal.ofReal C₁m * μ A') := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          gcongr
      _ ≤ ENNReal.ofReal (a * (2 : ℝ) ^ (-((N₀ : ℝ) * β))) * M := mul_le_mul_right hMlo _
      _ = ENNReal.ofReal (a * (2 : ℝ) ^ (-(((N₀ : ℝ) + ((0 : ℕ) : ℝ)) * β))) * M := by norm_num
  have hmass_succ : ∀ j : ℕ, ENNReal.ofReal C₄' * V (j + 1) ≤ ENNReal.ofReal (k (j + 1)) * M →
      ∀ r : ℝ, 0 < r → ∀ w ∈ ball (0 : ℂ) 1,
      annulus w r (7 * r) ⊆ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1)) →
      μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤
        ENNReal.ofReal a * M * ENNReal.ofReal (shellScale N₀ (j + 1) ^ β) := by
    intro j hj r hr w _ hsub
    rw [hKform]
    have hAB : annulus w r (7 * r) ⊆ ball x₀ ρ := (hsub.trans (hsub_ρ _)).trans sdiff_subset
    have h1 := h68 r hr w hAB
    calc μ (Λ ∩ annulus w (3 * r) (5 * r))
          ≤ ENNReal.ofReal C₄ * ⨆ x ∈ annulus w r (7 * r) ∩ Λ, odometerExt μ z t x := h1
      _ ≤ ENNReal.ofReal C₄' * V (j + 1) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _))
            (biSup_mono fun x hx => ⟨hx.2, hsub hx.1⟩)
      _ ≤ ENNReal.ofReal (k (j + 1)) * M := hj
  have hP : ∀ j : ℕ, ENNReal.ofReal C₄' * V (j + 1) ≤ ENNReal.ofReal (k (j + 1)) * M := by
    intro j
    induction j with
    | zero =>
      have h1 := h613 0 hmass0
      have hμA : μ A' ≤ ENNReal.ofReal (1 / C₁m) * M := by
        calc μ A' = ENNReal.ofReal (1 / C₁m * C₁m) * μ A' := by
              rw [one_div_mul_cancel h1m.ne', ENNReal.ofReal_one, one_mul]
          _ = ENNReal.ofReal (1 / C₁m) * (ENNReal.ofReal C₁m * μ A') := by
              rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
          _ ≤ ENNReal.ofReal (1 / C₁m) * M := mul_le_mul_right hMlo _
      have hreal : C₄' * (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + ((0 : ℕ) : ℝ)))) * c * C₂p * (1 / C₁m) ≤
          k (0 + 1) := by
        have e1 : (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + ((0 : ℕ) : ℝ)))) = (2 : ℝ) ^ (-(2 * β * N₀)) := by norm_num
        have e2 : k (0 + 1) = a * (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)) := by rw [hk']; norm_num
        rw [e1, e2, mul_one_div]
        exact hN₀
      calc ENNReal.ofReal C₄' * V (0 + 1) ≤
          ENNReal.ofReal C₄' * (ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + ((0 : ℕ) : ℝ)))) * V 0) :=
            mul_le_mul_right h1 _
        _ ≤ ENNReal.ofReal C₄' * (ENNReal.ofReal ((2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + ((0 : ℕ) : ℝ))))) *
            (ENNReal.ofReal c * (ENNReal.ofReal C₂p * (ENNReal.ofReal (1 / C₁m) * M)))) := by
            rw [hbpow]; gcongr; exact hV0.trans (by gcongr)
        _ = ENNReal.ofReal (C₄' * (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + ((0 : ℕ) : ℝ)))) * c * C₂p *
            (1 / C₁m)) * M := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
            ring
        _ ≤ ENNReal.ofReal (k (0 + 1)) * M := mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _
    | succ j ih =>
      have h1 := h613 (j + 1) (hmass_succ j ih)
      have hbj : 0 ≤ b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ))) := Real.rpow_nonneg hb0 _
      have hreal : b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ))) * k (j + 1) ≤ k (j + 1 + 1) := by
        have h2 : (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ)))) ≤ (2 : ℝ) ^ (-β) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          push_cast
          nlinarith [mul_nonneg hβ.le (Nat.cast_nonneg (α := ℝ) N₀),
            mul_nonneg hβ.le (Nat.cast_nonneg (α := ℝ) j)]
        have e : k (j + 1 + 1) = (2 : ℝ) ^ (-β) * k (j + 1) := by
          rw [hk', hk', mul_left_comm, ← Real.rpow_add (by norm_num)]
          congr 2
          push_cast
          ring
        rw [hbpow, e]
        exact mul_le_mul_of_nonneg_right h2 (hkpos _)
      calc ENNReal.ofReal C₄' * V (j + 1 + 1) ≤
          ENNReal.ofReal C₄' * (ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ)))) *
            V (j + 1)) := mul_le_mul_right h1 _
        _ = ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ)))) *
            (ENNReal.ofReal C₄' * V (j + 1)) := by ring
        _ ≤ ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ)))) *
            (ENNReal.ofReal (k (j + 1)) * M) := mul_le_mul_right ih _
        _ = ENNReal.ofReal (b ^ (C' * C₃ * ((N₀ : ℝ) + ((j + 1 : ℕ) : ℝ))) * k (j + 1)) * M := by
            rw [ENNReal.ofReal_mul hbj]; ring
        _ ≤ ENNReal.ofReal (k (j + 1 + 1)) * M := mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _
  -- conclusion: the odometer vanishes on `Λ̃_t ∩ 𝔸_{ρ/2,d}(x₀)`
  have hL : ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ / 2 ^ 40 := by
    have : (2 : ℝ)⁻¹ ^ 50 ≤ 1 / 2 ^ 40 := by norm_num
    calc ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ * (1 / 2 ^ 40) := mul_le_mul_of_nonneg_left this hρ.le
      _ = ρ / 2 ^ 40 := by ring
  have hL0 : 0 ≤ ρ * (2 : ℝ)⁻¹ ^ 50 := by positivity
  refine hD (3 / 4 * ρ - 224 * (ρ * (2 : ℝ)⁻¹ ^ 50)) ⟨by linarith, by linarith⟩
    (eq_empty_iff_forall_notMem.2 fun x hx => ?_)
  obtain ⟨hxΛ, hxA⟩ := hx
  have hxj : ∀ j : ℕ, ENNReal.ofReal C₄' * odometerExt μ z t x ≤ ENNReal.ofReal (k (j + 1)) * M := by
    intro j
    refine le_trans (mul_le_mul_right ?_ _) (hP j)
    exact le_iSup₂_of_le (f := fun x (_ : x ∈ Λ ∩ annulus x₀ (ρ / 2) (shellOuterRadius ρ (j + 1))) =>
      odometerExt μ z t x) x ⟨hxΛ, annulus_subset_annulus le_rfl (le_shellOuterRadius hρ (j + 1)) hxA⟩ le_rfl
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (k (j + 1)) * M) atTop (𝓝 0) := by
    have hs : Tendsto (fun j : ℕ => shellScale N₀ (j + 1)) atTop (𝓝 0) := by
      simp only [shellScale, dyadicScale]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_atTop_mono (f := id) (g := fun j : ℕ => N₀ + (j + 1))
          (fun j => show j ≤ N₀ + (j + 1) by omega) tendsto_id)
    have hs' : Tendsto (fun j : ℕ => shellScale N₀ (j + 1) ^ β) atTop (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.comp hs
      rwa [Real.zero_rpow hβ.ne'] at this
    have hq : Tendsto (fun j : ℕ => k (j + 1)) atTop (𝓝 0) := by
      simp_rw [hk]
      simpa using hs'.const_mul a
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hq) (Or.inr hMt)
    simpa using this
  have h0 : ENNReal.ofReal C₄' * odometerExt μ z t x ≤ 0 := ge_of_tendsto' hlim hxj
  have hx0 : odometerExt μ z t x = 0 :=
    (mul_eq_zero.1 (le_zero_iff.1 h0)).resolve_left (ENNReal.ofReal_pos.2 hC4').ne'
  have hxB : x ∈ ball x₀ ρ := (hΛsub hxΛ).2
  have hxz : x ≠ z := fun h => hzΛ (h ▸ hxΛ)
  simp only [odometerExt, hxz, ↓reduceIte, ENNReal.ofReal_eq_zero] at hx0
  have hcl := ((hΛsub hxΛ).1).2.resolve_left hxz
  rw [odometer] at hx0
  linarith

end HarmonicBalls
