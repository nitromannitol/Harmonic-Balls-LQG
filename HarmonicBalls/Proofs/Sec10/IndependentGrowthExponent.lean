import HarmonicBalls.Proofs.Sec10.PoleAvoidingCrossingThresholds

/-! # Independent exponents for regularity and annular mass -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- The exponent in the ball-mass ratio need not equal either exponent used
for regularity of the measure. -/
theorem exists_component_middle_annulus_bound_independent_exponent :
    ∃ C : ℝ, 0 < C ∧ ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {U D : Set ℂ}, U ⊆ ball (0 : ℂ) 1 →
      D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t) → z ∉ D →
      ∀ {ρ : ℝ}, 0 < ρ → ∀ {x₀ : ℂ}, annulus x₀ (ρ / 4) ρ ⊆ U →
      ∀ {β C₁m C₁p α : ℝ}, 0 < C₁m → 0 ≤ α →
      annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
      μ (D ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ) →
      α < C₁m * (8 : ℝ) ^ (-β) →
      ⨆ x ∈ annulus x₀ (ρ / 2) (7 / 8 * ρ) ∩ D, odometerExt μ z t x ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ x₀ (ρ / 4) ρ := by
  obtain ⟨C, hC, hbound⟩ := exists_pole_avoiding_component_annulus_odometer_bound
    (s₁ := 1 / 4) (s₂ := 1 / 2) (s₃ := 7 / 8) (s₄ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro μ hμ βminus βplus hV z hz t ht U D hUsub hD hzD ρ hρ x₀ hA β C₁m C₁p α h1m hα0 hv1 hmass hα
  have hanchor := exists_middle_annulus_not_mem_of_outer_mass hρ h1m hα0 hv1 hmass hα
  have hbound' := hbound hμ hV hz ht hUsub hD hzD hρ
    (by simpa [div_eq_mul_inv, mul_comm] using hA)
    (by simpa [div_eq_mul_inv, mul_comm] using hanchor)
  simpa [div_eq_mul_inv, mul_comm] using hbound'

/-- The componentwise mass-or-avoidance estimate follows from one-annulus
odometer decay. The universal constants come from the annular mass and
Harnack bounds; the pole may lie in the containing disc. -/
theorem exists_pole_avoiding_mass_or_avoid_independent_exponent :
    ∃ C₄ c : ℝ, 0 < C₄ ∧ 0 < c ∧
    ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
    ∀ {β βminus βplus : ℝ}, 0 < β → VolumeGrowth μ 1 βminus βplus →
    ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
    ∀ {ρ : ℝ}, 0 < ρ → ∀ {x₀ : ℂ}, closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 →
    ∀ {Λ : Set ℂ}, Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball x₀ ρ) → z ∉ Λ →
    ∀ {N₀ : ℕ}, 200 ≤ N₀ → ∀ {a b C₁m C₁p C₂m C₂p C₃ α : ℝ},
    0 < a → b ∈ Ioo (0 : ℝ) 1 → 0 < C₁m → 0 < C₂p → 0 < C₃ → 0 ≤ α →
    annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
    annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) →
    μ (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ) →
    α ≤ a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * C₁m → α < C₁m * (8 : ℝ) ^ (-β) →
    (∀ j : ℕ, b ^ (Real.log 2 / (2 * Real.log 7) * C₃ * ((N₀ : ℝ) + j)) =
      (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + j)))) →
    max C₄ 1 * (2 : ℝ) ^ (-(2 * β * N₀)) * c * C₂p / C₁m ≤
      a * (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)) →
    VeryGoodCriterionThree μ ρ x₀ N₀ a b C₃ →
    (∀ r : ℝ, 0 < r → ∀ w : ℂ, closedBall w (5 * r) ⊆ ball x₀ ρ →
      IsGoodAnnulus μ r w a b →
      μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ ENNReal.ofReal a * μ (annulus w (3 * r) (5 * r)) →
      (⨆ x ∈ Λ ∩ ball w (4 * r), odometerExt μ z t x) ≤
        ENNReal.ofReal b * ⨆ x ∈ Λ ∩ annulus w (3 * r) (5 * r), odometerExt μ z t x) →
    Λ ∩ closedBall x₀ (ρ / 2) = ∅ := by
  obtain ⟨C₄, hC₄, h68⟩ := component_annulus_mass_le_odometer_of_pole_not_mem
    (s₁ := 1) (s₂ := 3) (s₃ := 5) (s₄ := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨c, hc, h610⟩ := exists_component_middle_annulus_bound_independent_exponent
  refine ⟨C₄, c, hC₄, hc, ?_⟩
  intro μ hμ β βminus βplus hβ hV z hz t ht ρ hρ x₀ hball Λ hΛ hzΛ N₀ hN₀
    a b C₁m C₁p C₂m C₂p C₃ α ha hb h1m h2p hC₃ hα0 hv1 hv2 hmass hα1 hα2 hbpow hN hVG3 hdec
  have hUsub : ball x₀ ρ ⊆ ball (0 : ℂ) 1 := ball_subset_closedBall.trans hball
  have hΛ' : Λ ∈ connectedComponentsIn (ball x₀ ρ ∩ cluster μ 1 z t) := by
    simpa only [inter_comm] using hΛ
  apply pole_avoiding_component_harnack_core hβ hρ hΛ hzΛ ha h1m hC₄ hc h2p hv1 hv2 hmass hα1 hbpow hb.1.le hN
  · intro r hr w hA
    have h := h68 hμ hV hz ht hUsub hΛ' hzΛ (w := w) hr (by simpa only [one_mul] using hA)
    simpa only [one_mul] using h
  · exact h610 hμ hV hz ht hUsub hΛ' hzΛ hρ sdiff_subset h1m hα0 hv1 hmass hα2
  · exact greenPotentialSupMonoStep_proved μ x₀ (ρ / 4) ρ (2 * ρ) (by positivity) (by linarith) (by linarith)
  · intro j hj
    exact pole_avoiding_component_lowMass_smallOdometer hμ hV hz ht hb hN₀ hC₃ hρ hball hVG3 hΛ hzΛ hdec j hj
  · intro d hd hempty
    exact pole_avoiding_component_inter_closedBall_eq_empty hμ hV hz ht hΛ hzΛ hd hempty


/-- For each positive volume-growth exponent and good-annulus frequency,
the decay factor and mass thresholds can be chosen before the measure,
center, pole, time and component. The only remaining analytic hypothesis
is the one-good-annulus decay for the selected component. -/
theorem exists_pole_avoiding_mass_thresholds_independent_exponent
    {β C₃ : ℝ} (hβ0 : 0 < β) (hC₃ : 0 < C₃) :
    ∃ b ∈ Ioo (0 : ℝ) 1, ∃ N₁ : ℝ → ℝ → ℝ → ℕ, ∃ α : ℝ → ℕ → ℝ → ℝ,
      (∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
        200 ≤ N₁ a C₁m C₂p ∧ ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ → α a N₀ C₁m ∈ Ioo (0 : ℝ) 1) ∧
      ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ → ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {ρ : ℝ}, 0 < ρ → ∀ {x₀ : ℂ}, closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 →
      ∀ {Λ : Set ℂ}, Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball x₀ ρ) → z ∉ Λ →
      ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
      ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ →
      annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
      annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) →
      μ (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal (α a N₀ C₁m) * μ (annulus x₀ (ρ / 2) ρ) →
      VeryGoodCriterionThree μ ρ x₀ N₀ a b C₃ →
      (∀ r : ℝ, 0 < r → ∀ w : ℂ, closedBall w (5 * r) ⊆ ball x₀ ρ →
        IsGoodAnnulus μ r w a b →
        μ (Λ ∩ annulus w (3 * r) (5 * r)) ≤ ENNReal.ofReal a * μ (annulus w (3 * r) (5 * r)) →
        (⨆ x ∈ Λ ∩ ball w (4 * r), odometerExt μ z t x) ≤
          ENNReal.ofReal b * ⨆ x ∈ Λ ∩ annulus w (3 * r) (5 * r), odometerExt μ z t x) →
      Λ ∩ closedBall x₀ (ρ / 2) = ∅ := by
  obtain ⟨C₄, c, hC₄, hc, havoid⟩ := exists_pole_avoiding_mass_or_avoid_independent_exponent
  let C' := Real.log 2 / (2 * Real.log 7)
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hCC : 0 < C' * C₃ := mul_pos hC' hC₃
  set b : ℝ := (2 : ℝ) ^ (-(2 * β) / (C' * C₃)) with hb_def
  have hb0 : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (div_neg_of_neg_of_pos (by linarith) hCC)
  have hbpow : ∀ (N₀ : ℕ) (j : ℕ), b ^ (C' * C₃ * ((N₀ : ℝ) + j)) = (2 : ℝ) ^ (-(2 * β * ((N₀ : ℝ) + j))) := by
    intro N₀ j
    rw [hb_def, ← Real.rpow_mul (by norm_num)]
    congr 1
    rw [div_mul_eq_mul_div, div_eq_iff hCC.ne']
    ring
  set θ : ℝ → ℝ → ℝ → ℝ := fun a C₁m C₂p => a * (2 : ℝ) ^ (-β) * C₁m / (max C₄ 1 * c * C₂p) with hθ
  set N₁f : ℝ → ℝ → ℝ → ℕ := fun a C₁m C₂p =>
    max 200 ⌈-Real.log (θ a C₁m C₂p) / (β * Real.log 2)⌉₊ with hN₁f
  set αf : ℝ → ℕ → ℝ → ℝ := fun a N₀ C₁m =>
    a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * min C₁m 1 * (8 : ℝ) ^ (-β) / 2 with hαf
  have h8le : (8 : ℝ) ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2le : ∀ N₀ : ℕ, (2 : ℝ) ^ (-((N₀ : ℝ) * β)) ≤ 1 := fun N₀ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) N₀])
  have hαprop : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m : ℝ, 0 < C₁m → ∀ N₀ : ℕ,
      0 < αf a N₀ C₁m ∧ αf a N₀ C₁m < 1 ∧ αf a N₀ C₁m ≤ a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * C₁m ∧
      αf a N₀ C₁m < C₁m * (8 : ℝ) ^ (-β) := by
    intro a ha C₁m h1m N₀
    have ha0 := ha.1
    have hm0 : 0 < min C₁m 1 := lt_min h1m one_pos
    have hm1 : min C₁m 1 ≤ C₁m := min_le_left _ _
    have hm2 : min C₁m 1 ≤ 1 := min_le_right _ _
    have h2p : 0 < (2 : ℝ) ^ (-((N₀ : ℝ) * β)) := by positivity
    have h8p : 0 < (8 : ℝ) ^ (-β) := by positivity
    have hA : a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right ha.1.le (h2le N₀)) ha.2
    have hA0 : 0 < a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) := mul_pos ha.1 h2p
    simp only [hαf]
    have hA' := hA.le
    refine ⟨by positivity, ?_, ?_, ?_⟩
    · have : a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * min C₁m 1 * (8 : ℝ) ^ (-β) ≤
          a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) := by
        calc a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * min C₁m 1 * (8 : ℝ) ^ (-β) ≤
            a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * 1 * 1 := by gcongr
          _ = a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) := by ring
      linarith
    · have h1 : min C₁m 1 * (8 : ℝ) ^ (-β) / 2 ≤ C₁m := by
        calc min C₁m 1 * (8 : ℝ) ^ (-β) / 2 ≤ C₁m * 1 / 2 := by gcongr
          _ ≤ C₁m := by linarith
      calc a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * min C₁m 1 * (8 : ℝ) ^ (-β) / 2
          = a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * (min C₁m 1 * (8 : ℝ) ^ (-β) / 2) := by ring
        _ ≤ a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * C₁m := by gcongr
    · calc a * (2 : ℝ) ^ (-((N₀ : ℝ) * β)) * min C₁m 1 * (8 : ℝ) ^ (-β) / 2
          ≤ 1 * C₁m * (8 : ℝ) ^ (-β) / 2 := by gcongr
        _ < C₁m * (8 : ℝ) ^ (-β) := by have := mul_pos h1m h8p; linarith
  have hN₁prop : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₂p : ℝ, 0 < C₁m → 0 < C₂p → ∀ N₀ : ℕ, N₁f a C₁m C₂p ≤ N₀ →
      max C₄ 1 * (2 : ℝ) ^ (-(2 * β * N₀)) * c * C₂p / C₁m ≤ a * (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)) := by
    intro a ha C₁m C₂p h1m h2p N₀ hN₀
    have hC4' : 0 < max C₄ 1 := lt_max_of_lt_right one_pos
    have hθpos : 0 < θ a C₁m C₂p := by simp only [hθ]; have := ha.1; positivity
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hc' : ⌈-Real.log (θ a C₁m C₂p) / (β * Real.log 2)⌉₊ ≤ N₀ := (le_max_right 200 _).trans hN₀
    have hceil : -Real.log (θ a C₁m C₂p) / (β * Real.log 2) ≤ N₀ :=
      (Nat.le_ceil _).trans (by exact_mod_cast hc')
    have hX : (2 : ℝ) ^ (-(β * N₀)) ≤ θ a C₁m C₂p := by
      rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_log hθpos]
      refine Real.exp_le_exp.2 ?_
      rw [div_le_iff₀ (mul_pos hβ0 hlog2)] at hceil
      nlinarith
    have e1 : (2 : ℝ) ^ (-(2 * β * N₀)) = (2 : ℝ) ^ (-(β * N₀)) * (2 : ℝ) ^ (-(β * N₀)) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have e2 : (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)) = (2 : ℝ) ^ (-β) * (2 : ℝ) ^ (-(β * N₀)) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have hX0 : 0 ≤ (2 : ℝ) ^ (-(β * N₀)) := by positivity
    have hK : 0 ≤ max C₄ 1 * c * C₂p / C₁m := by positivity
    calc max C₄ 1 * (2 : ℝ) ^ (-(2 * β * N₀)) * c * C₂p / C₁m
        = (max C₄ 1 * c * C₂p / C₁m * (2 : ℝ) ^ (-(β * N₀))) * (2 : ℝ) ^ (-(β * N₀)) := by rw [e1]; ring
      _ ≤ (max C₄ 1 * c * C₂p / C₁m * θ a C₁m C₂p) * (2 : ℝ) ^ (-(β * N₀)) := by gcongr
      _ = a * (2 : ℝ) ^ (-β) * (2 : ℝ) ^ (-(β * N₀)) := by
          simp only [hθ]; field_simp
      _ = a * (2 : ℝ) ^ (-(((N₀ : ℝ) + 1) * β)) := by rw [e2]; ring
  refine ⟨b, ⟨hb0, hb1⟩, N₁f, αf, ?_, ?_⟩
  · intro a ha C₁m C₂p h1m h2p
    exact ⟨le_max_left _ _, fun N₀ _ => ⟨(hαprop a ha C₁m h1m N₀).1, (hαprop a ha C₁m h1m N₀).2.1⟩⟩
  · intro μ hμ βminus βplus hV z hz t ht ρ hρ x₀ hball Λ hΛ hzΛ a ha C₁m C₁p C₂m C₂p h1m h2p N₀ hN₀ hv1 hv2 hmass hVG3 hdec
    have hN200 : 200 ≤ N₀ := (le_max_left _ _).trans hN₀
    obtain ⟨hαpos, _, hα1, hα2⟩ := hαprop a ha C₁m h1m N₀
    exact havoid hμ hβ0 hV hz ht hρ hball hΛ hzΛ hN200 ha.1 ⟨hb0, hb1⟩ h1m h2p hC₃ hαpos.le
      hv1 hv2 hmass hα1 hα2 (hbpow N₀) (hN₁prop a ha C₁m C₂p h1m h2p N₀ hN₀) hVG3 hdec


/-- Uniform mass thresholds give the sharp crossing count at a displaced good
ball, assuming the one-good-annulus decay for every pole-avoiding component. -/
theorem exists_pole_avoiding_crossing_thresholds_independent_exponent
    {β C₃ : ℝ} (hβ0 : 0 < β) (hC₃ : 0 < C₃) :
    ∃ b ∈ Ioo (0 : ℝ) 1, ∃ N₁ : ℝ → ℝ → ℝ → ℕ, ∃ α : ℝ → ℕ → ℝ → ℝ,
      (∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
        200 ≤ N₁ a C₁m C₂p ∧ ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ → α a N₀ C₁m ∈ Ioo (0 : ℝ) 1) ∧
      ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ → ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {ρ : ℝ}, 0 < ρ → ∀ {x₀ : ℂ}, closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 →
      ∀ {w : ℂ}, dist w x₀ < ρ / 6 → μ (annulus x₀ (ρ / 2) ρ) ≠ ∞ →
      ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
      ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ →
      annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
      annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) →
      VeryGoodCriterionThree μ ρ x₀ N₀ a b C₃ →
      (∀ Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball x₀ ρ), z ∉ Λ →
        ∀ r : ℝ, 0 < r → ∀ v : ℂ, closedBall v (5 * r) ⊆ ball x₀ ρ →
        IsGoodAnnulus μ r v a b →
        μ (Λ ∩ annulus v (3 * r) (5 * r)) ≤ ENNReal.ofReal a * μ (annulus v (3 * r) (5 * r)) →
        (⨆ x ∈ Λ ∩ ball v (4 * r), odometerExt μ z t x) ≤
          ENNReal.ofReal b * ⨆ x ∈ Λ ∩ annulus v (3 * r) (5 * r), odometerExt μ z t x) →
      (crossingComponents (cluster μ 1 z t ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤
        ⌈1 / α a N₀ C₁m⌉₊ := by
  obtain ⟨b, hb, N₁, α, hparam, hmass⟩ := exists_pole_avoiding_mass_thresholds_independent_exponent hβ0 hC₃
  refine ⟨b, hb, N₁, α, hparam, ?_⟩
  intro μ hμ βminus βplus hV z hz t ht ρ hρ x₀ hx₀ w hw hfin a ha C₁m C₁p C₂m C₂p hC₁ hC₂ N₀ hN₀ hmassratio hgreen hgood hdec
  have hopen := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ zero_lt_one hV hz ht).1
  have hα := (hparam a ha C₁m C₂p hC₁ hC₂).2 N₀ hN₀
  apply encard_crossingComponents_of_nearby_harnack_away_from_pole_sharp
    μ (cluster μ 1 z t) hopen hα.1 w x₀ z hρ hw hfin
  intro Λ hΛ hzΛ hsmall
  exact hmass hμ hV hz ht hρ hx₀ hΛ hzΛ a ha C₁m C₁p C₂m C₂p hC₁ hC₂ N₀ hN₀
    hmassratio hgreen hsmall hgood (hdec Λ hΛ hzΛ)


end HarmonicBalls
