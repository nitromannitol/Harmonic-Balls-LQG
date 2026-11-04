import HarmonicBalls.Proofs.Sec8.AEGermTriviality
import HarmonicBalls.Proofs.Sec8.OriginGermZeroOne
import HarmonicBalls.Proofs.Sec8.PhaseCircleSections

/-! # Ergodicity of stationary local paths

The Section 8 development uses Leonardo Bonanno's LatticeProb formalization
of the pointwise ergodic theorem.
-/

open MeasureTheory Filter Set

namespace HarmonicBalls

/-- A stationary path is ergodic when its sufficiently late coordinates have
almost-sure local versions in a trivial, countably cofinal germ. -/
theorem ergodic_shift_of_stationary_ae_local_germ
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (germ : ℝ → MeasurableSpace Ω)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (X : ℕ → Ω → E) (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω))
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → E,
      (∀ n, K ≤ n → @Measurable Ω E (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1) :
    Ergodic (fun x : ℕ → E => fun n => x (n + 1)) (P.map (fun ω n => X n ω)) := by
  let path : Ω → ℕ → E := fun ω n => X n ω
  let shift : (ℕ → E) → ℕ → E := fun x n => x (n + 1)
  let Q : Measure (ℕ → E) := P.map path
  have hp : Measurable path := Measurable.of_eval hXm
  have hs : Measurable shift := Measurable.of_eval (fun n => measurable_pi_apply (n + 1))
  have hmp : MeasurePreserving shift Q Q := by
    refine ⟨hs, ?_⟩
    dsimp only [Q]
    rw [Measure.map_map hs hp]
    exact hstat
  have hiter : ∀ k : ℕ, ∀ x : ℕ → E, ∀ n : ℕ, (shift^[k] x) n = x (n + k) := by
    intro k
    induction k with
    | zero => intro x n; simp
    | succ k ih =>
      intro x n
      rw [Function.iterate_succ_apply']
      change (shift^[k] x) (n + 1) = x (n + (k + 1))
      rw [ih]
      congr 1; omega
  have : IsProbabilityMeasure Q := inferInstance
  refine ⟨hmp, ⟨?_⟩⟩
  intro A hA hinv
  have hloc : ∀ ε, 0 < ε → ∃ B : Set Ω,
      MeasurableSet[germ ε] B ∧ path ⁻¹' A =ᵐ[P] B := by
    intro ε hε
    obtain ⟨K, Y, hYm, hYeq⟩ := hlocal ε hε
    let localPath : Ω → ℕ → E := fun ω n => Y (n + K) ω
    have hlm : @Measurable Ω (ℕ → E) (germ ε) _ localPath := by
      let : MeasurableSpace Ω := germ ε
      exact Measurable.of_eval (fun n => hYm (n + K) (by omega))
    refine ⟨localPath ⁻¹' A, hlm hA, ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ n, X (n + K) ω = Y (n + K) ω :=
      ae_all_iff.2 (fun n => hYeq (n + K) (by omega))
    have hinvk : (shift^[K]) ⁻¹' A = A := Function.IsFixedPt.preimage_iterate hinv K
    filter_upwards [hall] with ω hω
    apply propext
    have heq : shift^[K] (path ω) = localPath ω := by
      funext n
      rw [hiter]
      exact hω n
    have hmem := Set.ext_iff.mp hinvk (path ω)
    simpa only [mem_preimage, heq] using hmem.symm
  obtain ⟨B, hB, hBeq⟩ := exists_germ_measurable_event_of_ae_local P germ r hr
    hcofinal hrmono hgmono (path ⁻¹' A) hloc
  have hzero : Q A = 0 ∨ Q A = 1 := by
    dsimp only [Q]
    rw [Measure.map_apply hp hA, measure_congr hBeq]
    exact htrivial B hB
  rw [eventuallyEmptyOrUniv_iff']
  rcases hzero with hz | ho
  · exact Or.inl (ae_eq_empty.mpr hz)
  · right
    apply (ae_eq_univ_iff_measure_eq hA.nullMeasurableSet).mpr
    simpa using ho

/-- A stationary local path is jointly ergodic with the phase-torus doubling. -/
theorem ergodic_phaseTorusDouble_prod_of_stationary_ae_local_germ
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (germ : ℝ → MeasurableSpace Ω)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (X : ℕ → Ω → E) (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω))
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → E,
      (∀ n, K ≤ n → @Measurable Ω E (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1) :
    Ergodic (Prod.map phaseTorusDouble (fun x : ℕ → E => fun n => x (n + 1)))
      (((volume : Measure PhaseCircle).prod volume).prod (P.map (fun ω n => X n ω))) := by
  exact ergodic_phaseTorusDouble_prod _ _
    (ergodic_shift_of_stationary_ae_local_germ P germ r hr hcofinal hrmono hgmono
      X hXm hstat hlocal htrivial)

/-- A stationary path with small-scale versions local to the whole-plane GFF
modulo constants is jointly ergodic with the phase-torus doubling. -/
theorem IsWholePlaneGFF.ergodic_phaseTorusDouble_prod_of_stationary_local_path
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ)
    (X : ℕ → Ω → E) (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω))
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → E,
      (∀ n, K ≤ n → @Measurable Ω E
        (Section6.fieldSigmaAlgebraModConst α₀ hC (Metric.ball 0 ε)) _ (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n)) :
    Ergodic (Prod.map phaseTorusDouble (fun x : ℕ → E => fun n => x (n + 1)))
      (((volume : Measure PhaseCircle).prod volume).prod (P.map (fun ω n => X n ω))) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  exact ergodic_phaseTorusDouble_prod_of_stationary_ae_local_germ P
    (fun ε => Section6.fieldSigmaAlgebraModConst α₀ hC (Metric.ball 0 ε))
    dyadicScale dyadicScale_pos dyadicScale_germ_cofinal.2 dyadicScale_germ_cofinal.1
    (monotone_fieldSigmaAlgebraModConst_ball α₀ hC 0) X hXm hstat hlocal
    (h.origin_germ_trivial α₀)

end HarmonicBalls
