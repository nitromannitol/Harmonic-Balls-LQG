import HarmonicBalls.Proofs.Sec8.PhaseErgodicFrequency

/-! # Ergodic factors for the phase-shifted scale process

The pointwise ergodic theorem used by the imported frequency result is from
Leonardo Bonanno's LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory

namespace HarmonicBalls

/-- The tail law of a measurable sequence is an ergodic factor of any ergodic
system that transports each observable to the next one. -/
theorem ergodic_tail_law_of_ergodic_transport
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (T : Ω → Ω) (hT : Ergodic T P)
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n))
    (htransport : ∀ n ω, X n (T ω) = X (n + 1) ω) :
    Ergodic (fun x : ℕ → E => fun n => x (n + 1))
      (P.map (fun ω n => X (n + 1) ω)) := by
  let path : Ω → ℕ → E := fun ω n => X (n + 1) ω
  let shift : (ℕ → E) → (ℕ → E) := fun x n => x (n + 1)
  have hp : Measurable path := Measurable.of_eval (fun n => hX (n + 1))
  have hs : Measurable shift := Measurable.of_eval (fun n => measurable_pi_apply (n + 1))
  have hcomm : Function.Semiconj path T shift := by
    intro ω
    funext n
    exact htransport (n + 1) ω
  exact (hp.measurePreserving P).ergodic_of_ergodic_semiconj hT hs hcomm

/-- Almost-sure semiconjugacy also sends ergodicity to the factor law. -/
theorem ergodic_map_of_ae_semiconj
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (T : Ω → Ω) (hT : Ergodic T P)
    (f : Ω → E) (hf : Measurable f) (S : E → E) (hS : Measurable S)
    (hcomm : ∀ᵐ ω ∂P, f (T ω) = S (f ω)) : Ergodic S (P.map f) := by
  have hcomm' : (f ∘ T) =ᵐ[P] (S ∘ f) := hcomm
  have hfactor : MeasurePreserving f P (P.map f) := hf.measurePreserving P
  have hmap : MeasurePreserving S (P.map f) (P.map f) := by
    refine ⟨hS, ?_⟩
    rw [Measure.map_map hS hf]
    calc
      P.map (S ∘ f) = P.map (f ∘ T) := Measure.map_congr hcomm'.symm
      _ = (P.map T).map f := (Measure.map_map hf hT.measurable).symm
      _ = P.map f := by rw [hT.map_eq]
  refine ⟨hmap, ?_⟩
  refine ⟨?_⟩
  intro s hs hinv
  rw [← hfactor.aeconst_preimage hs.nullMeasurableSet]
  apply hT.quasiErgodic.aeconst_set₀ (hf hs).nullMeasurableSet
  filter_upwards [hcomm] with ω hω
  apply propext
  change (f (T ω) ∈ s) ↔ (f ω ∈ s)
  rw [hω]
  exact Set.ext_iff.mp hinv (f ω)

/-- The scale-sequence tail is an ergodic factor under almost-sure transport. -/
theorem ergodic_tail_law_of_ae_ergodic_transport
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (T : Ω → Ω) (hT : Ergodic T P)
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n))
    (htransport : ∀ᵐ ω ∂P, ∀ n, X n (T ω) = X (n + 1) ω) :
    Ergodic (fun x : ℕ → E => fun n => x (n + 1))
      (P.map (fun ω n => X (n + 1) ω)) := by
  let path : Ω → ℕ → E := fun ω n => X (n + 1) ω
  let shift : (ℕ → E) → (ℕ → E) := fun x n => x (n + 1)
  have hp : Measurable path := Measurable.of_eval (fun n => hX (n + 1))
  have hs : Measurable shift := Measurable.of_eval (fun n => measurable_pi_apply (n + 1))
  apply ergodic_map_of_ae_semiconj P T hT path hp shift hs
  filter_upwards [htransport] with ω hω
  funext n
  exact hω (n + 1)

/-- Bounded observables transported by an ergodic system have their initial
mean as the almost-sure limiting average, even when transport holds only
outside a null set. -/
theorem ae_tendsto_initialScaleAverage_of_ae_ergodic_transport
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → Ω) (hT : Ergodic T P)
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n))
    (hbound : ∀ n ω, X n ω ∈ Set.Icc (0 : ℝ) 1)
    (htransport : ∀ᵐ ω ∂P, ∀ n, X n (T ω) = X (n + 1) ω) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, X n ω) / (N : ℝ)) Filter.atTop
      (nhds (∫ ω, X 0 ω ∂P)) := by
  let path : Ω → ℕ → ℝ := fun ω n => X n ω
  have hp : Measurable path := Measurable.of_eval hX
  have heq : (fun ω n => X (n + 1) ω) =ᵐ[P] (path ∘ T) := by
    filter_upwards [htransport] with ω hω
    funext n
    exact (hω n).symm
  have hstat : P.map (fun ω n => X (n + 1) ω) = P.map path := by
    calc
      _ = P.map (path ∘ T) := Measure.map_congr heq
      _ = (P.map T).map path := (Measure.map_map hp hT.measurable).symm
      _ = P.map path := by rw [hT.map_eq]
  exact ae_tendsto_initialScaleAverage_of_ergodic_law P X hX hbound hstat
    (ergodic_tail_law_of_ae_ergodic_transport P T hT X hX htransport)

open Classical in
/-- The shifted very-good scale sequence is an ergodic factor of the joint
phase and field rescaling map, provided that map is ergodic and realizes the
normalized pullback. -/
theorem phaseVeryGoodComparable_ergodic_tail_of_ergodic_rescaling
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [SFinite P] (Q : Measure T) [SFinite Q] (D : T → T) (R : Ω → Ω)
    (herg : Ergodic (Prod.map D R) (Q.prod P))
    (phase : T → ℂ) (hphase : Measurable phase)
    (hperiod : ∀ t, phase (D t) - (2 : ℝ) • phase t ∈
      Section6.scaledLattice ((1 : ℝ) / 100))
    (U : Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν}) (hU : Measurable U)
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α β : ℝ)
    (hUeq : ∀ᵐ ω ∂P, (U (R ω)).val =
      normalizedPullbackMeasure γ α (dyadicScale 1) (hcirc ω) (U ω).val)
    (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    Ergodic (fun x : ℕ → ℝ => fun n => x (n + 1))
      ((Q.prod P).map (fun p n => if
        PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale (n + 1)) 0 N
          a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
        AnnulusBallComparison (U p.2).val (n + 1) 0 m then (1 : ℝ) else 0)) := by
  let X : ℕ → T × Ω → ℝ := fun n p => if
    PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N
      a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
    AnnulusBallComparison (U p.2).val n 0 m then 1 else 0
  have hval : Measurable (fun p : T × Ω => (U p.2).val) :=
    measurable_subtype_coe.comp (hU.comp measurable_snd)
  have hfin : ∀ p : T × Ω, IsLocallyFiniteMeasure (U p.2).val := fun p => (U p.2).property
  have hm : ∀ n, Measurable (X n) := by
    intro n
    have hs := (measurableSet_phaseVeryGoodAnnulus
      (c := fun _ : T × Ω => (0 : ℂ)) hval hfin measurable_const
      (hphase.comp measurable_fst) β (dyadicScale n) (dyadicScale_pos n) N
      a b C₁m C₁p C₂m C₂p C₃ hunit).inter
      (measurableSet_annulusBallComparison_joint (c := fun _ : T × Ω => (0 : ℂ))
        hval hfin measurable_const n m)
    exact measurable_const.piecewise hs measurable_const
  apply ergodic_tail_law_of_ae_ergodic_transport (Q.prod P) (Prod.map D R) herg X hm
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hUeq] with p hp
  intro n
  dsimp only [X, Prod.map]
  simp only [hp, phaseVeryGoodComparable_normalizedPullback_dyadic_succ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hperiod p.1)]

end HarmonicBalls
