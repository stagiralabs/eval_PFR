import Mathlib.MeasureTheory.Measure.Real
import PFR.Mathlib.MeasureTheory.Measure.Prod
import VerifiedAgora.tagger

open Function Set
open scoped ENNReal NNReal

namespace MeasureTheory
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}

lemma Measure.ennreal_smul_real_apply (c : ℝ≥0∞) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c.toReal • μ.real s := by simp

lemma Measure.nnreal_smul_real_apply (c : ℝ≥0) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c • μ.real s := by simp [Measure.real, NNReal.smul_def]

lemma Measure.comap_real_apply {s : Set α} {f : α → β} (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    (comap f μ).real s = μ.real (f '' s) := by simp [Measure.real, comap_apply _ hfi hf μ hs]

lemma Measure.prod_real_singleton (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  simp [Measure.real, Measure.prod_apply_singleton]

variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ω']

@[target] lemma measureReal_preimage_fst_singleton_eq_sum {S T : Type*} {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] [Fintype T] {_ : MeasurableSpace T}
    [MeasurableSingletonClass T] (μ : Measure (S × T)) [IsFiniteMeasure μ] (x : S) :
    μ.real (Prod.fst ⁻¹' {x}) = ∑ y : T, μ.real {(x, y)} := by
  sorry


@[target] lemma measureReal_preimage_snd_singleton_eq_sum {S T : Type*} [Fintype S] {_ : MeasurableSpace S}
    [MeasurableSingletonClass S] {_ : MeasurableSpace T}
    [MeasurableSingletonClass T] (μ : Measure (S × T)) [IsFiniteMeasure μ] (y : T) :
    μ.real (Prod.snd ⁻¹' {y}) = ∑ x : S, μ.real {(x, y)} := by
  sorry


end MeasureTheory
