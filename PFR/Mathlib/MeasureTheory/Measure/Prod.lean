import Mathlib.MeasureTheory.Measure.Prod
import VerifiedAgora.tagger

open Function
open scoped ENNReal NNReal

namespace MeasureTheory.Measure
variable {Ω α β γ : Type*} [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}

/-- The law of $(X, Z)$ is the image of the law of $(Z,X)$. -/
/-- The law of $(X, Z)$ is the image of the law of $(Z,X)$.-/
@[target] lemma map_prod_comap_swap (hX : Measurable X) (hZ : Measurable Z) (μ : Measure Ω) :
    (μ.map (fun ω ↦ (X ω, Z ω))).comap Prod.swap = μ.map (fun ω ↦ (Z ω, X ω)) := by
  sorry


@[target] lemma prod_apply_singleton {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν) {x} = μ {x.1} * ν {x.2} := by
  sorry


lemma prod_real_apply_singleton {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  simp [Measure.real, prod_apply_singleton]

lemma prod_of_full_measure_finset {μ : Measure α} {ν : Measure β} [SigmaFinite ν]
    {A : Finset α} {B : Finset β} (hA : μ Aᶜ = 0) (hB : ν Bᶜ = 0) :
    (μ.prod ν) (A ×ˢ B : Finset (α × β))ᶜ = 0 := by
  have : (↑(A ×ˢ B) : Set (α × β))ᶜ = ((A : Set α)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (B : Set β)ᶜ) := by
    ext ⟨s, t⟩; simp; tauto
  rw [this]
  simp [hA, hB]

end MeasureTheory.Measure

open MeasureTheory

set_option linter.flexible false in
instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [IsZeroOrProbabilityMeasure μ] {ν : Measure β} [IsZeroOrProbabilityMeasure ν] :
    IsZeroOrProbabilityMeasure (μ.prod ν) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp; infer_instance
  rcases eq_zero_or_isProbabilityMeasure ν with rfl | hν
  · simp; infer_instance
  infer_instance
