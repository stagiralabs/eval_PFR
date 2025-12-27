import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import VerifiedAgora.tagger

open Set

namespace MeasureTheory
variable {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] {μ : Measure Ω} {s : Set Ω}

@[target] lemma measure_eq_univ_of_forall_singleton {X : Type*} [Countable X] [MeasurableSpace X]
    {μ : Measure X} {s : Set X} (hμ : ∀ x ∈ sᶜ, μ {x} = 0) : μ s = μ Set.univ := by
  sorry


end MeasureTheory
