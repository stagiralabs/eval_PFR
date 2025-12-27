import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import PFR.Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import VerifiedAgora.tagger

namespace MeasureTheory
variable {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] {μ : Measure Ω}

@[target] lemma measure_eq_one_of_forall_singleton {X : Type*} [Countable X] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {s : Set X} (hμ : ∀ x ∈ sᶜ, μ {x} = 0) : μ s = 1 := by
  sorry


end MeasureTheory
