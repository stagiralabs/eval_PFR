import Mathlib.Probability.UniformOn
import PFR.Mathlib.Data.Set.Card
import VerifiedAgora.tagger

open Function MeasureTheory Measure

namespace ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}

@[target] lemma uniformOn_apply_singleton_of_mem (hx : x ∈ s) (hs : s.Finite) :
    uniformOn s {x} = 1 / Nat.card s := by
  sorry


lemma real_uniformOn_apply_singleton_of_mem (hx : x ∈ s) (hs : s.Finite) :
    (uniformOn s).real {x} = 1 / Nat.card s := by
  simp [measureReal_def, uniformOn_apply_singleton_of_mem hx hs]

@[target] lemma uniformOn_apply_singleton_of_not_mem (hx : x ∉ s) : uniformOn s {x} = 0 := by
  sorry


lemma real_uniformOn_apply_singleton_of_not_mem (hx : x ∉ s) :
    (uniformOn s).real {x} = 0 := by
  simp [measureReal_def, uniformOn_apply_singleton_of_not_mem hx]

@[target] theorem uniformOn_apply_eq_zero (hst : s ∩ t = ∅) : uniformOn s t = 0 := by
  sorry


@[target] lemma uniformOn_of_infinite (hs : s.Infinite) : uniformOn s = 0 := by sorry


@[target] lemma uniformOn_apply (hs : s.Finite) (t : Set Ω) :
    uniformOn s t = (Nat.card ↑(s ∩ t)) / Nat.card s := by
  sorry


lemma uniformOn_real (hs : s.Finite) (t : Set Ω) :
    (uniformOn s).real t = (Nat.card ↑(s ∩ t)) / Nat.card s := by
  simp [measureReal_def, uniformOn_apply hs]

lemma uniformOn_real_singleton (hs : s.Finite) (ω : Ω) [Decidable (ω ∈ s)] :
    (uniformOn s).real {ω} = if ω ∈ s then (s.ncard : ℝ)⁻¹ else 0 := by
  simp [uniformOn_real hs, Set.ncard_inter_singleton]; split <;> simp

instance uniformOn.instIsProbabilityMeasure [Nonempty s] [Finite s] :
    IsProbabilityMeasure (uniformOn s) := uniformOn_isProbabilityMeasure ‹_› .of_subtype

lemma map_uniformOn_apply {f : Ω → Ω'} (hmes : Measurable f) (hf : Injective f) {t : Set Ω'}
    (ht : MeasurableSet t) :
    (uniformOn s).map f t = uniformOn (f '' s) t := by
  obtain hs | hs := s.infinite_or_finite
  · simp [uniformOn_of_infinite, hs, hs.image hf.injOn]
  · rw [map_apply hmes ht, uniformOn_apply hs, uniformOn_apply (hs.image _),
      Nat.card_image_of_injective hf, ← Nat.card_image_of_injective hf, Set.image_inter_preimage]

lemma map_uniformOn {f : Ω → Ω'} (hmes : Measurable f) (hf : Injective f) :
    (uniformOn s).map f = uniformOn (f '' s) := by
  ext t ht
  exact map_uniformOn_apply hmes hf ht

end ProbabilityTheory
