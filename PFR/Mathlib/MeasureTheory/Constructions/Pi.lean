import Mathlib.MeasureTheory.Constructions.Pi
import VerifiedAgora.tagger

open Function Set

namespace MeasureTheory.Measure
variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

instance : IsProbabilityMeasure (.pi μ) :=
  ⟨by simp_rw [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

@[target] lemma pi_pi_set (t : Set ι) [DecidablePred (· ∈ t)] (s : ∀ i, Set (α i)) :
    Measure.pi μ (pi t s) = ∏ i ∈ Finset.univ.filter (· ∈ t), μ i (s i) := by
  sorry

  classical
  simp (config := {singlePass := true}) only [← pi_univ_ite]
  simp_rw [pi_pi, apply_ite, measure_univ,
    Finset.prod_ite, Finset.prod_const_one, mul_one]

@[target] lemma pi_pi_finset (t : Finset ι) (s : ∀ i, Set (α i)) :
    Measure.pi μ (pi t s) = ∏ i ∈ t, μ i (s i) := by
  sorry

  classical
  rw [pi_pi_set]
  congr; ext x; simp

@[target] lemma pi_eval_preimage (i : ι) (s : Set (α i)) :
    Measure.pi μ (eval i ⁻¹' s) = μ i s := by
  sorry

  classical
  simp_rw [eval_preimage, pi_pi, apply_update (fun i ↦ μ i), measure_univ,
    Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_const_one, mul_one]

@[target] lemma map_eval_pi (i : ι) : Measure.map (eval i) (Measure.pi μ) = μ i := by
  sorry


end MeasureTheory.Measure
