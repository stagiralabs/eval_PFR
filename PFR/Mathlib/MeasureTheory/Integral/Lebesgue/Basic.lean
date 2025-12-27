import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import VerifiedAgora.tagger

/-!
# TODO

Rename `setLIntegral_congr` to `setLIntegral_congr_set`
-/

open ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

@[target] lemma lintegral_eq_zero_of_ae_zero {f : α → ℝ≥0∞} (hs : μ sᶜ = 0) (hf : ∀ x ∈ s, f x = 0)
    (hmes : MeasurableSet s) : ∫⁻ x, f x ∂μ = 0 := by
  sorry


lemma lintegral_eq_setLIntegral (hs : μ sᶜ = 0) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  rw [← setLIntegral_univ, ← setLIntegral_congr]; rwa [ae_eq_univ]

end MeasureTheory
