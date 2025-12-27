import Mathlib.Util.Notation3
import Mathlib.Tactic.Basic
import VerifiedAgora.tagger

/-- The pair of two random variables -/
@[target] lemma iIndepFun.prod {hf : ∀ (i : ι), Measurable (f i)} {ST : ι' → Finset ι}
    (hS : Pairwise (Disjoint on ST)) (h : iIndepFun n f μ) :
    let β := fun k ↦ Π i : ST k, α i
    iIndepFun (β := β) (fun _ ↦ MeasurableSpace.pi) (fun (k : ι') (x : Ω) (i : ST k) ↦ f i x) μ := by
  sorry


@[inherit_doc prod] notation3:100 "⟨" X ", " Y "⟩" => prod X Y

@[simp]
lemma prod_eq {Ω S T : Type*} {X : Ω → S} {Y : Ω → T} {ω : Ω} :
    (⟨ X, Y ⟩ : Ω → S × T) ω = (X ω, Y ω) := rfl
