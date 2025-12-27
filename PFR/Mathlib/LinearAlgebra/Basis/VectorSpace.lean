import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import VerifiedAgora.tagger

namespace Submodule
variable {B F R : Type*} [DivisionRing R] [AddCommGroup B] [AddCommGroup F]
  [Module R B] [Module R F]

open LinearMap

/-- Given a submodule $E$ of $B \times F$, there is an equivalence $f : E \to B' \times F'$
given by the projections $E \to B$ and $E \to F$ "modulo" some $φ : B \to F$. -/
/-- Given a submodule $E$ of $B \times F$, there is an equivalence $f : E \to B' \times F'$
given by the projections $E \to B$ and $E \to F$ "modulo" some $φ : B \to F$. -/
@[target] theorem exists_equiv_fst_sndModFst (E : Submodule R (B × F)) :
    ∃ (B' : Submodule R B) (F' : Submodule R F) (f : E ≃ₗ[R] B' × F') (φ : B →ₗ[R] F),
    (∀ x, (f x).1.val = x.val.1 ∧ (f x).2.val = x.val.2 - φ x.val.1) ∧
    (∀ (x₁ : B') (x₂ : F'), (f.symm (x₁, x₂)).val = (x₁.val, x₂.val + φ x₁.val)) := by
  sorry


end Submodule
