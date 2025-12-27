import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Constructions.SubmoduleQuotient
import PFR.Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import PFR.Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import PFR.ForMathlib.AffineSpaceDim
import PFR.ForMathlib.Entropy.RuzsaSetDist
import PFR.ImprovedPFR
import VerifiedAgora.tagger

/-!
# Weak PFR over the integers

Here we use the entropic form of PFR to deduce a weak form of PFR over the integers.

## Main statement

* `weak_PFR_int`: Let $A\subseteq \mathbb{Z}^d$ and $\lvert A+A\rvert\leq K\lvert A\rvert$.
  There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-17}\lvert A\rvert$ and
  $\dim A' \leq (40/\log 2)\log K$.

-/

open Set
open scoped Pointwise
section AddCommGroup
variable {G : Type*} [AddCommGroup G] {A B : Set G}

/-- A set `A` is a shift of a set `B` if it can be written as `x + B`. -/
/-- A set `A` is a shift of a set `B` if it can be written as `x + B`. -/
def IsShift (A B : Set G) : Prop := by sorry


lemma IsShift.sub_self_congr : IsShift A B → A - A = B - B := by
  rintro ⟨x, rfl⟩; simp [vadd_sub_vadd_comm]

lemma IsShift.card_congr : IsShift A B → Nat.card A = Nat.card B := by rintro ⟨x, rfl⟩; simp

/-- The property of two sets A, B of a group G not being contained in cosets of the same proper
subgroup -/
def NotInCoset (A B : Set G) : Prop := AddSubgroup.closure ((A - A) ∪ (B - B)) = ⊤

/-- Without loss of generality, one can move (up to translation and embedding) any pair A, B of
non-empty sets into a subgroup where they are not in a coset. -/
/-- Without loss of generality, one can move (up to translation and embedding) any pair A, B of
non-empty sets into a subgroup where they are not in a coset. -/
@[target] lemma wlog_notInCoset (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ (G' : AddSubgroup G) (A' B' : Set (G' : Set G)),
    IsShift A A' ∧ IsShift B B' ∧ NotInCoset A' B' := by
  sorry


end AddCommGroup

section Torsion

open Real ProbabilityTheory MeasureTheory

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [Countable G] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : Ω → G) (Y : Ω' → G)
  (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- If `G` is torsion-free and `X, Y` are `G`-valued random variables then `d[X; 2Y] ≤ 5d[X; Y]`. -/
/-- If `G` is torsion-free and `X, Y` are `G`-valued random variables then `d[X ; 2Y] ≤ 5d[X ; Y]`. -/
@[target] lemma torsion_free_doubling [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) (hG : AddMonoid.IsTorsionFree G) :
    d[X ; μ # (Y + Y) ; μ'] ≤ 5 * d[X ; μ # Y ; μ'] := by
  sorry


/-- If `G` is a torsion-free group and `X, Y` are `G`-valued random variables and
`φ : G → 𝔽₂^d` is a homomorphism then `H[φ ∘ X; μ] ≤ 10 * d[X; μ # Y; μ']`. -/
/-- If `G` is a torsion-free group and `X, Y` are `G`-valued random variables and
`φ : G → 𝔽₂^d` is a homomorphism then `H[φ ∘ X ; μ] ≤ 10 * d[X ; μ # Y ; μ']`. -/
@[target] lemma torsion_dist_shrinking {H : Type*} [FiniteRange X] [FiniteRange Y] (hX : Measurable X)
    (hY : Measurable Y) [AddCommGroup H] [Module (ZMod 2) H]
    [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H]
    (hG : AddMonoid.IsTorsionFree G) (φ : G →+ H) :
    H[φ ∘ X ; μ] ≤ 10 * d[X ; μ # Y ; μ'] :=
  calc
    H[φ ∘ X ; μ] = 2 * d[φ ∘ X ; μ # φ ∘ (Y + Y) ; μ'] := by
      sorry


end Torsion

section F2_projection

open Real ProbabilityTheory MeasureTheory

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] [MeasurableSpace G]
[MeasurableSingletonClass G] {Ω Ω' : Type*}

/-- Let $G=\mathbb{F}_2^n$ and `X, Y` be `G`-valued random variables such that
\[\mathbb{H}(X)+\mathbb{H}(Y)> (20/\alpha) d[X;Y],\]
for some $\alpha > 0$.
There is a non-trivial subgroup $H\leq G$ such that
\[\log \lvert H\rvert <(1+\alpha)/2 (\mathbb{H}(X)+\mathbb{H}(Y))\] and
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))< \alpha (\mathbb{H}(X)+\mathbb{H}(Y))\]
where $\psi:G\to G/H$ is the natural projection homomorphism.
-/
@[target] lemma app_ent_PFR (α : ℝ) (hent : 20 * d[X ;μ # Y;μ'] < α * (H[X ; μ] + H[Y; μ'])) (hX : Measurable X)
    (hY : Measurable Y) :
    ∃ H : Submodule (ZMod 2) G, log (Nat.card H) < (1 + α) / 2 * (H[X ; μ] + H[Y;μ']) ∧
    H[H.mkQ ∘ X ; μ] + H[H.mkQ ∘ Y; μ'] < α * (H[ X ; μ] + H[Y; μ']) := by sorry


variable [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : Ω → G) (Y : Ω' → G)
(μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac)
[IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

lemma app_ent_PFR (α : ℝ) (hent : 20 * d[X; μ # Y; μ'] < α * (H[X; μ] + H[Y; μ']))
    (hX : Measurable X) (hY : Measurable Y) :
    ∃ H : Submodule (ZMod 2) G, log (Nat.card H) < (1 + α) / 2 * (H[X; μ] + H[Y;μ']) ∧
    H[H.mkQ ∘ X; μ] + H[H.mkQ ∘ Y; μ'] < α * (H[X; μ] + H[Y; μ']) :=
  app_ent_PFR' (mΩ := .mk μ) (mΩ' := .mk μ') X Y hent hX hY

set_option linter.flexible false in
/-- If $G=\mathbb{F}_2^d$ and `X, Y` are `G`-valued random variables and $\alpha < 1$ then there is
a subgroup $H\leq \mathbb{F}_2^d$ such that
\[\log \lvert H\rvert \leq (1 + α) / (2 * (1 - α)) * (\mathbb{H}(X)+\mathbb{H}(Y))\]
and if $\psi:G \to G/H$ is the natural projection then
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))\leq 20/\alpha * d[\psi(X);\psi(Y)].\] -/
/-- If $G=\mathbb{F}_2^d$ and `X, Y` are `G`-valued random variables then there is
a subgroup $H\leq \mathbb{F}_2^d$ such that
\[\log \lvert H\rvert \leq 2 * (\mathbb{H}(X)+\mathbb{H}(Y))\]
and if $\psi:G \to G/H$ is the natural projection then
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))\leq 34 * d[\psi(X);\psi(Y)].\] -/
@[target] lemma PFR_projection (hX : Measurable X) (hY : Measurable Y) :
    ∃ H : Submodule (ZMod 2) G, log (Nat.card H) ≤ 2 * (H[X ; μ] + H[Y;μ']) ∧
    H[H.mkQ ∘ X ; μ] + H[H.mkQ ∘ Y; μ'] ≤
      34 * d[H.mkQ ∘ X ;μ # H.mkQ ∘ Y;μ'] := by
  sorry


/-- If $G=\mathbb{F}_2^d$ and `X, Y` are `G`-valued random variables then there is
a subgroup $H\leq \mathbb{F}_2^d$ such that
\[\log \lvert H\rvert \leq 2 * (\mathbb{H}(X)+\mathbb{H}(Y))\]
and if $\psi:G \to G/H$ is the natural projection then
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))\leq 34 * d[\psi(X);\psi(Y)].\] -/
lemma PFR_projection (hX : Measurable X) (hY : Measurable Y) :
    ∃ H : Submodule (ZMod 2) G, log (Nat.card H) ≤ 2 * (H[X; μ] + H[Y;μ']) ∧
    H[H.mkQ ∘ X; μ] + H[H.mkQ ∘ Y; μ'] ≤
      34 * d[H.mkQ ∘ X;μ # H.mkQ ∘ Y;μ'] := by
  rcases PFR_projection' X Y μ μ' ((3 : ℝ) / 5) hX hY (by norm_num) (by norm_num) with ⟨H, h, h'⟩
  refine ⟨H, ?_, ?_⟩
  · convert h
    norm_num
  · have : 0 ≤ d[⇑H.mkQ ∘ X; μ # ⇑H.mkQ ∘ Y; μ'] :=
      rdist_nonneg (.comp .of_discrete hX) (.comp .of_discrete hY)
    linarith

end F2_projection

open MeasureTheory ProbabilityTheory Real Set

@[target] lemma four_logs {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    log ((a*b)/(c*d)) = log a + log b - log c - log d := by
  sorry


@[target] lemma sum_prob_preimage {G H : Type*} {X : Finset H} {A : Set G} [Finite A] {φ : A → X}
    {A_ : H → Set G} (hA : A.Nonempty) (hφ : ∀ x : X, A_ x = Subtype.val '' (φ ⁻¹' {x})) :
    ∑ x ∈ X, (Nat.card (A_ x) : ℝ) / Nat.card A = 1 := by
  sorry

  classical
  have := Fintype.ofFinite A
  rewrite [Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
    <| fun a _ ↦ Finset.mem_univ (φ a), ← Finset.sum_coe_sort]
  norm_cast
  congr with x
  rewrite [← Set.Finite.toFinset_setOf, (Set.toFinite _).card_toFinset, ← Nat.card_eq_fintype_card,
    hφ, Nat.card_image_of_injective Subtype.val_injective]
  · rfl
  · exact toFinite {x_1 | φ x_1 = x}

/-- Let $\phi : G\to H$ be a homomorphism and $A,B\subseteq G$ be finite subsets.
If $x,y\in H$ then let $A_x=A\cap \phi^{-1}(x)$ and $B_y=B\cap \phi^{-1}(y)$.
There exist $x,y\in H$ such that $A_x,B_y$ are both non-empty and
\[d[\phi(U_A);\phi(U_B)]\log \frac{\lvert A\rvert\lvert B\rvert}{\lvert A_x\rvert\lvert B_y\rvert}
\leq (\mathbb{H}(\phi(U_A))+\mathbb{H}(\phi(U_B)))(d(U_A,U_B)-d(U_{A_x},U_{B_y}).\] -/
/-- Let $\phi : G\to H$ be a homomorphism and $A,B\subseteq G$ be finite subsets.
If $x,y\in H$ then let $A_x=A\cap \phi^{-1}(x)$ and $B_y=B\cap \phi^{-1}(y)$.
There exist $x,y\in H$ such that $A_x,B_y$ are both non-empty and
\[d[\phi(U_A);\phi(U_B)]\log \frac{\lvert A\rvert\lvert B\rvert}{\lvert A_x\rvert\lvert B_y\rvert}
\leq (\mathbb{H}(\phi(U_A))+\mathbb{H}(\phi(U_B)))(d(U_A,U_B)-d(U_{A_x},U_{B_y}).\] -/
@[target] lemma single_fibres {G H Ω Ω': Type*}
    [AddCommGroup G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
    [AddCommGroup H] [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')]
    (φ : G →+ H)
    {A B : Set G} [Finite A] [Finite B] {UA : Ω → G} {UB : Ω' → G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hUA': Measurable UA) (hUB': Measurable UB) (hUA : IsUniform A UA) (hUB : IsUniform B UB)
    (hUA_mem : ∀ ω, UA ω ∈ A) (hUB_mem : ∀ ω, UB ω ∈ B) :
    ∃ (x y : H) (Ax By : Set G),
    Ax = A ∩ φ.toFun ⁻¹' {x} ∧ By = B ∩ φ.toFun ⁻¹' {y} ∧ Ax.Nonempty ∧ By.Nonempty ∧
    d[φ.toFun ∘ UA # φ.toFun ∘ UB]
    * log (Nat.card A * Nat.card B / ((Nat.card Ax) * (Nat.card By))) ≤
    (H[φ.toFun ∘ UA] + H[φ.toFun ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := by
  sorry


variable {G : Type*} [AddCommGroup G] [Module.Free ℤ G]

open Real MeasureTheory ProbabilityTheory Pointwise Set Function
open QuotientAddGroup

variable [Module.Finite ℤ G]


/-- A version of the third isomorphism theorem: if G₂ ≤ G and H' is a subgroup of G⧸G₂, then there
is a canonical isomorphism between H⧸H' and G⧸N, where N is the preimage of H' in G. A bit clunky;
may be a better way to do this -/
lemma third_iso {G : Type*} [AddCommGroup G] {G₂ : AddSubgroup G} (H' : AddSubgroup (G ⧸ G₂)) :
    let H := G ⧸ G₂
    let φ : G →+ H := mk' G₂
    let N := AddSubgroup.comap φ H'
    ∃ e : H ⧸ H' ≃+ G ⧸ N, ∀ x : G, e (mk' H' (φ x)) = mk' N x := by
  set H := G ⧸ G₂
  let φ : G →+ H := mk' G₂
  let N := AddSubgroup.comap φ H'
  have h1 : G₂ ≤ N := by
    intro x hx
    rw [← eq_zero_iff] at hx
    have : φ x = 0 := hx
    simp [N, this, AddSubgroup.zero_mem H']
  set H'' := AddSubgroup.map (mk' G₂) N
  have h2 : H' = H'' := by
    change H' = AddSubgroup.map (mk' G₂) N
    rw [AddSubgroup.map_comap_eq, AddMonoidHom.range_eq_top_of_surjective _ (mk'_surjective G₂)]
    simp
  let e1 : H ⧸ H'' ≃+ G ⧸ N := quotientQuotientEquivQuotient _ _ h1
  let e2 := quotientAddEquivOfEq h2
  set e := e2.trans e1
  use e
  intro x
  convert (quotientQuotientEquivQuotientAux_mk_mk _ _ h1 x) using 1

@[target] lemma single {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} {z : Ω} (hA : μ.real A = 1) (hz : 0 < μ.real {z}) :
    z ∈ A := by
  sorry


variable [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

/-- Given two non-empty finite subsets A, B of a rank n free Z-module G, there exists a subgroup N
and points x, y in G/N such that the fibers Ax, By of A, B over x, y respectively are non-empty,
one has the inequality $$\log\frac{|A| |B|}{|A_x| |B_y|} ≤ 34 (d[U_A; U_B] - d[U_{A_x}; U_{B_y}])$$
and one has the dimension bound $$n \log 2 ≤ \log |G/N| + 40 d[U_A; U_B]$$. -/
/-- Given two non-empty finite subsets A, B of a rank n free Z-module G, there exists a subgroup N
and points x, y in G/N such that the fibers Ax, By of A, B over x, y respectively are non-empty,
one has the inequality $$\log\frac{|A| |B|}{|A_x| |B_y|} ≤ 34 (d[U_A; U_B] - d[U_{A_x}; U_{B_y}])$$
and one has the dimension bound $$n \log 2 ≤ \log |G/N| + 40 d[U_A; U_B]$$.
 -/
@[target] lemma weak_PFR_asymm_prelim (A B : Set G) [A_fin : Finite A] [B_fin : Finite B]
    (hnA : A.Nonempty) (hnB : B.Nonempty):
    ∃ (N : AddSubgroup G) (x y : G ⧸ N) (Ax By : Set G), Ax.Nonempty ∧ By.Nonempty ∧
    Set.Finite Ax ∧ Set.Finite By ∧ Ax = {z : G | z ∈ A ∧ QuotientAddGroup.mk' N z = x } ∧
    By = {z : G | z ∈ B ∧ QuotientAddGroup.mk' N z = y } ∧
    (log 2) * Module.finrank ℤ G ≤ log (Nat.card (G ⧸ N)) +
      40 * dᵤ[ A # B ] ∧ log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By)
      ≤ 34 * (dᵤ[ A # B ] - dᵤ[ Ax # By ]) := by
  sorry

    classical
    rwa [← ModN.natCard_eq, ← Nat.card_congr e.toEquiv, H'.card_eq_card_quotient_mul_card,
      Nat.cast_mul, log_mul, add_comm, add_le_add_iff_left]
    all_goals norm_cast; rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
  use N, x, y, Ax, By
  refine ⟨hnAx, hnBy, Ax.toFinite, By.toFinite, hAx, hBy, h_card, ?_⟩
  replace hH2 : H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB] ≤ 34 * d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] := by
    set X := (H'.mkQ.toFun ∘ φ.toFun) ∘ UA
    set Y := (H'.mkQ.toFun ∘ φ.toFun) ∘ UB
    have hX : Measurable X := Measurable.comp .of_discrete hUA_mes
    have hY : Measurable Y := Measurable.comp .of_discrete hUB_mes
    change H[X] + H[Y] ≤ 34 * d[X # Y] at hH2
    have ha : φ'.toFun ∘ UA = e.toFun ∘ X := by ext x; exact (he (UA x)).symm
    have hb : φ'.toFun ∘ UB = e.toFun ∘ Y := by ext x; exact (he (UB x)).symm
    have he_inj : Injective e.toFun := e.injective
    rw [ha, hb, entropy_comp_of_injective _ hX _ he_inj, entropy_comp_of_injective _ hY _ he_inj]
    have : d[e.toFun ∘ X # e.toFun ∘ Y] = d[X # Y] := rdist_of_inj hX hY e.toAddMonoidHom he_inj
    rwa [this]
  set X : Ω → G ⧸ N := φ'.toFun ∘ UA
  set Y : Ω' → G ⧸ N := φ'.toFun ∘ UB
  have hX : Measurable X := Measurable.comp .of_discrete hUA_mes
  have hY : Measurable Y := Measurable.comp .of_discrete hUB_mes
  rcases le_iff_lt_or_eq.mp (rdist_nonneg (μ := ℙ) (μ' := ℙ) hX hY) with h | h
  swap
  · rw [← h] at hH2
    have hH2A : H[X] ≥ 0 := entropy_nonneg _ _
    have hH2B : H[Y] ≥ 0 := entropy_nonneg _ _
    have hH2A' : H[X] ≤ 0 := by linarith only [hH2, hH2A, hH2B]
    have hH2B' : H[Y] ≤ 0 := by linarith only [hH2, hH2A, hH2B]
    rcases const_of_nonpos_entropy (μ := ℙ) hX hH2A' with ⟨x', hx⟩
    rcases const_of_nonpos_entropy (μ := ℙ) hY hH2B' with ⟨y', hy⟩
    have hAAx {z : G} (hz : z ∈ A) : φ'.toFun z = x' := by
      change (ℙ).real (UA⁻¹' (φ'⁻¹' {x'})) = 1 at hx
      rw [← MeasureTheory.map_measureReal_apply hUA_mes .of_discrete] at hx
      set Af := A.toFinite.toFinset
      have hUAf : IsUniform Af UA := by
        convert hUA_unif; simp only [Af, Set.Finite.coe_toFinset]
      have hnAf : 0 < Nat.card Af := by simp only [Af, Set.Finite.mem_toFinset, Nat.card_pos]
      have hzf : z ∈ Af := by simp [Af, Set.Finite.mem_toFinset, hz]
      have : (Measure.map UA ℙ).real {z} > 0 := by
        rw [IsUniform.measureReal_preimage_of_mem' hUAf hUA_mes hzf]
        simp only [one_div, gt_iff_lt, inv_pos, Nat.cast_pos, Finset.card_pos]
        exact (Finite.toFinset_nonempty (toFinite A)).mpr hnA
      have _ : IsProbabilityMeasure ((ℙ).map UA) :=
        Measure.isProbabilityMeasure_map (Measurable.aemeasurable hUA_mes)
      replace this := single ((ℙ).map UA) hx this
      rwa [Set.mem_preimage, Set.mem_singleton_iff] at this
    have hxx : Ax = A := by
      have h : hnAx.some ∈ Ax := hnAx.some_mem
      simp only [hAx, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_inter_iff, mem_preimage,
        mem_singleton_iff, inter_eq_left] at h ⊢
      have := hAAx h.1
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, h.2] at this
      intro z hz
      simp only [this, mem_preimage, mem_singleton_iff]
      convert hAAx hz
    have hBBy {z : G} (hz : z ∈ B) : φ'.toFun z = y' := by
      change (ℙ).real (UB⁻¹' (φ'⁻¹' {y'})) = 1 at hy
      rw [← MeasureTheory.map_measureReal_apply hUB_mes .of_discrete] at hy
      set Bf := B.toFinite.toFinset
      have hUBf : IsUniform Bf UB := by convert hUB_unif; simp only [Bf, Set.Finite.coe_toFinset]
      have hnBf : 0 < Nat.card Bf := by simp only [Bf, Set.Finite.mem_toFinset, Nat.card_pos]
      have hzf : z ∈ Bf := by simp [Bf, Set.Finite.mem_toFinset, hz]
      have : (Measure.map UB ℙ).real {z} > 0 := by
        rw [IsUniform.measureReal_preimage_of_mem' hUBf hUB_mes hzf]
        simp only [one_div, gt_iff_lt, inv_pos, Nat.cast_pos, Finset.card_pos]
        exact (Finite.toFinset_nonempty (toFinite B)).mpr hnB
      have _ : IsProbabilityMeasure ((ℙ).map UB) :=
        Measure.isProbabilityMeasure_map (Measurable.aemeasurable hUB_mes)
      replace this := single ((ℙ).map UB) hy this
      rwa [Set.mem_preimage, Set.mem_singleton_iff] at this
    have hyy : By = B := by
      have h : hnBy.some ∈ By := hnBy.some_mem
      simp only [hBy, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_inter_iff, mem_preimage,
        mem_singleton_iff, inter_eq_left] at h ⊢
      have := hBBy h.1
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, h.2] at this
      intro z hz
      simp only [this, mem_preimage, mem_singleton_iff]
      convert hBBy hz
    simp [hxx, hyy]
  have := calc d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] *
    (log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By))
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] *
        log (Nat.card A * Nat.card B / ((Nat.card Ax) * (Nat.card By))) := by
      congr
      convert (four_logs ?_ ?_ ?_ ?_).symm
      all_goals norm_cast; exact Nat.card_pos
    _ ≤ (H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := hcard_ineq
    _ ≤ (34 * d[φ'.toFun ∘ UA # φ'.toFun ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := by
      apply mul_le_mul_of_nonneg_right hH2
      have := rdist_le_avg_ent (Measurable.comp (.of_discrete (f := φ'.toFun)) hUA_mes)
        (Measurable.comp (.of_discrete (f := φ'.toFun)) hUB_mes)
      replace this : 0 < H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB] := by linarith
      rw [← mul_le_mul_iff_right₀ this]
      apply le_trans _ hcard_ineq
      rw [mul_zero]
      change 0 ≤ d[φ'.toFun ∘ UA # φ'.toFun ∘ UB]
        * log (Nat.card A * Nat.card B / ((Nat.card Ax) * (Nat.card By)))
      rw [← mul_zero d[φ'.toFun ∘ UA # φ'.toFun ∘ UB], mul_le_mul_iff_right₀ h]
      apply Real.log_nonneg
      rw [one_le_div (mod_cast mul_pos Nat.card_pos Nat.card_pos)]
      gcongr
      · apply Nat.card_mono (Set.toFinite A) (hAx ▸ Set.inter_subset_left)
      · apply Nat.card_mono (Set.toFinite B) (hBy ▸ Set.inter_subset_left)
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * (34 * (d[UA # UB] - dᵤ[Ax # By])) := by ring
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * (34 * (dᵤ[A # B] - dᵤ[Ax # By])) := by
      rw [←  setRuzsaDist_eq_rdist hUA_unif hUB_unif hUA_mes hUB_mes]
  exact (mul_le_mul_iff_right₀ h).mp this

/-- Separating out the conclusion of `weak_PFR_asymm` for convenience of induction arguments. -/
/-- Separating out the conclusion of `weak_PFR_asymm` for convenience of induction arguments.-/
def WeakPFRAsymmConclusion (A B : Set G) : Prop := by sorry


/-- The property of two sets A,B of a group G not being contained in cosets of the same proper
subgroup. -/
def not_in_coset {G : Type*} [AddCommGroup G] (A B : Set G) : Prop :=
  AddSubgroup.closure ((A - A) ∪ (B - B)) = ⊤

/-- In fact one has equality here, but this is trickier to prove and not needed for the argument. -/
/-- In fact one has equality here, but this is trickier to prove and not needed for the argument. -/
@[target] lemma dimension_of_shift {G : Type*} [AddCommGroup G] {H : AddSubgroup G}
    (A : Set H) (x : G) :
    AffineSpace.finrank ℤ ((fun a : H ↦ (a : G) + x) '' A) = AffineSpace.finrank ℤ A := by
  sorry

  classical
  calc
    _ = AffineSpace.finrank ℤ (x +ᵥ Subtype.val '' A) := by
      simp [← image_vadd, image_image, add_comm]
    _ = AffineSpace.finrank ℤ (Subtype.val '' A) := by rw [AffineSpace.finrank_vadd_set]
    _ = ((vectorSpan ℤ A).map H.subtype.toIntLinearMap).finrank := by
      simp only [AffineSpace.finrank, vectorSpan, Submodule.map_span,
        AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply]
      congr! 2
      symm
      exact image_image2_distrib fun _ _ ↦ rfl
    _ = AffineSpace.finrank ℤ A :=
      (Submodule.equivMapOfInjective _ Subtype.val_injective _).symm.finrank_eq

omit [Module.Finite ℤ G] [Module.Free ℤ G] in
omit [Module.Finite ℤ G] [Module.Free ℤ G] in
@[target] lemma conclusion_transfers {A B : Set G}
    (G': AddSubgroup G) (A' B' : Set (G' : Set G))
    (hA : IsShift A A') (hB : IsShift B B') [Finite A'] [Finite B']
    (hA' : A'.Nonempty) (hB' : B'.Nonempty)
    (h : WeakPFRAsymmConclusion A' B') : WeakPFRAsymmConclusion A B := by
  sorry


/-- If $A,B\subseteq \mathbb{Z}^d$ are finite non-empty sets then there exist non-empty
$A'\subseteq A$ and $B'\subseteq B$ such that
\[\log\frac{\lvert A\rvert\lvert B\rvert}{\lvert A'\rvert\lvert B'\rvert}\leq 34 d[U_A;U_B]\]
such that $\max(\dim A',\dim B')\leq \frac{40}{\log 2} d[U_A;U_B]$. -/
lemma weak_PFR_asymm (A B : Set G) [Finite A] [Finite B] (hA : A.Nonempty) (hB : B.Nonempty) :
    WeakPFRAsymmConclusion A B := by
  let P (M : ℕ) : Prop := ∀ (G : Type _) (hG_comm : AddCommGroup G) (_hG_free : Module.Free ℤ G)
    (_hG_fin : Module.Finite ℤ G) (_hG_count : Countable G) (hG_mes : MeasurableSpace G)
    (_hG_sing : MeasurableSingletonClass G) (A B : Set G) (_hA_fin : Finite A) (_hB_fin : Finite B)
    (_hA_non : A.Nonempty) (_hB_non : B.Nonempty)
    (_hM : Nat.card A + Nat.card B ≤ M), WeakPFRAsymmConclusion A B
  suffices ∀ M, (∀ M', M' < M → P M') → P M by
    set M := Nat.card A + Nat.card B
    have hM : Nat.card A + Nat.card B ≤ M := Nat.le_refl _
    convert (Nat.strong_induction_on (p := P) M this) G ‹_› ‹_› ‹_› ‹_› _ ‹_› A B ‹_› ‹_› ‹_› ‹_› hM
  intro M h_induct
  -- wlog we can assume A, B are not in cosets of a smaller subgroup
  suffices ∀ (G : Type _) (hG_comm : AddCommGroup G) (_hG_free : Module.Free ℤ G)
    (_hG_fin : Module.Finite ℤ G) (_hG_count : Countable G) (hG_mes : MeasurableSpace G)
    (_hG_sing : MeasurableSingletonClass G) (A B : Set G) (_hA_fin : Finite A) (_hB_fin : Finite B)
      (_hA_non : A.Nonempty) (_hB_non : B.Nonempty) (_hM : Nat.card A + Nat.card B ≤ M)
    (_hnot : NotInCoset A B), WeakPFRAsymmConclusion A B by
    intro G hG_comm hG_free hG_fin hG_count hG_mes hG_sing A B hA_fin hB_fin hA_non hB_non hM
    obtain ⟨G', A', B', hAA', hBB', hnot'⟩ := wlog_notInCoset hA_non hB_non
    have hG'_fin : Module.Finite ℤ G' :=
      Module.Finite.iff_fg (N := AddSubgroup.toIntSubmodule G').2 (IsNoetherian.noetherian _)
    have hG'_free : Module.Free ℤ G' := by
      rcases Submodule.nonempty_basis_of_pid (Module.Free.chooseBasis ℤ G)
        (AddSubgroup.toIntSubmodule G') with ⟨n, ⟨b⟩⟩
      exact Module.Free.of_basis b
    have hAA'_card : Nat.card A = Nat.card A' :=
      Nat.card_image_of_injective Subtype.val_injective _ ▸ hAA'.card_congr
    have hBB'_card : Nat.card B = Nat.card B' :=
      Nat.card_image_of_injective Subtype.val_injective _ ▸ hBB'.card_congr
    have hA_non' : Nonempty A := Set.nonempty_coe_sort.mpr hA_non
    have hB_non' : Nonempty B := Set.nonempty_coe_sort.mpr hB_non
    rw [hAA'_card, hBB'_card] at hM
    have hA'_nonfin : A'.Nonempty ∧ Finite A' := by
      convert Nat.card_pos_iff.mp ?_
      · exact Iff.symm nonempty_coe_sort
      · simpa [hAA'_card] using Nat.card_pos (α := A)
    have hB'_nonfin : B'.Nonempty ∧ Finite B' := by
      convert Nat.card_pos_iff.mp ?_
      · exact Iff.symm nonempty_coe_sort
      · simpa [hBB'_card] using Nat.card_pos (α := B)
    obtain ⟨hA'_non, hA'_fin⟩ := hA'_nonfin
    obtain ⟨hB'_non, hB'_fin⟩ := hB'_nonfin
    replace this := this G' _ hG'_free hG'_fin (by infer_instance) (by infer_instance)
      (by infer_instance) A' B' hA'_fin hB'_fin hA'_non hB'_non hM hnot'
    exact conclusion_transfers G' A' B' hAA' hBB' hA'_non hB'_non this
  intro G hG_comm hG_free hG_fin hG_count hG_mes hG_sing A B hA_fin hB_fin hA_non hB_non hM hnot
  obtain ⟨N, x, y, Ax, By, hAx_non, hBy_non, hAx_fin, hBy_fin, hAx, hBy, hdim, hcard⟩ :=
    weak_PFR_asymm_prelim A B hA_non hB_non
  have hAxA : Ax ⊆ A := by rw [hAx]; simp
  have hByB : By ⊆ B := by rw [hBy]; simp
  have hA_pos : (0 : ℝ) < Nat.card A := Nat.cast_pos.mpr (@Nat.card_pos _ hA_non.to_subtype _)
  have hB_pos : (0 : ℝ) < Nat.card B := Nat.cast_pos.mpr (@Nat.card_pos _ hB_non.to_subtype _)
  rcases lt_or_ge (Nat.card Ax + Nat.card By) (Nat.card A + Nat.card B) with h | h
  · replace h := h_induct (Nat.card Ax + Nat.card By) (h.trans_le hM) G hG_comm hG_free hG_fin
      hG_count hG_mes hG_sing Ax By (Set.finite_coe_iff.mpr hAx_fin) hBy_fin hAx_non hBy_non le_rfl
    rcases h with ⟨A', B', hA', hB', hA'_non, hB'_non, hcard_ineq, hdim_ineq⟩
    use A', B'
    have hAx_fin' := Set.finite_coe_iff.mpr hAx_fin
    have hBy_fin' := Set.finite_coe_iff.mpr hBy_fin
    have hA'_fin' := Set.finite_coe_iff.mpr (Set.Finite.subset hAx_fin hA')
    have hB'_fin' := Set.finite_coe_iff.mpr (Set.Finite.subset hBy_fin hB')
    have hAx_non' := Set.nonempty_coe_sort.mpr hAx_non
    have hBy_non' := Set.nonempty_coe_sort.mpr hBy_non
    have hA'_non' := Set.nonempty_coe_sort.mpr hA'_non
    have hB'_non' := Set.nonempty_coe_sort.mpr hB'_non
    have hAx_pos : (0 : ℝ) < Nat.card Ax := Nat.cast_pos.mpr Nat.card_pos
    have hBy_pos : (0 : ℝ) < Nat.card By := Nat.cast_pos.mpr Nat.card_pos
    have hA'_pos : (0 : ℝ) < Nat.card A' := Nat.cast_pos.mpr Nat.card_pos
    have hB'_pos : (0 : ℝ) < Nat.card B' := Nat.cast_pos.mpr Nat.card_pos
    have hAxA_le : (Nat.card Ax : ℝ) ≤ Nat.card A := by gcongr; exact Nat.card_mono A.toFinite hAxA
    have hByB_le : (Nat.card By : ℝ) ≤ Nat.card B := by gcongr; exact Nat.card_mono B.toFinite hByB
    refine ⟨hA'.trans hAxA, hB'.trans hByB, hA'_non, hB'_non, ?_, ?_⟩
    · rw [four_logs hA_pos hB_pos hA'_pos hB'_pos]
      rw [four_logs hAx_pos hBy_pos hA'_pos hB'_pos] at hcard_ineq
      linarith only [hcard, hcard_ineq]
    apply hdim_ineq.trans
    gcongr
    linarith only [Real.log_le_log hAx_pos hAxA_le, Real.log_le_log hBy_pos hByB_le, hcard]
  use A, B
  refine ⟨Eq.subset rfl, Eq.subset rfl, hA_non, hB_non, ?_, ?_⟩
  · have := hA_non.to_subtype
    have := hB_non.to_subtype
    apply LE.le.trans _ <| mul_nonneg (by norm_num) <| setRuzsaDist_nonneg A B
    rw [div_self (by positivity)]
    simp
  have hAx_eq : Ax = A := by
    apply Set.Finite.eq_of_subset_of_card_le A.toFinite hAxA
    linarith only [h, Nat.card_mono B.toFinite hByB]
  have hBy_eq : By = B := by
    apply Set.Finite.eq_of_subset_of_card_le B.toFinite hByB
    linarith only [h, Nat.card_mono A.toFinite hAxA]
  have hN : N = ⊤ := by
    have : (A-A) ∪ (B-B) ⊆ N := by
      rw [← hAx_eq, ← hBy_eq, hAx, hBy]
      intro z hz
      simp only [mk'_apply, mem_union, mem_sub, mem_setOf_eq] at hz
      convert (QuotientAddGroup.eq_zero_iff z).mp ?_
      · infer_instance
      rcases hz with ⟨a, ⟨-, ha⟩, a', ⟨-, ha'⟩, haa'⟩ | ⟨b, ⟨-, hb⟩, b', ⟨-,hb'⟩, hbb'⟩
      · rw [← haa']; simp [ha, ha']
      rw [← hbb']; simp [hb, hb']
    rw [← AddSubgroup.closure_le, hnot] at this
    exact top_le_iff.mp this
  have : Nat.card (G ⧸ N) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · rw [hN]
      exact QuotientAddGroup.subsingleton_quotient_top
    infer_instance
  simp only [this, Nat.cast_one, log_one, zero_add] at hdim
  rw [← le_div_iff₀' (by positivity)] at hdim
  convert le_trans ?_ hdim using 1
  · field_simp
  simp only [Nat.cast_max, max_le_iff, Nat.cast_le]
  exact ⟨AffineSpace.finrank_le_moduleFinrank, AffineSpace.finrank_le_moduleFinrank⟩

/-- If $A\subseteq \mathbb{Z}^d$ is a finite non-empty set with $d[U_A;U_A]\leq \log K$ then
there exists a non-empty $A'\subseteq A$ such that $\lvert A'\rvert\geq K^{-17}\lvert A\rvert$
and $\dim A'\leq \frac{40}{\log 2} \log K$. -/
/-- If $A\subseteq \mathbb{Z}^d$ is a finite non-empty set with $d[U_A;U_A]\leq \log K$ then
there exists a non-empty $A'\subseteq A$ such that $\lvert A'\rvert\geq K^{-17}\lvert A\rvert$
and $\dim A'\leq \frac{40}{\log 2} \log K$. -/
@[target] lemma weak_PFR {A : Set G} [Finite A] {K : ℝ} (hA : A.Nonempty) (hK : 0 < K)
    (hdist : dᵤ[A # A] ≤ log K) :
    ∃ A' : Set G, A' ⊆ A ∧ K^(-17 : ℝ) * Nat.card A ≤ Nat.card A' ∧
      AffineSpace.finrank ℤ A' ≤ (40 / log 2) * log K := by
  sorry


/-- Let $A\subseteq \mathbb{Z}^d$ and $\lvert A-A\rvert\leq K\lvert A\rvert$.
There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-17}\lvert A\rvert$
and $\dim A' \leq \frac{40}{\log 2} \log K$. -/
/-- Let $A\subseteq \mathbb{Z}^d$ and $\lvert A-A\rvert\leq K\lvert A\rvert$.
There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-17}\lvert A\rvert$
and $\dim A' \leq \frac{40}{\log 2} \log K$.-/
@[target] theorem weak_PFR_int
    {G : Type*} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G]
    {A : Set G} [A_fin : Finite A] (hnA : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A-A) ≤ K * Nat.card A) :
    ∃ A' : Set G, A' ⊆ A ∧ Nat.card A' ≥ K ^ (-17 : ℝ) * Nat.card A ∧
      AffineSpace.finrank ℤ A' ≤ (40 / log 2) * log K := by
  sorry
