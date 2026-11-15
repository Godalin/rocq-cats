From Cats Require Export
  Cat.Profunctor.Strength
  Cat.Profunctor.Parameter.
From Cats Require Import
  Cat.Profunctor.Iterated
  Instance.Set.Core
  Instance.Set.Product.

Local Open Scope binoidal_scope.
Local Open Scope monoidal_scope.
Local Open Scope prof_scope.

(** * Strength of a Specified Profunctor Composite

    Apply each input strength to a generating pair and reinsert at the
    context-extended intermediate object. Balance and the original coend
    mediator give descent. Only the supplied composition family is chosen;
    no tensor preservation, global coend choice or size order is assumed. *)

(** * 指定 Profunctor 复合的强度

    对生成对的两个输入分别施加强度，并在扩展上下文后的中间对象处重新注入。
    平衡律及原 coend 中介给出下降。只选择给定复合族，不假定张量保持性、
    全局 coend 选择或大小次序。 *)

(** ** Balanced Context Extension

    Fix a monoidal category and two profunctors with chosen strengths.
    Select only the coends used below. The same value carrier/equality bounds remain
    independent. Extend the middle index with the original context functor. *)

(** ** 平衡的上下文扩展

    固定幺半范畴及两个带选定强度的 profunctor，只选择以下实际使用的 coend。
    原值载体与相等大小界保持独立，用原上下文函子扩展中间指标。 *)

Section CompositionStrength.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C).
Context (Q P : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})).
Context (SQ : HasProfStrength MC Q) (SP : HasProfStrength MC P).

(** ** Two Fixed Boundary Coends

    Context extension needs only the target coend for balanced legs, then
    the source coend for descent. A full boundary family is used only later
    to package naturality and the complete strength. *)

(** ** 两个固定边界 coend

    平衡腿只需上下文扩展后的目标 coend；下降再需要来源 coend。
    完整边界族只在随后打包自然性及完整强度时使用。 *)

Section FixedBoundaries.
Context (Z X Y : @Ob C).
Context `{HT : !HasCoend SetCat (ProfCompKernel Q P (Z ⊗ X) (Z ⊗ Y))}.

(** A generating pair receives the same context in both factors. *)

(** 生成对的两个因子接受同一上下文。 *)

Program Definition ProfCompStrengthLeg (B : @Ob C)
  : (P (X,B) ×S Q (B,Y)) →r coend[ProfCompKernel Q P (Z ⊗ X) (Z ⊗ Y)]
  :=
  {|func xy := ιPr[Q; P; Z ⊗ B]
      (pstrength[SP; Z] (fst xy),pstrength[SQ; Z] (snd xy))
  |}.
Next Obligation.
  intros [x y] [x' y'] [Hx Hy]. apply func_proper. split;
    apply func_proper; assumption.
Defined.

(** Naturality of the two strengths moves the middle arrow to its
    context extension; original coend gluing then balances the legs. *)

(** 两个强度的自然性将中间箭头改为其上下文扩展；原 coend 粘合使各腿平衡。 *)

Lemma prof_comp_strength_gluing
    {B B' : @Ob C} (h : Hom B B') (x : P (X,B)) (y : Q (B',Y))
  : ProfCompStrengthLeg B (x,lmap[Q; h] y) ≈S
      ProfCompStrengthLeg B' (rmap[P; h] x,y).
Proof.
  change (ιPr[Q; P; Z ⊗ B]
    (pstrength[SP; Z] x,pstrength[SQ; Z] (lmap[Q; h] y)) ≈S
    ιPr[Q; P; Z ⊗ B']
      (pstrength[SP; Z] (rmap[P; h] x),pstrength[SQ; Z] y)).
  transitivity (ιPr[Q; P; Z ⊗ B]
    (pstrength[SP; Z] x,lmap[Q; Z ⊲ h] (pstrength[SQ; Z] y))).
  - apply func_proper. split; [reflexivity |].
    exact (prof_strength_lmap SQ Z h y).
  - transitivity (ιPr[Q; P; Z ⊗ B']
      (rmap[P; Z ⊲ h] (pstrength[SP; Z] x),pstrength[SQ; Z] y)).
    + apply prof_comp_gluing.
    + apply func_proper. split; [| reflexivity].
      symmetry. exact (prof_strength_rmap SP Z h x).
Defined.

(** Use the existing balanced-legs constructor, retaining the same legs. *)

(** 使用已有平衡腿构造子，保留同一组腿。 *)

Definition ProfCompStrengthCowedge
  : Cowedge (ProfCompKernel Q P X Y)
      coend[ProfCompKernel Q P (Z ⊗ X) (Z ⊗ Y)]
  := ProfCompCowedge Q P ProfCompStrengthLeg
      (λ B B' h x y, prof_comp_strength_gluing h x y).

Context `{HS : !HasCoend SetCat (ProfCompKernel Q P X Y)}.

(** The transparent original mediator extends context to the composite. *)

(** 透明的原中介为复合扩展上下文。 *)

Definition prof_comp_strength
  : coend[ProfCompKernel Q P X Y] →r
      coend[ProfCompKernel Q P (Z ⊗ X) (Z ⊗ Y)]
  := prof_comp_desc Q P ProfCompStrengthCowedge.

(** On every generator descent is simultaneous strength and reinsertion. *)

(** 在每个生成元上，下降就是同时施加强度并重新注入。 *)

Lemma prof_comp_strength_inject (B : @Ob C)
    (x : P (X,B)) (y : Q (B,Y))
  : prof_comp_strength (ιPr[Q; P; B] (x,y)) ≈S
      ιPr[Q; P; Z ⊗ B] (pstrength[SP; Z] x,pstrength[SQ; Z] y).
Proof.
  exact (prof_comp_desc_β Q P ProfCompStrengthCowedge B (x,y)).
Defined.

(** The generating equation characterizes the complete descended map,
    using the original coend extensionality rather than representative
    equality or proof-field equality. *)

(** 生成元方程通过原 coend 外延性刻画整个下降映射，不使用代表或证明字段的原生相等。 *)

Lemma prof_comp_strength_unique
    (f : coend[ProfCompKernel Q P X Y] →r
      coend[ProfCompKernel Q P (Z ⊗ X) (Z ⊗ Y)])
    (Hf : ∀ B (x : P (X,B)) (y : Q (B,Y)),
      f (ιPr[Q; P; B] (x,y)) ≈S
        ιPr[Q; P; Z ⊗ B] (pstrength[SP; Z] x,pstrength[SQ; Z] y))
  : f ≈f prof_comp_strength.
Proof.
  apply (@prof_comp_hom_ext C C C Q P X Y HS). intros B [x y].
  transitivity (ιPr[Q; P; Z ⊗ B]
    (pstrength[SP; Z] x,pstrength[SQ; Z] y)).
  - exact (Hf B x y).
  - symmetry. exact (prof_comp_strength_inject B x y).
Defined.

End FixedBoundaries.

Context `{HC : !HasProfComp C C C Q P}.

(** Endpoint naturality follows on generators from the single-sided
    naturality of each input, without additional composition choices. *)

(** 端点自然性在生成元上由各输入的单侧自然性得到，不增加复合选择。 *)

Lemma prof_comp_strength_natural (Z : @Ob C)
    {X X' Y Y' : @Ob C} (f : Hom X' X) (g : Hom Y Y')
  : (prof_comp_strength Z X' Y' ∘r dimap[Q ∘Pr P; f; g]) ≈f
      (dimap[Q ∘Pr P; Z ⊲ f; Z ⊲ g] ∘r prof_comp_strength Z X Y).
Proof.
  apply (@prof_comp_hom_ext C C C Q P X Y
    (@hasProfCompCoend C C C Q P HC X Y)). intros B [x y].
  change (prof_comp_strength Z X' Y'
    (dimap[Q ∘Pr P; f; g] (ιPr[Q; P; B] (x,y))) ≈S
    dimap[Q ∘Pr P; Z ⊲ f; Z ⊲ g]
      (prof_comp_strength Z X Y (ιPr[Q; P; B] (x,y)))).
  transitivity (prof_comp_strength Z X' Y'
    (ιPr[Q; P; B] (lmap[P; f] x,rmap[Q; g] y))).
  - apply func_proper. apply prof_comp_dimap_inject.
  - rewrite prof_comp_strength_inject.
    transitivity (ιPr[Q; P; Z ⊗ B]
      (lmap[P; Z ⊲ f] (pstrength[SP; Z] x),
        rmap[Q; Z ⊲ g] (pstrength[SQ; Z] y))).
    + apply func_proper. split.
      * exact (prof_strength_lmap SP Z f x).
      * exact (prof_strength_rmap SQ Z g y).
    + symmetry. transitivity (dimap[Q ∘Pr P; Z ⊲ f; Z ⊲ g]
        (ιPr[Q; P; Z ⊗ B] (pstrength[SP; Z] x,pstrength[SQ; Z] y))).
      * apply func_proper. exact (prof_comp_strength_inject Z X Y B x y).
      * apply prof_comp_dimap_inject.
Defined.

(** Package the same components into the existing context reindexing. *)

(** 将同一组分量打包到已有上下文重索引。 *)

Program Definition ProfCompStrengthN (Z : @Ob C)
  : Q ∘Pr P ⇒ ProfContext MC (Q ∘Pr P) Z
  :=
  {|nt XY := prof_comp_strength Z (fst XY) (snd XY)
  |}.
Next Obligation.
  exact (prof_comp_strength_natural Z (fst f) (snd f)).
Defined.

(** Context substitution may be noninvertible. Its middle component moves
    between the factors by the same coend gluing equation. *)

(** 上下文代入不必可逆，其中间分量通过同一 coend 粘合方程在因子间移动。 *)

Lemma prof_comp_strength_context {Z W : @Ob C} (h : Hom Z W)
    (X Y : @Ob C)
  : (lmap[Q ∘Pr P; h ⊗m @id X] ∘r prof_comp_strength W X Y) ≈f
      (rmap[Q ∘Pr P; h ⊗m @id Y] ∘r prof_comp_strength Z X Y).
Proof.
  apply (@prof_comp_hom_ext C C C Q P X Y
    (@hasProfCompCoend C C C Q P HC X Y)). intros B [x y].
  change (lmap[Q ∘Pr P; h ⊗m @id X]
    (prof_comp_strength W X Y (ιPr[Q; P; B] (x,y))) ≈S
    rmap[Q ∘Pr P; h ⊗m @id Y]
      (prof_comp_strength Z X Y (ιPr[Q; P; B] (x,y)))).
  rewrite !prof_comp_strength_inject.
  rewrite profunctor_comp_lmap_inject, profunctor_comp_rmap_inject.
  transitivity (ιPr[Q; P; W ⊗ B]
    (rmap[P; h ⊗m @id B] (pstrength[SP; Z] x),pstrength[SQ; W] y)).
  - apply func_proper. split; [| reflexivity].
    exact (prof_strength_context SP h X B x).
  - transitivity (ιPr[Q; P; Z ⊗ B]
      (pstrength[SP; Z] x,lmap[Q; h ⊗m @id B] (pstrength[SQ; W] y))).
    + symmetry. exact (prof_comp_gluing Q P (h ⊗m @id B)
        (pstrength[SP; Z] x) (pstrength[SQ; W] y)).
    + apply func_proper. split; [reflexivity |].
      exact (prof_strength_context SQ h B Y y).
Defined.

(** Remove the unit context in each factor; the middle unitor is glued
    between them. Only the original selected unit boundaries are used. *)

(** 在各因子中移去单位上下文，并将中间单位子在它们之间粘合；只使用原选定单位边界。 *)

Lemma prof_comp_strength_unit (X Y : @Ob C)
  : (rmap[Q ∘Pr P; λ⊗[Y]] ∘r prof_comp_strength (I⊗[MC]) X Y) ≈f
      lmap[Q ∘Pr P; λ⊗[X]].
Proof.
  apply (@prof_comp_hom_ext C C C Q P X Y
    (@hasProfCompCoend C C C Q P HC X Y)). intros B [x y].
  change (rmap[Q ∘Pr P; λ⊗[Y]]
    (prof_comp_strength (I⊗[MC]) X Y (ιPr[Q; P; B] (x,y))) ≈S
    lmap[Q ∘Pr P; λ⊗[X]] (ιPr[Q; P; B] (x,y))).
  rewrite prof_comp_strength_inject.
  rewrite profunctor_comp_lmap_inject, profunctor_comp_rmap_inject.
  transitivity (ιPr[Q; P; I⊗[MC] ⊗ B]
    (pstrength[SP; I⊗[MC]] x,lmap[Q; λ⊗[B]] y)).
  - apply func_proper. split; [reflexivity |].
    exact (prof_strength_unit SQ B Y y).
  - transitivity (ιPr[Q; P; B]
      (rmap[P; λ⊗[B]] (pstrength[SP; I⊗[MC]] x),y)).
    + exact (prof_comp_gluing Q P (λ⊗[B]) (pstrength[SP; I⊗[MC]] x) y).
    + apply func_proper. split; [| reflexivity].
      exact (prof_strength_unit SP X B x).
Defined.

(** Nested context extension uses the two original associativity laws.
    Gluing their middle associator retains the same outer boundaries. *)

(** 嵌套上下文扩展使用两个原结合律；粘合它们的中间结合子保留同一组外部边界。 *)

Lemma prof_comp_strength_assoc (Z W X Y : @Ob C)
  : (lmap[Q ∘Pr P; α⊗[Z; W; X]] ∘r
      prof_comp_strength Z (W ⊗ X) (W ⊗ Y) ∘r
      prof_comp_strength W X Y) ≈f
      (rmap[Q ∘Pr P; α⊗[Z; W; Y]] ∘r prof_comp_strength (Z ⊗ W) X Y).
Proof.
  apply (@prof_comp_hom_ext C C C Q P X Y
    (@hasProfCompCoend C C C Q P HC X Y)). intros B [x y].
  change (lmap[Q ∘Pr P; α⊗[Z; W; X]]
    (prof_comp_strength Z (W ⊗ X) (W ⊗ Y)
      (prof_comp_strength W X Y (ιPr[Q; P; B] (x,y)))) ≈S
    rmap[Q ∘Pr P; α⊗[Z; W; Y]]
      (prof_comp_strength (Z ⊗ W) X Y (ιPr[Q; P; B] (x,y)))).
  rewrite !prof_comp_strength_inject.
  rewrite profunctor_comp_lmap_inject, profunctor_comp_rmap_inject.
  transitivity (ιPr[Q; P; Z ⊗ (W ⊗ B)]
    (rmap[P; α⊗[Z; W; B]] (pstrength[SP; Z ⊗ W] x),
      pstrength[SQ; Z] (pstrength[SQ; W] y))).
  - apply func_proper. split; [| reflexivity].
    exact (prof_strength_assoc SP Z W X B x).
  - transitivity (ιPr[Q; P; (Z ⊗ W) ⊗ B]
      (pstrength[SP; Z ⊗ W] x,
        lmap[Q; α⊗[Z; W; B]] (pstrength[SQ; Z] (pstrength[SQ; W] y)))).
    + symmetry. exact (prof_comp_gluing Q P (α⊗[Z; W; B])
        (pstrength[SP; Z ⊗ W] x) (pstrength[SQ; Z] (pstrength[SQ; W] y))).
    + apply func_proper. split; [reflexivity |].
      exact (prof_strength_assoc SQ Z W B Y y).
Defined.

(** Explicitly enable the composite strength on the supplied composition.
    Importing the module registers no chosen strength or coend model. *)

(** 在给定复合上显式启用复合强度；导入模块不注册选定强度或 coend 模型。 *)

Program Definition ProfCompStrength
  : HasProfStrength MC (Q ∘Pr P)
  :=
  {|prof_strengthN Z := ProfCompStrengthN Z
  ; prof_strength_context Z W h X Y := prof_comp_strength_context h X Y
  ; prof_strength_unit X Y := prof_comp_strength_unit X Y
  ; prof_strength_assoc Z W X Y := prof_comp_strength_assoc Z W X Y
  |}.

End CompositionStrength.
