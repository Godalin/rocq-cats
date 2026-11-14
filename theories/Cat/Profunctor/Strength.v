From Cats Require Export
  Cat.Profunctor.Core
  Cat.Monoidal.Core.
From Cats Require Import
  Instance.Set.Core.

Local Open Scope binoidal_scope.
Local Open Scope monoidal_scope.
Local Open Scope profunctor_scope.

(** * Left-Context Profunctor Strength

    A strength carries the same ordinary left context across both ends of
    a profunctor value. Fixing that context gives a natural transformation
    into an existing reindexing. Varying the context requires dinaturality;
    unit and associator laws specify its coherence. Neither symmetry,
    cartesian structure nor coend existence is assumed. *)

(** * 左上下文 Profunctor 强度

    强度让同一通常左上下文穿过 profunctor 值的两端。固定上下文时，作用是
    到已有重索引的自然变换；改变上下文需要双自然性，单位及结合定律
    指定其相干性。不要求对称性、笛卡尔结构或 coend 存在。 *)

(** Extend both profunctor boundaries by the same selected left context.
    This is just the existing reindexing, with its value bounds explicit. *)

(** 用同一选定左上下文扩展 profunctor 两端；这只是值界显式的已有重索引。 *)

Definition ProfunctorContext@{u p +} {C : Cat} (MC : MonoidalCat C)
    (P : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})) (Z : @Ob C)
  : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})
  := ProfunctorReindex (@BinoidalLeftF C MC Z) (@BinoidalLeftF C MC Z) P.

(** ** Chosen Strength on a Supplied Profunctor

    Fix a named monoidal category and a setoid-valued profunctor on it.
    Keep carrier and equality levels independent. The existing left-context
    functor supplies both boundary actions, without another tensor choice. *)

(** ** 给定 Profunctor 上的选定强度

    固定具名幺半范畴及其上的广集值 profunctor，保持载体及相等层级独立。
    已有左上下文函子提供两端作用，不另选张量。 *)

Section Interface.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C).
Context (P : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})).

Class HasProfunctorStrength
  :=
  (** Naturality in input and output is stored once, as an ordinary
      transformation; the underlying profunctor is the supplied parameter. *)

  (** 输入及输出自然性只保存一次，作为通常自然变换；底层 profunctor 为给定参数。 *)

  { profunctor_strengthN (Z : @Ob C)
      : P ⇒ ProfunctorContext MC P Z

  (** Substitution in the ordinary context may be performed on either end.
      This is dinaturality, not an invertibility requirement on that map. *)

  (** 通常上下文代入可在任一端进行；这是双自然性，不要求该映射可逆。 *)

  ; profunctor_strength_context {Z W : @Ob C} (h : Hom Z W)
      (X Y : @Ob C)
      : (lmap[P; h ⊗m @id X] ∘r profunctor_strengthN W (X,Y)) ≈f
          (rmap[P; h ⊗m @id Y] ∘r profunctor_strengthN Z (X,Y))

  (** Remove the unit through the two specified left-unitor boundaries. *)

  (** 通过两端指定左单位子移去单位上下文。 *)

  ; profunctor_strength_unit (X Y : @Ob C)
      : (rmap[P; λ⊗[Y]] ∘r profunctor_strengthN (I⊗[MC]) (X,Y)) ≈f
          lmap[P; λ⊗[X]]

  (** Nested contexts agree after the supplied associator boundaries;
      this law does not identify endpoints by native object equality. *)

  (** 嵌套上下文经给定结合子边界后相等，不用原生对象相等识别两端。 *)

  ; profunctor_strength_assoc (Z W X Y : @Ob C)
      : (lmap[P; α⊗[Z; W; X]] ∘r
          profunctor_strengthN Z (W ⊗ X,W ⊗ Y) ∘r
          profunctor_strengthN W (X,Y)) ≈f
          (rmap[P; α⊗[Z; W; Y]] ∘r
            profunctor_strengthN (Z ⊗ W) (X,Y))
  }.

End Interface.

Arguments HasProfunctorStrength {_} _ _.
Arguments profunctor_strengthN {_ _ _} _ _.
Arguments profunctor_strength_context {_ _ _} _ {_ _} _ _ _.
Arguments profunctor_strength_unit {_ _ _} _ _ _.
Arguments profunctor_strength_assoc {_ _ _} _ _ _ _ _.

(** The pointwise action retains the component's existing respectful map. *)

(** 逐点作用保留分量已有的尊重映射。 *)

Definition profunctor_strength {C : Cat} {MC : MonoidalCat C}
    {P : Fct ((C^op) ×C C) SetCat} (S : HasProfunctorStrength MC P)
    (Z : @Ob C) {X Y : @Ob C}
  : P (X,Y) →r P (Z ⊗ X,Z ⊗ Y)
  := profunctor_strengthN S Z (X,Y).

Notation "'pstrength[' S ';' Z ']'" := (profunctor_strength S Z)
  : profunctor_scope.

(** Naturality in both profunctor arguments is inherited from the single
    stored transformation, with the same fixed-context functor on both ends. *)

(** 两个 profunctor 变元的自然性均继承自唯一存储的变换，两端使用同一固定上下文函子。 *)

Lemma profunctor_strength_natural {C : Cat} {MC : MonoidalCat C}
    {P : Fct ((C^op) ×C C) SetCat} (S : HasProfunctorStrength MC P)
    (Z : @Ob C) {X X' Y Y' : @Ob C} (f : Hom X' X) (g : Hom Y Y')
  : (pstrength[S; Z] ∘r dimap[P; f; g]) ≈f
      (dimap[P; Z ⊲ f; Z ⊲ g] ∘r pstrength[S; Z]).
Proof.
  exact (nt_naturality (profunctor_strengthN S Z)
    (X := (X,Y)) (Y := (X',Y')) (f,g)).
Defined.
