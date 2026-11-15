From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Preorder
  Cat.Adjunction.

(** * Adjunctions from Type-Valued Preorder Correspondences

    Relation witnesses are retained as arrows. The specified equality of
    parallel witnesses is thin, so a two-way entailment correspondence
    suffices for the existing adjunction interface; no native inverse
    equations or propositional truncations of the witnesses are required. *)

(** * 由 Type 值预序对应构造伴随

    关系见证保留为箭头。平行见证的指定相等是薄的，因此双向蕴含对应足以给出
    既有伴随接口；不要求见证的原生互逆等式，也不作命题截断。 *)

(** ** General Preorder Functors

    Fix two preorders and functors between their categories. Relation,
    hom-equality and law bounds are independently supplied on both sides.
    The correspondence's two maps remain computational data. *)

(** ** 一般预序函子

    固定两个预序及其范畴之间的函子。两侧分别给定关系、Hom 相等与定律界；
    对应的两个映射保持为计算数据。 *)

Section PreorderAdjunction.
Universes x y r s p q l m.
Context {X : Type@{x}} {Y : Type@{y}}
    {R : crelation@{x r} X} {S : crelation@{y s} Y}
    `{HR : !PreOrder R} `{HS : !PreOrder S}.
Let C
  : Cat@{x r p l l}
  := @PreorderCatAt@{x r p l} X R HR.
Let D
  : Cat@{y s q m m}
  := @PreorderCatAt@{y s q m} Y S HS.
Context (F : Fct C D) (G : Fct D C).
Context (H : ∀ x y, S (F x) y ↔ R x (G y)).

(** The forward comparison map is respectful for the specified thin
    hom equality, while preserving the supplied witness transformation. *)

(** 正向比较映射对指定的薄 Hom 相等保相等，同时保留给定的见证变换。 *)

Program Definition preorder_adjunct_resp (x : X) (y : Y)
  : @HomSet D (F x) y →r @HomSet C x (G y)
  :=
  {|func h := fst (H x y) h
  |}.
Next Obligation. repeat intro; exact tt. Defined.

(** The reverse comparison map retains the other supplied transformation. *)

(** 反向比较映射保留另一给定变换。 *)

Program Definition preorder_unadjunct_resp (x : X) (y : Y)
  : @HomSet C x (G y) →r @HomSet D (F x) y
  :=
  {|func h := snd (H x y) h
  |}.
Next Obligation. repeat intro; exact tt. Defined.

(** Assemble the existing adjunction from the two native hom maps.
    Inverse and naturality laws use thin equality, not witness equality. *)

(** 从两个原生 Hom 映射组装既有伴随；互逆与自然性使用薄相等，不用见证相等。 *)

Definition PreorderAdj
  : F ⊣ G.
Proof.
  refine (AdjFromHom F G preorder_adjunct_resp preorder_unadjunct_resp
    _ _ _ _); repeat intro; exact tt.
Defined.

(** Forward transposition computes to the supplied correspondence map. *)

(** 正向转置计算为给定对应的正向映射。 *)

Definition preorder_adjunct_data (x : X) (y : Y) (h : S (F x) y)
  : adjunct PreorderAdj h = fst (H x y) h
  := eq_refl.

(** Reverse transposition computes to the supplied reverse map. *)

(** 反向转置计算为给定对应的反向映射。 *)

Definition preorder_unadjunct_data (x : X) (y : Y) (h : R x (G y))
  : unadjunct PreorderAdj h = snd (H x y) h
  := eq_refl.

End PreorderAdjunction.

(** ** Recovering a Correspondence

    An adjunction of the same general preorder functors supplies maps of
    relation witnesses in both directions. This does not identify two
    chosen correspondences by equality. *)

(** ** 取回对应

    同一类一般预序函子的伴随给出关系见证的双向映射；不将两个选定对应用
    相等识别。 *)

Section PreorderCorrespondence.
Universes x y r s p q l m.
Context {X : Type@{x}} {Y : Type@{y}}
    {R : crelation@{x r} X} {S : crelation@{y s} Y}
    `{HR : !PreOrder R} `{HS : !PreOrder S}.
Let C
  : Cat@{x r p l l}
  := @PreorderCatAt@{x r p l} X R HR.
Let D
  : Cat@{y s q m m}
  := @PreorderCatAt@{y s q m} Y S HS.
Context {F : Fct C D} {G : Fct D C} (A : F ⊣ G).

(** Recover the Type-valued entailment correspondence by native transposes. *)

(** 用原生转置取回 Type 值蕴含对应。 *)

Definition preorder_adjunction_correspondence (x : X) (y : Y)
  : S (F x) y ↔ R x (G y)
  := (adjunct A, unadjunct A).

End PreorderCorrespondence.

(** ** Monotone Functions

    Specialize to the existing functors induced by two monotone functions.
    Use the usual preorder categories, without new functor or adjunction
    fields, and keep the given monotonicity maps. *)

(** ** 单调函数

    特化到既有的两个单调函数所诱导函子；使用通常的预序范畴，不新增函子或
    伴随字段，并保留给定的单调映射。 *)

Section MonotoneAdjunction.
Context {X Y : Type} {R : crelation X} {S : crelation Y}
    `{HR : !PreOrder R} `{HS : !PreOrder S}
    (f : X → Y) (g : Y → X)
    (Hf : ∀ x x', R x x' → S (f x) (f x'))
    (Hg : ∀ y y', S y y' → R (g y) (g y'))
    (H : ∀ x y, S (f x) y ↔ R x (g y)).

(** The monotone-map correspondence gives an adjunction of the existing
    preorder functors; it does not choose any model structures globally. *)

(** 单调映射对应给出既有预序函子之间的伴随，不全局选择任何模型结构。 *)

Definition PreorderFAdj
  : PreorderF f Hf ⊣ PreorderF g Hg
  := PreorderAdj (PreorderF f Hf) (PreorderF g Hg) H.

End MonotoneAdjunction.
