From Cats Require Export Cat.Core.
From Cats Require Import Cat.Functor.Core.

(** * Categories from Type-Valued Preorders

    Relation witnesses are morphisms; parallel witnesses are equivalent. This
    specifies a thin category without equating the witnesses by [eq]. *)

(** * 由 Type 值预序构造范畴

    关系见证作为态射，平行见证均等价；由此指定薄范畴，不用原生相等识别见证。 *)

Program Definition PreorderCat {X : Type} (R : crelation X) `{HR : !PreOrder R}
  : Cat
  :=
  {|Ob := X
  ; HomSet x y :=
      {|carrier := R x y
      ; carrier_equiv _ _ := unit
      |}
  ; id x := reflexivity x
  ; comp x y z g f := transitivity f g
  |}.
Next Obligation. split; repeat intro; exact tt. Defined.
Next Obligation. repeat intro; exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** A relation-preserving function induces a functor of preorder categories. *)

(** 保持关系的函数诱导预序范畴之间的函子。 *)

Program Definition PreorderF {X Y : Type} {R : crelation X} {S : crelation Y}
    `{HR : !PreOrder R} `{HS : !PreOrder S}
    (f : X → Y) (Hf : ∀ x y, R x y → S (f x) (f y))
  : Functor (PreorderCat R) (PreorderCat S)
  :=
  {|F0 := f
  ; F1 x y := Hf x y
  |}.
Next Obligation. repeat intro; exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** Forget symmetry to view an equivalence relation as a preorder. *)

(** 忘去对称性，将等价关系视为预序。 *)

Program Definition equivalence_preorder {X : Type} (R : crelation X)
    `{HR : !Equivalence R}
  : PreOrder R
  :=
  {|PreOrder_Reflexive := Equivalence_Reflexive
  ; PreOrder_Transitive := Equivalence_Transitive
  |}.

(** Pull a preorder back along an ordinary function. *)

(** 沿普通函数拉回预序。 *)

Program Definition pullback_preorder {X Y : Type} (R : crelation Y)
    `{HR : !PreOrder R} (f : X → Y)
  : PreOrder (λ x y, R (f x) (f y))
  :=
  {|PreOrder_Reflexive := _
  ; PreOrder_Transitive := _
  |}.
Next Obligation. intros x. apply reflexivity. Defined.
Next Obligation. intros x y z H K. exact (transitivity H K). Defined.

(** The always-inhabited relation is a preorder. *)

(** 处处有见证的关系是预序。 *)

Program Definition codiscrete_preorder (X : Type)
  : PreOrder (λ _ _ : X, unit)
  :=
  {|PreOrder_Reflexive := _
  ; PreOrder_Transitive := _
  |}.
Next Obligation. intros x. exact tt. Defined.
Next Obligation. repeat intro; exact tt. Defined.

(** The category with exactly one morphism up to equivalence between any two
    objects. *)

(** 任意两对象间在等价下恰有一条态射的范畴。 *)

Definition CodiscreteCat (X : Type)
  : Cat
  := @PreorderCat X (λ _ _, unit) (codiscrete_preorder X).

(** Any two objects of a codiscrete category are isomorphic. *)

(** 余离散范畴的任意两对象同构。 *)

Definition codiscrete_iso {X : Type} (x y : X)
  : x ≅[CodiscreteCat X] y.
Proof. exists tt, tt. split; exact tt. Defined.
