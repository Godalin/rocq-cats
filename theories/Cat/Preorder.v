From Cats Require Export Cat.Core.
From Cats Require Import Cat.Functor.

(** * Categories from Type-Valued Preorders

    Relation witnesses are morphisms; parallel witnesses are equivalent.
    This specifies a thin category without equating the witnesses by [eq]. *)
Program Definition PreorderCat {X : Type} (R : crelation X) `{HR : !PreOrder R}
  : Cat
  := {| Ob := X
      ; HomSet x y := {| carrier := R x y; carrier_equiv _ _ := unit |}
      ; id x := reflexivity x
      ; comp x y z g f := transitivity f g |}.
Next Obligation. split; repeat intro; exact tt. Defined.
Next Obligation. repeat intro; exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

Program Definition PreorderF {X Y : Type} {R : crelation X} {S : crelation Y}
    `{HR : !PreOrder R} `{HS : !PreOrder S}
    (f : X → Y) (Hf : ∀ x y, R x y → S (f x) (f y))
  : Functor (PreorderCat R) (PreorderCat S)
  := {| F0 := f; F1 x y := Hf x y |}.
Next Obligation. repeat intro; exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

Program Definition pullback_preorder {X Y : Type} (R : crelation Y)
    `{HR : !PreOrder R} (f : X → Y)
  : PreOrder (λ x y, R (f x) (f y))
  := {| PreOrder_Reflexive := _; PreOrder_Transitive := _ |}.
Next Obligation. intros x. apply reflexivity. Defined.
Next Obligation. intros x y z H K. exact (transitivity H K). Defined.

Program Definition codiscrete_preorder (X : Type)
  : PreOrder (λ _ _ : X, unit)
  := {| PreOrder_Reflexive := _; PreOrder_Transitive := _ |}.
Next Obligation. intros x. exact tt. Defined.
Next Obligation. repeat intro; exact tt. Defined.

Definition CodiscreteCat (X : Type)
  : Cat
  := @PreorderCat X (λ _ _, unit) (codiscrete_preorder X).

Definition codiscrete_iso {X : Type} (x y : X)
  : x ≅[CodiscreteCat X] y.
Proof. exists tt, tt. split; exact tt. Defined.
