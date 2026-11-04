From Cats Require Import
  Cat.Core
  Cat.Product.Transport.
From Cats Require Export
  Cat.Coproduct.Core.

(** * Transport of Coproduct Cocones *)

(** * 余积余锥的运输 *)

(** Equal injections retain the original opposite product property. *)

(** 相等注入保留原反积性质。 *)

Definition coproduct_cocone_equiv {C : Cat} {X Y P : @Ob C}
    {i i' : Hom X P} {j j' : Hom Y P} (Hi : i ≈ i') (Hj : j ≈ j')
    (HP : is_coproduct X Y P i j)
  : is_coproduct X Y P i' j'
  := @product_cone_equiv (C^op) X Y P i i' j j' Hi Hj HP.

(** Isomorphisms of summands induce a coproduct isomorphism through the
    original product isomorphism in the opposite category. *)

(** 加数同构通过反范畴中的原积同构诱导余积同构。 *)

Definition coproduct_iso {C : Cat} `{HC : !HasCoproduct C}
    {X Y X' Y' : @Ob C} (i : X ≅ X') (j : Y ≅ Y')
  : (X ⊔ Y) ≅ (X' ⊔ Y').
Proof.
  pose (e := @product_iso (C^op) (@hasOpProduct C HC) X Y X' Y'
    (i.2.1; (i.1; i.2.2)) (j.2.1; (j.1; j.2.2))).
  exists e.2.1, e.1. exact e.2.2.
Defined.

(** Maps out of a candidate coproduct are detected by its two injections. *)

(** 从候选余积出发的映射由其两个注入检测。 *)

Lemma coproduct_cocone_ext {C : Cat} {X Y P Z : @Ob C}
    {i : Hom X P} {j : Hom Y P} (HP : is_coproduct X Y P i j)
    {f g : Hom P Z} (H1 : f ∘ i ≈ g ∘ i) (H2 : f ∘ j ≈ g ∘ j)
  : f ≈ g.
Proof. exact (@product_cone_ext (C^op) X Y P Z i j HP f g H1 H2). Qed.
