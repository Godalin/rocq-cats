From Cats Require Import Cat.Core Cat.Functor Cat.Natural.

(** * Arrow Categories

    Morphisms retain commuting squares. Their equality compares the two
    maps, without comparing the commutativity witnesses. *)

Record ArrowOb (C : Cat) :=
  { arrow_dom : @Ob C
  ; arrow_cod : @Ob C
  ; arrow_map : Hom arrow_dom arrow_cod
  }.

Arguments arrow_dom {_} _.
Arguments arrow_cod {_} _.
Arguments arrow_map {_} _.

Record ArrowHom {C : Cat} (A B : ArrowOb C) :=
  { arrow_top : Hom (arrow_dom A) (arrow_dom B)
  ; arrow_bottom : Hom (arrow_cod A) (arrow_cod B)
  ; arrow_comm : arrow_map B ∘ arrow_top ≈ arrow_bottom ∘ arrow_map A
  }.

Arguments arrow_top {_ _ _} _.
Arguments arrow_bottom {_ _ _} _.
Arguments arrow_comm {_ _ _} _.

Definition ArrowHomEq {C : Cat} {A B : ArrowOb C} (f g : ArrowHom A B) :=
  arrow_top f ≈ arrow_top g ∧ arrow_bottom f ≈ arrow_bottom g.

Global Instance ArrowHomEq_Equivalence {C : Cat} {A B : ArrowOb C}
  : Equivalence (@ArrowHomEq C A B).
Proof.
  split.
  - intros f. split; reflexivity.
  - intros f g [Ht Hb]. split; symmetry; assumption.
  - intros f g h [Ht Hb] [Kt Kb]. split.
    + transitivity (arrow_top g); assumption.
    + transitivity (arrow_bottom g); assumption.
Defined.

Program Definition arrow_id {C : Cat} (A : ArrowOb C) : ArrowHom A A :=
  {| arrow_top := id; arrow_bottom := id |}.
Next Obligation. rewrite comp_id_r, comp_id_l. reflexivity. Defined.

Program Definition arrow_comp {C : Cat} {A B D : ArrowOb C}
    (g : ArrowHom B D) (f : ArrowHom A B) : ArrowHom A D :=
  {| arrow_top := arrow_top g ∘ arrow_top f
   ; arrow_bottom := arrow_bottom g ∘ arrow_bottom f |}.
Next Obligation.
  rewrite <- comp_assoc, (arrow_comm g), comp_assoc, (arrow_comm f),
    <- comp_assoc. reflexivity.
Defined.

Infix "∘Arr" := arrow_comp (at level 40, left associativity) : cat_scope.

Program Definition Arr (C : Cat) : Cat :=
  {| Ob := ArrowOb C
   ; HomSet A B :=
       {| carrier := ArrowHom A B
        ; carrier_equiv := ArrowHomEq
        ; carrier_setoid := ArrowHomEq_Equivalence |}
   ; id := arrow_id
   ; comp A B D := arrow_comp |}.
Next Obligation.
  intros g g' [Ht Hb] f f' [Kt Kb]. split; apply comp_proper; assumption.
Defined.
Next Obligation. split; apply comp_id_r. Defined.
Next Obligation. split; apply comp_id_l. Defined.
Next Obligation. split; apply comp_assoc. Defined.

Program Definition ArrowDomF (C : Cat) : Functor (Arr C) C :=
  {| F0 := arrow_dom; F1 A B := arrow_top |}.
Next Obligation. intros f g H. exact (fst H). Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

Program Definition ArrowCodF (C : Cat) : Functor (Arr C) C :=
  {| F0 := arrow_cod; F1 A B := arrow_bottom |}.
Next Obligation. intros f g H. exact (snd H). Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** A natural transformation is a functor into the arrow category. *)
Program Definition NatArrowF {C D : Cat} {F G : Functor C D} (α : F => G)
  : Functor C (Arr D) :=
  {| F0 X := {| arrow_dom := F X; arrow_cod := G X; arrow_map := α X |}
   ; F1 X Y f :=
       {| arrow_top := fmap F f; arrow_bottom := fmap G f
        ; arrow_comm := nt_naturality α f |} |}.
Next Obligation.
  intros f g H. exact (@functor_fmap_proper C D F X Y f g H,
    @functor_fmap_proper C D G X Y f g H).
Defined.
Next Obligation. exact (@functor_id C D F X, @functor_id C D G X). Defined.
Next Obligation.
  exact (@functor_comp C D F X Y Z f g, @functor_comp C D G X Y Z f g).
Defined.
