From Cats.Cat.Functor Require Import RelationGluing.
From Cats Require Import
  Cat.Preorder
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Nat.

(** * Relation Gluing Interface Regressions

    Relation witnesses can be larger than setoid equality, or smaller
    than both carriers and equality. A concrete identity action changes
    the retained witness while preserving the glued setoid value. *)

(** ** Witnesses above Equality

    Fix [q < w < u]. Both diagrams share the ambient bounds [u] and [q];
    their constant relation retains arbitrary [Type@{w}] data. *)

Section LargeWitnesses.
Universes q w u.
Constraint q < w, w < u.
Context {J : Cat} (F G : Fct J SetCat@{u q _ _ _ _ _}).
Context (W : Type@{w}).

(** No equation between the retained witnesses is required. *)

Program Definition LargeRelation
  : DiagramRelation F G
  :=
  {|diagram_relation X x y := W
  ; diagram_relation_map X Y f x y h := h
  |}.
Next Obligation. intros x x' hx y y' hy. exact ((λ h, h), (λ h, h)). Defined.

(** Gluing does not raise the specified equality bound to [w]. *)

Definition large_witness_gluing
  : Fct J SetCat@{u q _ _ _ _ _}
  := RelationGluingF F G LargeRelation.

End LargeWitnesses.

(** ** Equality above Carriers

    Fix [w < u < q], reversing the witness/equality order and permitting
    equality above the common carrier bound. *)

Section LargeEquality.
Universes w u q.
Constraint w < u, u < q.
Context {J : Cat} (F G : Fct J SetCat@{u q _ _ _ _ _}).
Context (W : Type@{w}).

(** Membership stays at the smaller witness bound. *)

Program Definition SmallRelation
  : DiagramRelation F G
  :=
  {|diagram_relation X x y := W
  ; diagram_relation_map X Y f x y h := h
  |}.
Next Obligation. intros x x' hx y y' hy. exact ((λ h, h), (λ h, h)). Defined.

(** Large equality does not enlarge the glued carrier. *)

Definition large_equality_gluing
  : Fct J SetCat@{u q _ _ _ _ _}
  := RelationGluingF F G SmallRelation.

End LargeEquality.

(** ** Computational Witnesses and Setoid Laws

    Use a one-object world and two constant natural-number diagrams.
    Every pair is related by a natural-number tag. Arrow transport
    increments the tag, so witness transport is deliberately not strict
    on identities. The glued functor laws compare only the two values. *)

Section Tags.

(** The same constant diagram on either side. *)

Definition NumbersF
  : Fct (CodiscreteCat unit) SetCat
  := ConstF (CodiscreteCat unit) (C := SetCat) NatS.

(** Tags remain data, with arbitrary maps between the membership types. *)

Program Definition TaggedRelation
  : DiagramRelation NumbersF NumbersF
  :=
  {|diagram_relation X x y := nat
  ; diagram_relation_map X Y f x y h := S h
  |}.

(** A displayed related pair with tag seven. *)

Definition tagged_pair
  : RelationGluingF NumbersF NumbersF TaggedRelation tt
  := ((2, 3); 7).

(** Identity transport computes the changed tag, while preserving values. *)

Example identity_tag_computes
  : let p := fmap (RelationGluingF NumbersF NumbersF TaggedRelation)
      (@Cats.Cat.Core.id (CodiscreteCat unit) tt) tagged_pair in
    (p.1, p.2) = ((2, 3), 8).
Proof. reflexivity. Defined.

(** The functor identity still holds in the specified setoid equality. *)

Example identity_values_agree
  : fmap (RelationGluingF NumbersF NumbersF TaggedRelation)
      (@Cats.Cat.Core.id (CodiscreteCat unit) tt) tagged_pair ≈S tagged_pair.
Proof. exact (eq_refl, eq_refl). Defined.

End Tags.
