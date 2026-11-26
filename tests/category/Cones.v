From Stdlib Require Import
  Arith.PeanoNat.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Free
  Cat.Shape.Order
  Cat.Shape.Finite
  Cat.Diagram.Core
  Cat.Diagram.Presheaf.

(** A finite free shape uses its selected generating graph directly. *)

Definition free_generated_cones {n : nat} (k : Fin n → Fin n → nat)
    {C : Cat} (D : Fct (FreeCat (FiniteGraph k)) C)
  : ConeF D ≅N ConeF (D ∘F
      @generator_fct _ (FiniteGraphGen k))
  := generated_cone_nat_iso (HG := FiniteGraphGen k) D.

(** Interpret paths of underlying square arrows back in the commuting square.
    Fullness has a one-edge preimage and every object represents itself. *)

Definition SquareEvaluation
  : Fct (FreeCat (UnderlyingGraph SquareShape)) SquareShape
  := @FreeF (UnderlyingGraph SquareShape) SquareShape
      (GraphId (UnderlyingGraph SquareShape)).

Definition square_evaluation_full
  : is_full SquareEvaluation.
Proof.
  intros x y f. exists (@path_edge (UnderlyingGraph SquareShape) x y f).
  reflexivity.
Defined.

Definition square_evaluation_essentially_surjective
  : is_essentially_surjective SquareEvaluation.
Proof. intro x. exists x. apply iso_refl. Defined.

(** A nonfaithful path interpretation still gives the public natural
    isomorphism for every square diagram and target category. *)

Definition square_cone_comparison {C : Cat} (D : Fct SquareShape C)
  : ConeF D ≅N ConeF (D ∘F SquareEvaluation)
  := cone_reindex_nat_iso square_evaluation_full
      square_evaluation_essentially_surjective D.

(** Count occurrences of the top edge, distinguishing the two free routes
    while respecting the generated path equality. *)

Fixpoint square_top_count {x y}
    (p : Path (UnderlyingGraph SquareShape) x y)
  : nat
  := match p with
  | path_id _ => 0
  | @path_edge _ x y _ =>
      if fst x then 0 else if snd x then 0
      else if fst y then 0 else if snd y then 1 else 0
  | path_comp g f => square_top_count g + square_top_count f
  end.

Lemma square_top_count_proper {x y}
    (p q : Path (UnderlyingGraph SquareShape) x y) (H : p ≈P q)
  : square_top_count p = square_top_count q.
Proof.
  induction H; cbn; try reflexivity.
  - symmetry. assumption.
  - etransitivity; eassumption.
  - now rewrite IHPathEq1, IHPathEq2.
  - apply Nat.add_0_r.
  - now rewrite Nat.add_assoc.
Qed.

Definition square_upper_route
  : Path (UnderlyingGraph SquareShape) (false, false) (true, true)
  := path_comp
      (path_edge (G := UnderlyingGraph SquareShape) square_right)
      (path_edge (G := UnderlyingGraph SquareShape) square_top).

Definition square_lower_route
  : Path (UnderlyingGraph SquareShape) (false, false) (true, true)
  := path_comp
      (path_edge (G := UnderlyingGraph SquareShape) square_bottom)
      (path_edge (G := UnderlyingGraph SquareShape) square_left).

(** The free routes remain inequivalent even though their images commute. *)

Example square_free_routes_distinct
  : ¬ (square_upper_route ≈P square_lower_route).
Proof. intro H. discriminate (square_top_count_proper _ _ H). Qed.

Example square_routes_same_image
  : fmap SquareEvaluation square_upper_route
      ≈ fmap SquareEvaluation square_lower_route.
Proof. exact square_comm. Qed.
