From Cats Require Import
  Instance.Set.Simplicial.Vertex.Category
  Instance.Set.Simplicial.Vertex.Monoid
  Instance.Bool.Group
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

Local Open Scope nat_scope.

(** * Computing through the Fully Faithful Nerve Functor

    Identity images and chosen preimages must retain the nonidentity xor
    loop, even after bundling and extracting the fullness witness. *)

(** Bundle the existing singleton-labelled boolean action. *)

Definition BooleanPresentation
  : VtxPresentation@{Set Set Set Set Set Set Set Set}
  := VtxPresentationOf (MonoidObjF BoolS_Monoid).

(** All values remain at the small carrier and equality levels. *)

Definition BooleanNerveFunctor
  : Fct
      VtxPresentationCat@{Set Set Set Set Set Set Set Set _ _ _ _ _ _ _ _ _ _}
      (FctCat (Δ^op) SetCat@{Set Set _ _ _ _ _})
  := VtxNerveF.

(** The general full-faithfulness proof specializes without new choices. *)

Definition BooleanNerveFullyFaithful
  : is_fully_faithful BooleanNerveFunctor
  := vertex_nerve_fully_faithful.

(** Existing unbundled maps enter the new category without changing arrows. *)

Definition BooleanIdentity
  : (@Hom VtxPresentationCat) BooleanPresentation BooleanPresentation
  := VtxPresentationMap
      (VtxIdF (MonoidObjF BoolS_Monoid)).

Example bundled_existing_map_computes
  : fmap BooleanIdentity
      (true : (@Hom (VtxCat BooleanPresentation)) tt tt) = true.
Proof. reflexivity. Qed.

(** The image of the presentation identity computes on a nonidentity edge. *)

Example nerve_identity_computes
  : let P := BooleanPresentation in
    let e := △₁[P; tt; tt] true in
    fmap (lower (fmap BooleanNerveFunctor
      (@Cats.Cat.Core.id VtxPresentationCat P) 1 e))
      (ordinal_step fin_first) = true.
Proof. reflexivity. Qed.

(** Fullness returns an actual presentation morphism with a computable
    arrow map, rather than an opaque existence witness. *)

Example nerve_fullness_preimage_computes
  : fmap (fst BooleanNerveFullyFaithful
      BooleanPresentation BooleanPresentation IdN).1
      (true : (@Hom (VtxCat BooleanPresentation)) tt tt) = true.
Proof. reflexivity. Qed.
