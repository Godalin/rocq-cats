From Cats Require Import
  Instance.Set.Simplicial.Vertex.Product
  Instance.Set.Simplicial.Vertex.Terminal
  Instance.Set.Simplicial.Vertex.Edge
  Instance.Set.Simplicial.Vertex.Monoid
  Instance.Bool.Group
  Cat.Core.

Local Open Scope nat_scope.

(** * Transparent Product and Terminal Comparisons

    Nonidentical boolean edges must survive pairing and projection through
    the lifted nerve comparison. These equations check actual computation,
    rather than only the round-trip equivalences. *)

(** The xor monoid supplies a singleton presentation with distinct loops. *)

Definition BooleanPresentation
  := MonoidObjF BoolS_Monoid.

(** Pairing retains both distinct boolean components. *)

Example product_pair_computes
  : let t := BooleanPresentation in
    let z := ((vertex_nerve_product_iso t t).2 1).1
      (△₁[t; tt; tt] true, △₁[t; tt; tt] false) in
    fmap (lower z) (ordinal_step fin_first) = (true, false).
Proof. reflexivity. Qed.

(** Projecting a product edge computes both component arrows. *)

Example product_split_computes
  : let t := BooleanPresentation in
    let z := △₁[VtxProductObjF t t; (tt, tt); (tt, tt)] (true, false) in
    let xy := VtxNerveProductN t t 1 z in
    (fmap (lower (fst xy)) (ordinal_step fin_first),
     fmap (lower (snd xy)) (ordinal_step fin_first)) = (true, false).
Proof. reflexivity. Qed.

(** The inverse terminal comparison has a computable singleton edge. *)

Example terminal_inverse_computes
  : fmap (lower ((vertex_nerve_terminal_iso.2 1).1 tt))
      (ordinal_step fin_first) = tt.
Proof. reflexivity. Qed.
