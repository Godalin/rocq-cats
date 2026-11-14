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

(** * 透明的积与终比较

    不同布尔边须穿过提升后的 nerve 比较，在配对及投影后保留。
    这些方程检查实际计算，而不仅是往返等价。 *)

(** The xor monoid supplies a singleton presentation with distinct loops. *)

(** 异或幺半群提供具有不同环路的单元素呈现。 *)

Definition BooleanPresentation
  := MonoidObjF BoolS (HM := BoolS_Monoid).

(** Pairing retains both distinct boolean components. *)

(** 配对保留两个不同的布尔分量。 *)

Example product_pair_computes
  : let t := BooleanPresentation in
    let z := ((vertex_nerve_product_iso t t).2 1).1
      (△₁[t; tt; tt] true, △₁[t; tt; tt] false) in
    fmap (lower z) (ordinal_step fin_first) = (true, false).
Proof. reflexivity. Qed.

(** Projecting a product edge computes both component arrows. *)

(** 投影积边计算出两个分量箭头。 *)

Example product_split_computes
  : let t := BooleanPresentation in
    let z := △₁[VertexProductObjF t t; (tt, tt); (tt, tt)] (true, false) in
    let xy := VertexNerveProductN t t 1 z in
    (fmap (lower (fst xy)) (ordinal_step fin_first),
     fmap (lower (snd xy)) (ordinal_step fin_first)) = (true, false).
Proof. reflexivity. Qed.

(** The inverse terminal comparison has a computable singleton edge. *)

(** 终比较的逆具有可计算的单元素边。 *)

Example terminal_inverse_computes
  : fmap (lower ((vertex_nerve_terminal_iso.2 1).1 tt))
      (ordinal_step fin_first) = tt.
Proof. reflexivity. Qed.
