From Cats Require Export
  Cat.Functor.Product.
From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Natural
  Cat.Diagram.Core
  Cat.Terminal.

(** * Pointwise Finite Products in Functor Categories *)

(** * 函子范畴中的点态有限积 *)

Section Pointwise.
Context (J C : Cat) `{TC : !HasTerminal C} `{PC : !HasProduct C}.

(** The terminal component arrows assemble into a natural transformation. *)

(** 终对象的分量箭头组成自然变换。 *)

Program Definition PointwiseTerminalN (F : Functor J C)
  : F ⇒ ConstF J (@Term C TC)
  :=
  {|nt i := !
  |}.
Next Obligation.
  transitivity (@term C TC (F X)); [apply term_η | symmetry; apply term_η].
Defined.

(** The constant terminal diagram is terminal among all diagrams. *)

(** 常值终图式是全部图式中的终对象。 *)

Definition pointwise_terminal_universal
  : is_terminal (C := Fct J C) (ConstF J (@Term C TC)).
Proof.
  intros F. exists (PointwiseTerminalN F). split; [exact I |].
  intros α _ i. apply terminal_arrow_unique. exact I.
Defined.

(** Chosen terminal diagrams are enabled explicitly by clients. *)

(** 选定终图式由使用者显式启用。 *)

Program Definition Fct_HasTerminal
  : HasTerminal (Fct J C)
  :=
  {|Term := ConstF J (@Term C TC)
  ; terminal_universal := pointwise_terminal_universal
  |}.

(** Pointwise product projections are natural by the product equations. *)

(** 点态积投影由积方程保证自然性。 *)

Program Definition PointwiseFstN (F G : Functor J C)
  : PointwiseProductF F G ⇒ F
  :=
  {|nt i := π1
  |}.
Next Obligation. unfold cross. rewrite product_β1. reflexivity. Defined.

(** The second projection satisfies the other product equation. *)

(** 第二投影满足另一条积方程。 *)

Program Definition PointwiseSndN (F G : Functor J C)
  : PointwiseProductF F G ⇒ G
  :=
  {|nt i := π2
  |}.
Next Obligation. unfold cross. rewrite product_β2. reflexivity. Defined.

(** Pair natural transformations using the chosen component mediators. *)

(** 使用选定分量中介配对自然变换。 *)

Program Definition PointwisePairN {F G H : Functor J C}
    (α : H ⇒ F) (β : H ⇒ G)
  : H ⇒ PointwiseProductF F G
  :=
  {|nt i := ⟨α i, β i⟩
  |}.
Next Obligation.
  rewrite product_comp_r, product_comp_l, !nt_naturality. reflexivity.
Defined.

(** The pointwise cone satisfies the full product universal property. *)

(** 点态锥满足完整积泛性质。 *)

Definition pointwise_product_universal (F G : Functor J C)
  : is_product (C := Fct J C) F G (PointwiseProductF F G)
      (PointwiseFstN F G) (PointwiseSndN F G).
Proof.
  intros H α β. exists (PointwisePairN α β).
  split.
  - split; intros i; [apply product_β1 | apply product_β2].
  - intros γ [H1 H2] i. apply product_pair_unique.
    split; [exact (H1 i) | exact (H2 i)].
Defined.

(** Choose pointwise binary products without global instance registration. *)

(** 选定点态二元积，不进行全局实例注册。 *)

Program Definition Fct_HasProduct
  : HasProduct (Fct J C)
  :=
  {|Prod := PointwiseProductF
  ; π1 := PointwiseFstN
  ; π2 := PointwiseSndN
  ; product_universal := pointwise_product_universal
  |}.

End Pointwise.
