From Cats Require Export
  Cat.Applicative.Core.
From Cats Require Import
  Cat.Product.Transport.

Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.

(** * Binary Lifting in a Shared Context

    These equations specialize the general lax laws by pairing the inputs.
    They preserve input order and do not require exponentials or strength. *)

(** * 共同上下文中的二元提升

    这些方程通过配对输入特化一般 lax 定律。它们保持输入次序，不要求指数
    或强度。 *)

Section Lifting.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Applicative C HT HP).

(** Combine two contextual computations with an ordinary binary operation. *)

(** 用通常二元运算组合两个上下文计算。 *)

Definition applicative_combine {W X Y Z : @Ob C}
    (h : Hom (X × Y) Z) (u : Hom W (A X)) (v : Hom W (A Y))
  : Hom W (A Z)
  := @Cats.Cat.Core.comp C W (@Prod C HP (A X) (A Y)) (A Z)
    lift₂[A; h] ⟨u, v⟩.

End Lifting.

Notation "'lift₂[' A ';' h ';' u ';' v ']'" :=
  (applicative_combine A h u v) : applicative_scope.
Local Open Scope applicative_scope.

Section Laws.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Applicative C HT HP).

Local Opaque lax_lift2.

(** The operation and both computations respect specified equality. *)

(** 运算和两个计算均保持指定相等。 *)

Global Instance applicative_combine_proper {W X Y Z : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq ==> HomEq)
      (@applicative_combine C HT HP A W X Y Z).
Proof.
  intros h h' H u u' K v v' L. unfold applicative_combine.
  rewrite H, K, L. reflexivity.
Qed.

(** Context substitution acts on both inputs. *)

(** 上下文替换作用于两个输入。 *)

Lemma applicative_combine_sub {W V X Y Z : @Ob C}
    (h : Hom (X × Y) Z) (u : Hom W (A X)) (v : Hom W (A Y))
    (σ : Hom V W)
  : lift₂[A; h; u; v] ∘ σ ≈ lift₂[A; h; u ∘ σ; v ∘ σ].
Proof.
  unfold applicative_combine. rewrite comp_assoc, product_comp_r. reflexivity.
Qed.

(** An ordinary result map can be absorbed into the binary operation. *)

(** 结果上的通常映射可吸收到二元运算中。 *)

Lemma applicative_combine_post {W X Y Z T : @Ob C}
    (h : Hom (X × Y) Z) (k : Hom Z T)
    (u : Hom W (A X)) (v : Hom W (A Y))
  : fmap A k ∘ lift₂[A; h; u; v] ≈ lift₂[A; k ∘ h; u; v].
Proof.
  unfold applicative_combine. rewrite <- comp_assoc.
  apply comp_proper; [exact (lax_lift2_post A h k) | reflexivity].
Qed.

(** Ordinary maps of both inputs can be absorbed without reordering them. *)

(** 两个输入上的通常映射可被吸收，且不改变输入次序。 *)

Lemma applicative_combine_pre {W X Y X' Y' Z : @Ob C}
    (h : Hom (X' × Y') Z) (f : Hom X X') (g : Hom Y Y')
    (u : Hom W (A X)) (v : Hom W (A Y))
  : lift₂[A; h; fmap A f ∘ u; fmap A g ∘ v] ≈
      lift₂[A; h ∘ (f × g); u; v].
Proof.
  unfold applicative_combine.
  rewrite <- product_comp_l, <- comp_assoc.
  apply comp_proper; [exact (cartesian_lift2_pre A h f g) | reflexivity].
Qed.

(** Combining pure inputs gives the pure result of the original operation. *)

(** 组合纯输入，得到原运算结果的纯值。 *)

Lemma applicative_combine_pure {W X Y Z : @Ob C}
    (h : Hom (X × Y) Z) (u : Hom W X) (v : Hom W Y)
  : lift₂[A; h; pure[A; u]; pure[A; v]] ≈ pure[A; h ∘ ⟨u, v⟩].
Proof.
  unfold applicative_combine, applicative_pure_value.
  rewrite <- product_comp_l, <- !comp_assoc.
  apply comp_proper; [exact (applicative_lift2_pure A h) | reflexivity].
Qed.

(** A global pure first input reduces to ordinary partial evaluation. *)

(** 全局纯第一输入归约为通常部分求值。 *)

Lemma applicative_combine_pure_l {X Y Z : @Ob C}
    (h : Hom (X × Y) Z) (x : Hom 1 X) (g : Hom Y Z)
    (H : h ∘ (x × id) ≈ g ∘ π2) (v : Hom 1 (A Y))
  : lift₂[A; h; pure[A; x]; v] ≈ fmap A g ∘ v.
Proof.
  unfold applicative_combine, applicative_pure_value.
  transitivity ((lift₂[A; h] ∘ ((pure[A] X ∘ x) × id)) ∘ ⟨id, v⟩).
  - rewrite comp_assoc. apply comp_proper; [reflexivity |]. symmetry.
    etransitivity; [exact (product_comp_l id v (pure[A] X ∘ x) id) |].
    rewrite comp_id_l, comp_id_r. reflexivity.
  - rewrite (applicative_lift2_pure_l A h x g H), comp_assoc, product_β2.
    reflexivity.
Qed.

(** A global pure second input similarly reduces to post-evaluation. *)

(** 全局纯第二输入同样归约为后求值。 *)

Lemma applicative_combine_pure_r {X Y Z : @Ob C}
    (h : Hom (X × Y) Z) (y : Hom 1 Y) (g : Hom X Z)
    (H : h ∘ (id × y) ≈ g ∘ π1) (u : Hom 1 (A X))
  : lift₂[A; h; u; pure[A; y]] ≈ fmap A g ∘ u.
Proof.
  unfold applicative_combine, applicative_pure_value.
  transitivity ((lift₂[A; h] ∘ (id × (pure[A] Y ∘ y))) ∘ ⟨u, id⟩).
  - rewrite comp_assoc. apply comp_proper; [reflexivity |]. symmetry.
    etransitivity; [exact (product_comp_l u id id (pure[A] Y ∘ y)) |].
    rewrite comp_id_l, comp_id_r. reflexivity.
  - rewrite (applicative_lift2_pure_r A h y g H), comp_assoc, product_β1.
    reflexivity.
Qed.

(** Every ordinary associativity diagram lifts to contextual computations. *)

(** 每个通常结合图均提升为上下文计算的结合图。 *)

Lemma applicative_combine_assoc {W X Y Z U V T : @Ob C}
    (f : Hom (X × Y) U) (g : Hom (U × Z) T)
    (h : Hom (Y × Z) V) (k : Hom (X × V) T)
    (H : g ∘ (f × id) ≈ k ∘ (id × h) ∘
      (@product_assoc C HP X Y Z).1)
    (u : Hom W (A X)) (v : Hom W (A Y)) (w : Hom W (A Z))
  : lift₂[A; g; lift₂[A; f; u; v]; w] ≈
      lift₂[A; k; u; lift₂[A; h; v; w]].
Proof.
  unfold applicative_combine.
  transitivity ((lift₂[A; g] ∘ (lift₂[A; f] × id)) ∘ ⟨⟨u, v⟩, w⟩).
  - rewrite comp_assoc. apply comp_proper; [reflexivity |]. symmetry.
    etransitivity; [exact (product_comp_l ⟨u, v⟩ w lift₂[A; f] id) |].
    rewrite comp_id_l. reflexivity.
  - rewrite (cartesian_lift2_assoc A f g h k H), !comp_assoc.
    apply comp_proper; [reflexivity |].
    transitivity ((id × lift₂[A; h]) ∘ ⟨u, ⟨v, w⟩⟩).
    + apply comp_proper; [reflexivity |]. exact (product_assoc_pair u v w).
    + etransitivity; [exact (product_comp_l u ⟨v, w⟩ id lift₂[A; h]) |].
      rewrite comp_id_l. reflexivity.
Qed.

End Laws.

Local Transparent lax_lift2.
