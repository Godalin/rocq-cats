From Cats Require Export
  Cat.Applicative.Core
  Cat.Exponential.InternalHom.
From Cats Require Import
  Cat.Product.Transport.

Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.

(** * Applicative Application in a Closed Base

    Lifting evaluation defines application. Pure values and the four
    classical laws use designated hom equality. A shared context is
    allowed; fixed ordinary functions and arguments are global values
    pulled into that context. No strength of an arbitrary functor is assumed. *)

(** * 闭基底中的 Applicative 应用

    提升求值得到应用，纯值及四条经典定律使用指定 Hom 相等。允许共同上下文；
    固定的通常函数及参数是拉入该上下文的全局值。不假定任意函子具有强度。 *)

Section Application.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} (A : Applicative C HT HP).

(** Apply an effectful internal function to an effectful argument. *)

(** 将带效应的内部函数应用于带效应的参数。 *)

Definition applicative_ap {X Y : @Ob C}
  : Hom (A (Y ^ X) × A X) (A Y)
  := lift₂[A; (eval (X := X) (Y := Y))].

(** Application with both inputs in one context. *)

(** 两个输入位于同一上下文中的应用。 *)

Definition applicative_apply {W X Y : @Ob C}
    (u : Hom W (A (Y ^ X))) (v : Hom W (A X))
  : Hom W (A Y)
  := applicative_ap ∘ ⟨u, v⟩.

End Application.

Arguments applicative_ap {_ _ _ _} _ {_ _}.
Arguments applicative_apply {_ _ _ _} _ {_ _ _} _ _.

Notation "'ap[' A ']'" := (applicative_ap A) : applicative_scope.
Notation "u '⋆[' A ']' v" := (applicative_apply A u v)
  (at level 40, left associativity) : applicative_scope.

Section Laws.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} (A : Applicative C HT HP).

(** Application is respectful in both contextual inputs. *)

(** 应用对两个上下文输入均保持相等。 *)

Global Instance applicative_apply_proper {W X Y : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq)
      (@applicative_apply C HT HP HE A W X Y).
Proof. intros u u' H v v' K. unfold applicative_apply. rewrite H, K. reflexivity. Qed.

(** Application commutes with changing the shared context. *)

(** 应用与共同上下文的变换交换。 *)

Lemma applicative_apply_comp {W V X Y : @Ob C}
    (u : Hom W (A (Y ^ X))) (v : Hom W (A X)) (σ : Hom V W)
  : (u ⋆[A] v) ∘ σ ≈ (u ∘ σ) ⋆[A] (v ∘ σ).
Proof. unfold applicative_apply. rewrite comp_assoc, product_comp_r. reflexivity. Qed.

(** Homomorphism: application of two pure values is pure ordinary application. *)

(** 同态律：两个纯值的应用，就是通常应用的纯值。 *)

Lemma applicative_homomorphism {W X Y : @Ob C}
    (f : Hom W (Y ^ X)) (x : Hom W X)
  : pure[A; f] ⋆[A] pure[A; x] ≈ pure[A; app f x].
Proof.
  unfold applicative_apply, applicative_ap, applicative_pure_value.
  transitivity ((lift₂[A; (eval (X := X) (Y := Y))] ∘
    (pure[A] (Y ^ X) × pure[A] X)) ∘ ⟨f, x⟩).
  - rewrite !comp_assoc,
      (product_comp_l f x (pure[A] (Y ^ X)) (pure[A] X)). reflexivity.
  - rewrite (applicative_lift2_pure A (eval (X := X) (Y := Y))).
    unfold app. apply comp_assoc.
Qed.

(** Applying a fixed pure function agrees with the ordinary functor action. *)

(** 应用固定纯函数，与通常函子作用相同。 *)

Lemma applicative_pure_map {W X Y : @Ob C}
    (f : Hom X Y) (u : Hom W (A X))
  : pure[A; (ƛ (f ∘ π2) : Hom 1 (Y ^ X)) ∘ !] ⋆[A] u ≈
      fmap A f ∘ u.
Proof.
  unfold applicative_apply, applicative_ap, applicative_pure_value.
  transitivity ((lift₂[A; (eval (X := X) (Y := Y))] ∘
    ((pure[A] (Y ^ X) ∘ (ƛ (f ∘ π2))) × id)) ∘ ⟨!, u⟩).
  - rewrite !comp_assoc. apply comp_proper; [reflexivity |].
    symmetry. etransitivity.
    + exact (product_comp_l (! : Hom W 1) u
        (pure[A] (Y ^ X) ∘ (ƛ (f ∘ π2) : Hom 1 (Y ^ X))) id).
    + rewrite comp_id_l, comp_assoc. reflexivity.
  - rewrite (applicative_lift2_pure_l A (eval (X := X) (Y := Y))
      (ƛ (f ∘ π2)) f (exponential_β (f ∘ π2))).
    rewrite comp_assoc, product_β2. reflexivity.
Qed.

(** Identity: the pure internal identity leaves every effectful value alone. *)

(** 恒等律：纯内部恒等函数保持每个带效应值。 *)

Lemma applicative_identity {W X : @Ob C} (u : Hom W (A X))
  : pure[A; (idᴱ[X] : Hom W (X ^ X))] ⋆[A] u ≈ u.
Proof.
  pose proof (applicative_pure_map (@id X) u) as H.
  unfold applicative_pure_value in *.
  rewrite comp_id_l in H.
  change ((pure[A] (X ^ X) ∘ (idᴱ[X] ∘ !)) ⋆[A] u ≈
    fmap A (@id X) ∘ u) in H.
  rewrite exponential_id_comp, functor_id, comp_id_l in H. exact H.
Qed.

(** Interchange: a fixed pure argument can be applied after mapping
    evaluation at that argument over the effectful function. *)

(** 交换律：固定纯参数的应用，可通过对带效应函数映射该参数处的求值获得。 *)

Lemma applicative_interchange_map {W X Y : @Ob C}
    (u : Hom W (A (Y ^ X))) (y : Hom 1 X)
  : u ⋆[A] pure[A; y ∘ !] ≈ fmap A (app id (y ∘ !)) ∘ u.
Proof.
  assert (H : (eval (X := X) (Y := Y)) ∘ (id × y) ≈
      app id (y ∘ !) ∘ π1).
  { unfold app. rewrite comp_assoc, product_comp_r, comp_id_l.
    rewrite cross_η, comp_id_l, comp_assoc.
    rewrite (term_η (! ∘ π1)),
      (term_η (π2 : Hom ((Y ^ X) × 1) 1)). reflexivity. }
  unfold applicative_apply, applicative_ap, applicative_pure_value.
  transitivity ((lift₂[A; (eval (X := X) (Y := Y))] ∘
    (id × (pure[A] X ∘ y))) ∘ ⟨u, !⟩).
  - rewrite !comp_assoc. apply comp_proper; [reflexivity |].
    symmetry. etransitivity.
    + exact (product_comp_l u (! : Hom W 1) id (pure[A] X ∘ y)).
    + rewrite comp_id_l, comp_assoc. reflexivity.
  - rewrite (applicative_lift2_pure_r A _ y _ H).
    rewrite comp_assoc, product_β1. reflexivity.
Qed.

(** The classical interchange equation names the ordinary evaluation map
    as a pure function, rather than using [fmap] in the result. *)

(** 经典交换方程将通常求值映射命名为纯函数，结果中使用应用运算。 *)

Lemma applicative_interchange {W X Y : @Ob C}
    (u : Hom W (A (Y ^ X))) (y : Hom 1 X)
  : u ⋆[A] pure[A; y ∘ !] ≈
      pure[A; (ƛ (app id (y ∘ !) ∘ π2) : Hom 1 (Y ^ (Y ^ X))) ∘ !]
        ⋆[A] u.
Proof.
  rewrite applicative_interchange_map, applicative_pure_map. reflexivity.
Qed.

(** Mapping an ordinary function into the effectful function input can
    be absorbed into the lifted evaluation. *)

(** 对带效应函数输入映射通常函数，可以吸收到提升后的求值中。 *)

Lemma applicative_apply_fmap {W X Y Z : @Ob C}
    (f : Hom X (Z ^ Y)) (u : Hom W (A X)) (v : Hom W (A Y))
  : (fmap A f ∘ u) ⋆[A] v ≈
      lift₂[A; (eval (X := Y) (Y := Z)) ∘ (f × id)] ∘ ⟨u, v⟩.
Proof.
  unfold applicative_apply, applicative_ap.
  transitivity ((lift₂[A; (eval (X := Y) (Y := Z))] ∘
    (fmap A f × fmap A (@id Y))) ∘ ⟨u, v⟩).
  - rewrite !comp_assoc. apply comp_proper; [reflexivity |].
    symmetry. etransitivity.
    + exact (product_comp_l u v (fmap A f) (fmap A (@id Y))).
    + rewrite functor_id, comp_id_l. reflexivity.
  - apply comp_proper; [| reflexivity].
    exact (cartesian_lift2_pre A (eval (X := Y) (Y := Z)) f (@id Y)).
Qed.

(** The uncurried composition equation is a lifted evaluation diagram.
    It follows directly from generic lax preservation of associativity. *)

(** 未柯里化的复合方程是提升后的求值图，直接来自一般 lax 结合图保持性。 *)

Lemma applicative_composition_eval {W X Y Z : @Ob C}
    (u : Hom W (A (Z ^ Y))) (v : Hom W (A (Y ^ X)))
    (w : Hom W (A X))
  : (lift₂[A; internal_comp X Y Z] ∘ ⟨u, v⟩) ⋆[A] w ≈
      u ⋆[A] (v ⋆[A] w).
Proof.
  unfold applicative_apply, applicative_ap.
  transitivity ((lift₂[A; (eval (X := X) (Y := Z))] ∘
    (lift₂[A; internal_comp X Y Z] × id)) ∘ ⟨⟨u, v⟩, w⟩).
  - rewrite !comp_assoc. apply comp_proper; [reflexivity |].
    symmetry. etransitivity.
    + exact (product_comp_l ⟨u, v⟩ w (lift₂[A; internal_comp X Y Z]) id).
    + rewrite comp_id_l. reflexivity.
  - transitivity ((lift₂[A; (eval (X := Y) (Y := Z))] ∘
      (id × lift₂[A; (eval (X := X) (Y := Y))]) ∘
      (@product_assoc C HP (A (Z ^ Y)) (A (Y ^ X)) (A X)).1) ∘
      ⟨⟨u, v⟩, w⟩).
    + apply comp_proper; [| reflexivity].
      exact (cartesian_lift2_assoc A (internal_comp X Y Z)
        (eval (X := X) (Y := Z)) (eval (X := X) (Y := Y))
        (eval (X := Y) (Y := Z)) (internal_comp_eval X Y Z)).
    + rewrite !comp_assoc, (product_assoc_pair u v w).
      rewrite (product_comp_l u ⟨v, w⟩ id
        (lift₂[A; (eval (X := X) (Y := Y))])), comp_id_l.
      reflexivity.
Qed.

(** Composition: the pure curried composition function followed by three
    applications agrees with two successive effectful applications. *)

(** 复合律：纯柯里化复合函数连续应用三次，等于两次连续的带效应应用。 *)

Lemma applicative_composition {W X Y Z : @Ob C}
    (u : Hom W (A (Z ^ Y))) (v : Hom W (A (Y ^ X)))
    (w : Hom W (A X))
  : ((pure[A; (ƛ ((ƛ (internal_comp X Y Z)) ∘ π2)
        : Hom 1 (((Z ^ X) ^ (Y ^ X)) ^ (Z ^ Y))) ∘ !]
      ⋆[A] u) ⋆[A] v) ⋆[A] w ≈ u ⋆[A] (v ⋆[A] w).
Proof.
  rewrite applicative_pure_map, applicative_apply_fmap.
  change ((lift₂[A; uncurry (ƛ (internal_comp X Y Z))] ∘ ⟨u, v⟩)
    ⋆[A] w ≈ u ⋆[A] (v ⋆[A] w)).
  rewrite (exponential_β (internal_comp X Y Z)).
  apply applicative_composition_eval.
Qed.

End Laws.
