From Cats Require Export
  Cat.Monad.Strength
  Cat.Monoidal.CartesianStrength.
From Cats Require Import
  Cat.Product.Transport.

Local Open Scope monoidal_scope.
Local Open Scope monad_scope.

(** * Binding in a Shared Cartesian Context

    Strength extends a computation without losing its ordinary context.
    The resulting laws support ordered sequencing and context substitution. *)

(** * 共同笛卡尔上下文中的绑定

    强度扩张计算而不丢失其通常上下文。所得定律支持有序组合及上下文代入。 *)

Section Context.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (M : StrongMonad C (@CartesianMonoidal C HT HP)).

(** The cartesian specialization exposes product endpoints directly.
    This keeps product rewriting independent of the chosen monoidal packaging. *)

(** 笛卡尔特化直接暴露积端点，使积重写不依赖选定幺半结构的包装。 *)

Definition context_extend {W X Y : @Ob C} (k : Hom (W × X) (M Y))
  : Hom (W × M X) (M Y)
  := strong_extend M k.

(** Contextual extension respects the continuation's equality. *)

(** 上下文扩张保持后续计算的相等。 *)

Global Instance context_extend_proper {W X Y : @Ob C}
  : Proper (HomEq ==> HomEq) (@context_extend W X Y).
Proof. exact (strong_extend_proper M). Qed.

(** Pure inputs cancel cartesian extension. *)

(** 纯输入消去笛卡尔扩张。 *)

Lemma context_extend_pure {W X Y : @Ob C} (k : Hom (W × X) (M Y))
  : context_extend k ∘ (id × η[M] X) ≈ k.
Proof.
  pose proof (strong_extend_pure M k) as H.
  rewrite cartesian_tensor_map in H. exact H.
Qed.

(** Pure continuations are ordinary maps after strength. *)

(** 纯后续计算为强度之后的通常映射。 *)

Lemma context_extend_return {W X Y : @Ob C} (k : Hom (W × X) Y)
  : context_extend (η[M] Y ∘ k) ≈
      fmap M k ∘ st[hasStrength M; W; X].
Proof. exact (strong_extend_return M k). Qed.

(** Result mapping commutes with cartesian extension. *)

(** 结果映射与笛卡尔扩张交换。 *)

Lemma context_extend_post {W X Y Z : @Ob C}
    (k : Hom (W × X) (M Y)) (f : Hom Y Z)
  : fmap M f ∘ context_extend k ≈ context_extend (fmap M f ∘ k).
Proof. exact (strong_extend_post M k f). Qed.

(** Ordinary substitution commutes with cartesian extension. *)

(** 通常代入与笛卡尔扩张交换。 *)

Lemma context_extend_pre {W W' X X' Y : @Ob C}
    (k : Hom (W' × X') (M Y)) (f : Hom W W') (g : Hom X X')
  : context_extend k ∘ (f × fmap M g) ≈
      context_extend (k ∘ (f × g)).
Proof.
  pose proof (strong_extend_pre M k f g) as H.
  rewrite !cartesian_tensor_map in H. exact H.
Qed.

(** Nested extensions reassociate their ordinary product contexts. *)

(** 嵌套扩张重排其通常积上下文的括号。 *)

Lemma context_extend_assoc {W V X Y Z : @Ob C}
    (k : Hom (V × X) (M Y)) (h : Hom (W × Y) (M Z))
  : context_extend h ∘ (id × context_extend k) ∘
      (@product_assoc C HP W V (M X)).1 ≈
      context_extend (context_extend h ∘ (id × k) ∘
        (@product_assoc C HP W V X).1).
Proof.
  pose proof (strong_extend_assoc M k h) as H.
  rewrite !cartesian_tensor_map in H. exact H.
Qed.

(** Run the first computation, then pass its result together with the
    original context to the continuation. *)

(** 先运行第一个计算，再将其结果与原上下文一同传入后续计算。 *)

Definition context_bind {W X Y : @Ob C}
    (u : Hom W (M X)) (k : Hom (W × X) (M Y))
  : Hom W (M Y)
  := context_extend k ∘ ⟨id, u⟩.

(** Binding respects equality of the computation and continuation. *)

(** 绑定保持计算及后续计算的相等。 *)

Global Instance context_bind_proper {W X Y : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq) (@context_bind W X Y).
Proof. intros u u' H k k' K. unfold context_bind. rewrite H, K. reflexivity. Qed.

(** Ordinary changes of context can be performed before either computation. *)

(** 通常上下文变换可以在两个计算之前进行。 *)

Lemma context_bind_comp {W V X Y : @Ob C}
    (u : Hom W (M X)) (k : Hom (W × X) (M Y)) (σ : Hom V W)
  : context_bind u k ∘ σ ≈
      context_bind (u ∘ σ) (k ∘ (σ × id)).
Proof.
  unfold context_bind.
  transitivity ((context_extend k ∘ (σ × fmap M (@id X))) ∘
    ⟨id, u ∘ σ⟩).
  - rewrite functor_id, !comp_assoc.
    apply comp_proper; [reflexivity |].
    transitivity ⟨σ, u ∘ σ⟩.
    + rewrite product_comp_r, comp_id_l. reflexivity.
    + rewrite product_comp_l, comp_id_l, comp_id_r. reflexivity.
  - rewrite (context_extend_pre k σ id). reflexivity.
Qed.

(** Binding a pure result substitutes it into the continuation. *)

(** 绑定纯结果，即将其代入后续计算。 *)

Lemma context_bind_pure {W X Y : @Ob C}
    (x : Hom W X) (k : Hom (W × X) (M Y))
  : context_bind (η[M] X ∘ x) k ≈ k ∘ ⟨id, x⟩.
Proof.
  unfold context_bind.
  transitivity ((context_extend k ∘ (id × η[M] X)) ∘ ⟨id, x⟩).
  - rewrite comp_assoc, product_comp_l, comp_id_l. reflexivity.
  - rewrite (context_extend_pure k). reflexivity.
Qed.

(** Returning the bound result leaves the original computation unchanged. *)

(** 返回绑定结果，保持原计算不变。 *)

Lemma context_bind_unit {W X : @Ob C} (u : Hom W (M X))
  : context_bind u (η[M] X ∘ π2) ≈ u.
Proof.
  unfold context_bind. rewrite context_extend_return,
    (cartesian_strength_projection (hasStrength M) W X), product_β2.
  reflexivity.
Qed.

(** Mapping a result commutes with binding. *)

(** 结果映射与绑定交换。 *)

Lemma context_bind_post {W X Y Z : @Ob C}
    (u : Hom W (M X)) (k : Hom (W × X) (M Y)) (f : Hom Y Z)
  : fmap M f ∘ context_bind u k ≈ context_bind u (fmap M f ∘ k).
Proof.
  unfold context_bind. rewrite <- comp_assoc, context_extend_post. reflexivity.
Qed.

(** A continuation that only maps the bound value gives ordinary [fmap]. *)

(** 仅映射绑定值的后续计算给出通常 [fmap]。 *)

Lemma context_bind_map {W X Y : @Ob C}
    (u : Hom W (M X)) (f : Hom X Y)
  : context_bind u (η[M] Y ∘ (f ∘ π2)) ≈ fmap M f ∘ u.
Proof.
  pose proof (context_bind_post u (η[M] X ∘ π2) f) as H.
  rewrite context_bind_unit, <- comp_assoc,
    <- (nt_naturality (η[M]) f), comp_assoc in H. symmetry. exact H.
Qed.

(** Mapping the bound input can be absorbed into the continuation. *)

(** 绑定输入上的映射可以吸收到后续计算中。 *)

Lemma context_bind_fmap {W X Y Z : @Ob C}
    (u : Hom W (M X)) (f : Hom X Y) (k : Hom (W × Y) (M Z))
  : context_bind (fmap M f ∘ u) k ≈
      context_bind u (k ∘ (id × f)).
Proof.
  unfold context_bind.
  transitivity ((context_extend k ∘ (id × fmap M f)) ∘ ⟨id, u⟩).
  - rewrite comp_assoc, product_comp_l, comp_id_l. reflexivity.
  - rewrite (context_extend_pre k id f). reflexivity.
Qed.

(** Returning an input substitutes it into the continuation. *)

(** 返回输入，即将它代入后续计算。 *)

Lemma context_bind_return {W X Y : @Ob C}
    (x : Hom W X) (k : Hom (W × X) (M Y))
  : context_bind (monad_return M x) k ≈ k ∘ ⟨id, x⟩.
Proof. exact (context_bind_pure x k). Qed.

(** Returning the bound value is neutral. *)

(** 返回绑定值为中性运算。 *)

Lemma context_bind_return_unit {W X : @Ob C} (u : Hom W (M X))
  : context_bind u (monad_return M π2) ≈ u.
Proof. exact (context_bind_unit u). Qed.

(** Reassociation of binding preserves the order of all computations.
    The second continuation retains the original outer context. *)

(** 绑定的括号重排保持全部计算的次序；第二个后续计算保留原外层上下文。 *)

Lemma context_bind_assoc {W X Y Z : @Ob C}
    (u : Hom W (M X)) (k : Hom (W × X) (M Y))
    (h : Hom (W × Y) (M Z))
  : context_bind (context_bind u k) h ≈
      context_bind u (context_bind k (h ∘ (π1 × id))).
Proof.
  unfold context_bind.
  transitivity ((context_extend h ∘ (id × context_extend k) ∘
    (@product_assoc C HP W W (M X)).1) ∘ ⟨⟨id, id⟩, u⟩).
  - rewrite !comp_assoc, product_assoc_pair, product_comp_l,
      !comp_id_l. reflexivity.
  - rewrite (context_extend_assoc k h).
    transitivity ((context_extend
      (context_extend h ∘ (id × k) ∘ (@product_assoc C HP W W X).1) ∘
        (⟨id, id⟩ × fmap M (@id X))) ∘ ⟨id, u⟩).
    + rewrite functor_id, !comp_assoc, product_comp_l,
        !comp_id_l, comp_id_r. reflexivity.
    + rewrite (context_extend_pre _ ⟨id, id⟩ id).
      apply comp_proper; [| reflexivity].
      apply context_extend_proper.
      transitivity (context_extend h ∘ ⟨π1, k⟩).
      * cbn. repeat first [rewrite cross_η | rewrite product_comp_r |
          rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
          rewrite comp_id_l | rewrite comp_id_r |
          rewrite product_pair_η]. reflexivity.
      * rewrite <- (context_extend_pre h π1 id), functor_id, comp_assoc,
          product_comp_l, comp_id_l, comp_id_r. reflexivity.
Qed.

(** A continuation that discards the ordinary context is plain Kleisli
    extension. This connects contextual and noncontextual sequencing. *)

(** 丢弃通常上下文的后续计算就是普通 Kleisli 扩张，关联上下文与无上下文组合。 *)

Lemma context_bind_discard {W X Y : @Ob C}
    (u : Hom W (M X)) (k : Hom X (M Y))
  : context_bind u (k ∘ π2) ≈ kleisli_extend M k ∘ u.
Proof.
  unfold context_bind, context_extend, strong_extend.
  rewrite kleisli_extend_pre,
    (comp_assoc (kleisli_extend M k) (fmap M π2)
      st[hasStrength M; W; X]),
    (cartesian_strength_projection (hasStrength M) W X),
    comp_assoc, product_β2. reflexivity.
Qed.

(** Returning an ordinary context map together with the bound value is
    strength applied to their ordinary pairing. *)

(** 将通常上下文映射与绑定值一同返回，就是将强度作用于两者的通常配对。 *)

Lemma context_bind_pair {W V X : @Ob C}
    (u : Hom W (M X)) (σ : Hom W V)
  : context_bind u (return[M; ⟨σ ∘ π1, π2⟩]) ≈
      st[hasStrength M; V; X] ∘ ⟨σ, u⟩.
Proof.
  unfold context_bind, monad_return. rewrite context_extend_return.
  transitivity ((fmap M (σ × @id X) ∘
    st[hasStrength M; W; X]) ∘ ⟨id, u⟩).
  - apply comp_proper; [| reflexivity].
    apply comp_proper; [| reflexivity].
    apply functor_fmap_proper. rewrite cross_η, comp_id_l. reflexivity.
  - pose proof (strength_natural (hasStrength M) σ (@id X)) as H.
    rewrite !cartesian_tensor_map in H.
    rewrite <- H, functor_id, comp_assoc.
    change (st[hasStrength M; V; X] ∘
      ((σ × @id (M X)) ∘ ⟨id, u⟩) ≈
      st[hasStrength M; V; X] ∘ ⟨σ, u⟩).
    rewrite product_comp_l, comp_id_r, comp_id_l. reflexivity.
Qed.

End Context.

Arguments context_bind {_ _ _} _ {_ _ _} _ _.
Notation "'bind[' M ';' u ';' k ']'" := (context_bind M u k)
  : monad_scope.

(** Normalize only by proved binding, return and product equations.
    No rule exchanges two effectful computations. *)

(** 仅用已证的绑定、返回及积方程规范化；没有规则交换两个带效应计算。 *)

Ltac monad_context_simpl M :=
  repeat match goal with
  | |- context_bind M ?u ?k ≈ context_bind M ?u ?h =>
      apply (context_bind_proper M); [reflexivity |]
  | |- monad_return ?N ?x ≈ monad_return ?N ?y =>
      apply (monad_return_proper N)
  | |- context [id ∘ ?f] => rewrite (comp_id_l f)
  | |- context [?f ∘ id] => rewrite (comp_id_r f)
  | |- context [(?f ∘ ?g) ∘ ?h] => rewrite (comp_assoc f g h)
  | |- context [π1 ∘ ⟨?f, ?g⟩] => rewrite (product_β1 f g)
  | |- context [π2 ∘ ⟨?f, ?g⟩] => rewrite (product_β2 f g)
  | |- context [π1 ∘ (⟨?f, ?g⟩ ∘ ?h)] =>
      rewrite <- (comp_assoc π1 ⟨f, g⟩ h), (product_β1 f g)
  | |- context [π2 ∘ (⟨?f, ?g⟩ ∘ ?h)] =>
      rewrite <- (comp_assoc π2 ⟨f, g⟩ h), (product_β2 f g)
  | |- context [@cross _ _ _ _ _ _ ?f ?g] => rewrite (cross_η f g)
  | |- context [⟨?f, ?g⟩ ∘ ?h] => rewrite (product_comp_r f g h)
  | |- context [⟨π1, π2⟩] => rewrite product_pair_η
  | |- context [context_bind M ?u ?k ∘ ?σ] =>
      rewrite (context_bind_comp M u k σ)
  | |- context [fmap ?F ?f ∘ context_bind M ?u ?k] =>
      rewrite (context_bind_post M u k f)
  | |- context [context_bind M (context_bind M ?u ?k) ?h] =>
      rewrite (context_bind_assoc M u k h)
  | |- context [context_bind M (monad_return ?N ?x) ?k] =>
      rewrite (context_bind_return M x k)
  | |- context [context_bind M (fmap ?F ?f ∘ ?u) ?k] =>
      rewrite (context_bind_fmap M u f k)
  | |- context [context_bind M ?u (monad_return ?N π2)] =>
      rewrite (context_bind_return_unit M u)
  | |- context [monad_return ?N ?x ∘ ?σ] =>
      rewrite (monad_return_comp N x σ)
  | |- context [fmap ?F ?f ∘ monad_return ?N ?x] =>
      rewrite (monad_return_map N f x)
  end.
