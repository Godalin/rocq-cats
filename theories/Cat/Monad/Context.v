From Cats Require Export
  Cat.Monad.Strength
  Cat.Monoidal.Cartesian.
From Cats Require Import
  Cat.Product.Transport.

Local Open Scope monoidal_scope.
Local Open Scope monad_scope.

(** * Binding in a Shared Cartesian Context

    Strength extends a computation without losing its ordinary context.
    The resulting laws support ordered sequencing and context substitution. *)

(** * 共同笛卡尔上下文中的绑定

    强度扩张计算而不丢失其通常上下文。所得定律支持有序组合及上下文代入。 *)

Section ContextualBind.
Context {C : Cat}
    `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (M : StrongMonad C).

(** The cartesian specialization exposes product endpoints directly.
    This keeps product rewriting independent of the chosen monoidal packaging. *)

(** 笛卡尔特化直接暴露积端点，使积重写不依赖选定幺半结构的包装。 *)

Definition context_extend {W X Y : C}
    (k : Hom (W × X) (M Y))
  : Hom (W × M X) (M Y)
  := strong_extend M k.

(** Contextual extension respects the continuation's equality. *)

(** 上下文扩张保持后续计算的相等。 *)

Global Instance context_extend_proper {W X Y : C}
  : Proper (HomEq ==> HomEq) (@context_extend W X Y).
Proof. exact (strong_extend_proper M). Qed.

(** Pure inputs cancel cartesian extension. *)

(** 纯输入消去笛卡尔扩张。 *)

Lemma context_extend_pure {W X Y : C}
    (k : Hom (W × X) (M Y))
  : context_extend k ∘ (id × η[M] X) ≈ k.
Proof.
  pose proof (strong_extend_pure M k) as H.
  rewrite cartesian_tensor_map in H. exact H.
Qed.

(** Pure continuations are ordinary maps after strength. *)

(** 纯后续计算为强度之后的通常映射。 *)

Lemma context_extend_return {W X Y : C}
    (k : Hom (W × X) Y)
  : context_extend (η[M] Y ∘ k)
    ≈ fmap M k ∘ st[W; X].
Proof. exact (strong_extend_return M k). Qed.

(** Result mapping commutes with cartesian extension. *)

(** 结果映射与笛卡尔扩张交换。 *)

Lemma context_extend_post {W X Y Z : C}
    (k : Hom (W × X) (M Y)) (f : Hom Y Z)
  : fmap M f ∘ context_extend k
    ≈ context_extend (fmap M f ∘ k).
Proof. exact (strong_extend_post M k f). Qed.

(** Ordinary substitution commutes with cartesian extension. *)

(** 通常代入与笛卡尔扩张交换。 *)

Lemma context_extend_pre {W W' X X' Y : C}
    (k : Hom (W' × X') (M Y))
    (f : Hom W W') (g : Hom X X')
  : context_extend k ∘ (f × fmap M g)
    ≈ context_extend (k ∘ (f × g)).
Proof.
  pose proof (strong_extend_pre M k f g) as H.
  rewrite !cartesian_tensor_map in H. exact H.
Qed.

(** Nested extensions reassociate their ordinary product contexts. *)

(** 嵌套扩张重排其通常积上下文的括号。 *)

Lemma context_extend_assoc {W V X Y Z : C}
    (k : Hom (V × X) (M Y))
    (h : Hom (W × Y) (M Z))
  : context_extend h ∘ (id × context_extend k)
      ∘ product_assoc.1
    ≈ context_extend (context_extend h ∘ (id × k)
      ∘ product_assoc.1).
Proof.
  pose proof (strong_extend_assoc M k h) as H.
  rewrite !cartesian_tensor_map in H. exact H.
Qed.

(** Run the first computation, then pass its result together with the
    original context to the continuation. *)

(** 先运行第一个计算，再将其结果与原上下文一同传入后续计算。 *)

Definition context_bind {W X Y : C}
    (u : Hom W (M X)) (k : Hom (W × X) (M Y))
  : Hom W (M Y)
  := context_extend k ∘ ⟨id, u⟩.

(** Binding respects equality of the computation and continuation. *)

(** 绑定保持计算及后续计算的相等。 *)

Global Instance context_bind_proper {W X Y : C}
  : Proper (HomEq ==> HomEq ==> HomEq)
      (@context_bind W X Y).
Proof.
  intros u u' H k k' K. unfold context_bind.
  rewrite H, K. reflexivity.
Qed.

(** Ordinary changes of context can be performed before either computation. *)

(** 通常上下文变换可以在两个计算之前进行。 *)

Lemma context_bind_comp {W V X Y : C}
    (u : Hom W (M X)) (k : Hom (W × X) (M Y))
    (σ : Hom V W)
  : context_bind u k ∘ σ
    ≈ context_bind (u ∘ σ) (k ∘ (σ × id)).
Proof.
  unfold context_bind.
  transitivity ((context_extend k ∘ (σ × fmap M (id[X])))
    ∘ ⟨id, u ∘ σ⟩).
  - rewrite fmap_id, !comp_assoc.
    apply comp_proper; [reflexivity |].
    transitivity ⟨σ, u ∘ σ⟩.
    + rewrite product_comp_r, comp_id_l. reflexivity.
    + rewrite product_comp_l, comp_id_l, comp_id_r. reflexivity.
  - rewrite (context_extend_pre k σ id). reflexivity.
Qed.

(** Binding a pure result substitutes it into the continuation. *)

(** 绑定纯结果，即将其代入后续计算。 *)

Lemma context_bind_pure {W X Y : C}
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

Lemma context_bind_unit {W X : C}
    (u : Hom W (M X))
  : context_bind u (η[M] X ∘ π2) ≈ u.
Proof.
  unfold context_bind. rewrite context_extend_return,
    (cartesian_strength_projection (hasStrength M) W X), product_β2.
  reflexivity.
Qed.

(** Mapping a result commutes with binding. *)

(** 结果映射与绑定交换。 *)

Lemma context_bind_post {W X Y Z : C}
    (u : Hom W (M X)) (k : Hom (W × X) (M Y))
    (f : Hom Y Z)
  : fmap M f ∘ context_bind u k
    ≈ context_bind u (fmap M f ∘ k).
Proof.
  unfold context_bind.
  rewrite <- comp_assoc, context_extend_post.
  reflexivity.
Qed.

(** A continuation that only maps the bound value gives ordinary [fmap]. *)

(** 仅映射绑定值的后续计算给出通常 [fmap]。 *)

Lemma context_bind_map {W X Y : C}
    (u : Hom W (M X)) (f : Hom X Y)
  : context_bind u (η[M] Y ∘ (f ∘ π2))
    ≈ fmap M f ∘ u.
Proof.
  pose proof (context_bind_post u (η[M] X ∘ π2) f) as H.
  rewrite context_bind_unit, <- comp_assoc,
    <- (nat_naturality (η[M]) f), comp_assoc in H.
  symmetry. exact H.
Qed.

(** Mapping the bound input can be absorbed into the continuation. *)

(** 绑定输入上的映射可以吸收到后续计算中。 *)

Lemma context_bind_fmap {W X Y Z : C}
    (u : Hom W (M X)) (f : Hom X Y)
    (k : Hom (W × Y) (M Z))
  : context_bind (fmap M f ∘ u) k
    ≈ context_bind u (k ∘ (id × f)).
Proof.
  unfold context_bind.
  transitivity ((context_extend k ∘ (id × fmap M f)) ∘ ⟨id, u⟩).
  - rewrite comp_assoc, product_comp_l, comp_id_l. reflexivity.
  - rewrite (context_extend_pre k id f). reflexivity.
Qed.

(** Returning an input substitutes it into the continuation. *)

(** 返回输入，即将它代入后续计算。 *)

Lemma context_bind_return {W X Y : C}
    (x : Hom W X) (k : Hom (W × X) (M Y))
  : context_bind (monad_return M x) k
    ≈ k ∘ ⟨id, x⟩.
Proof. exact (context_bind_pure x k). Qed.

(** Returning the bound value is neutral. *)

(** 返回绑定值为中性运算。 *)

Lemma context_bind_return_unit {W X : C}
    (u : Hom W (M X))
  : context_bind u (monad_return M π2) ≈ u.
Proof. exact (context_bind_unit u). Qed.

(** Reassociation of binding preserves the order of all computations.
    The second continuation retains the original outer context. *)

(** 绑定的括号重排保持全部计算的次序；第二个后续计算保留原外层上下文。 *)

Lemma context_bind_assoc {W X Y Z : C}
    (u : Hom W (M X)) (k : Hom (W × X) (M Y))
    (h : Hom (W × Y) (M Z))
  : context_bind (context_bind u k) h
    ≈ context_bind u (context_bind k (h ∘ (π1 × id))).
Proof.
  unfold context_bind.
  transitivity ((context_extend h ∘ (id × context_extend k)
    ∘ product_assoc.1) ∘ ⟨⟨id, id⟩, u⟩).
  - rewrite !comp_assoc, product_assoc_pair, product_comp_l,
      !comp_id_l. reflexivity.
  - rewrite (context_extend_assoc k h).
    transitivity ((context_extend
      (context_extend h ∘ (id × k) ∘ product_assoc.1)
      ∘ (⟨id, id⟩ × fmap M (id[X]))) ∘ ⟨id, u⟩).
    + rewrite fmap_id, !comp_assoc, product_comp_l,
        !comp_id_l, comp_id_r. reflexivity.
    + rewrite (context_extend_pre _ ⟨id, id⟩ id).
      apply comp_proper; [| reflexivity].
      apply context_extend_proper.
      transitivity (context_extend h ∘ ⟨π1, k⟩).
      * cbn. repeat first [rewrite cross_η | rewrite product_comp_r |
          rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
          rewrite comp_id_l | rewrite comp_id_r |
          rewrite product_pair_η]. reflexivity.
      * rewrite <- (context_extend_pre h π1 id), fmap_id, comp_assoc,
          product_comp_l, comp_id_l, comp_id_r. reflexivity.
Qed.

(** A continuation that discards the ordinary context is plain Kleisli
    extension. This connects contextual and noncontextual sequencing. *)

(** 丢弃通常上下文的后续计算就是普通 Kleisli 扩张，关联上下文与无上下文组合。 *)

Lemma context_bind_discard {W X Y : C}
    (u : Hom W (M X)) (k : Hom X (M Y))
  : context_bind u (k ∘ π2) ≈ kleisli_extend M k ∘ u.
Proof.
  unfold context_bind, context_extend, strong_extend.
  rewrite kleisli_extend_pre,
    (comp_assoc (kleisli_extend M k) _ _),
    (cartesian_strength_projection (hasStrength M) W X),
    comp_assoc, product_β2. reflexivity.
Qed.

(** Returning an ordinary context map together with the bound value is
    strength applied to their ordinary pairing. *)

(** 将通常上下文映射与绑定值一同返回，就是将强度作用于两者的通常配对。 *)

Lemma context_bind_pair {W V X : C}
    (u : Hom W (M X)) (σ : Hom W V)
  : context_bind u (return[M; ⟨σ ∘ π1, π2⟩])
    ≈ st[V; X] ∘ ⟨σ, u⟩.
Proof.
  unfold context_bind, monad_return. rewrite context_extend_return.
  transitivity ((fmap M (σ × id[X]) ∘ st[W; X]) ∘ ⟨id, u⟩).
  - apply comp_proper; [| reflexivity].
    apply comp_proper; [| reflexivity].
    apply fmap_proper. rewrite cross_η, comp_id_l. reflexivity.
  - pose proof (strength_natural (F := M) σ (id[X])) as H.
    rewrite !cartesian_tensor_map in H.
    rewrite <- H, fmap_id, comp_assoc.
    change (st[V; X] ∘ ((σ × id[M X]) ∘ ⟨id, u⟩)
      ≈ st[V; X] ∘ ⟨σ, u⟩).
    rewrite product_comp_l, comp_id_r, comp_id_l. reflexivity.
Qed.

End ContextualBind.

Arguments context_bind {_ _ _} _ {_ _ _} _ _.
Notation "'bind[' M ';' u ';' k ']'" := (context_bind M u k)
  (at level 0, format "bind[ M ;  u ;  k ]")
  : monad_scope.

(** Match one equation at the root of a morphism. The bind laws preserve
    the order of effectful computations. *)

(** 为态射的最外层运算匹配一个方程。绑定定律保持带效应计算的次序。 *)

Ltac monad_context_law M t :=
  lazymatch t with
  | id ∘ ?f => constr:(comp_id_l f)
  | ?f ∘ id => constr:(comp_id_r f)
  | (?f ∘ ?g) ∘ ?h => constr:(comp_assoc f g h)
  | π1 ∘ ⟨?f, ?g⟩ => constr:(product_β1 f g)
  | π2 ∘ ⟨?f, ?g⟩ => constr:(product_β2 f g)
  | ⟨?f, ?g⟩ ∘ ?h => constr:(product_comp_r f g h)
  | @cross _ _ _ _ _ _ ?f ?g => constr:(cross_η f g)
  | ⟨π1, π2⟩ => constr:(product_pair_η : t ≈ _)
  | context_bind M ?u ?k ∘ ?s => constr:(context_bind_comp M u k s)
  | fmap ?F ?f ∘ context_bind M ?u ?k => constr:(context_bind_post M u k f)
  | context_bind M (context_bind M ?u ?k) ?h =>
      constr:(context_bind_assoc M u k h)
  | context_bind M (monad_return ?N ?x) ?k =>
      constr:(context_bind_return M x k)
  | context_bind M (fmap ?F ?f ∘ ?u) ?k =>
      constr:(context_bind_fmap M u f k)
  | context_bind M ?u (monad_return ?N π2) =>
      constr:(context_bind_return_unit M u)
  | monad_return ?N ?x ∘ ?s => constr:(monad_return_comp N x s)
  | fmap ?F ?f ∘ monad_return ?N ?x => constr:(monad_return_map N f x)
  end.

(** Simplify the operands using their congruence laws, then simplify the
    result. Each step constructs its equality at the subterm it changes. *)

(** 先用相容性定律化简各操作数，再化简结果。每一步都在所改动的子项处构造等式。 *)

Ltac monad_context_normalize law M :=
  lazymatch goal with
  | |- ?term ≈ _ =>
    etransitivity;
    [ lazymatch term with
      | ?f ∘ ?g =>
          refine (comp_proper f _ _ g _ _); monad_context_normalize law M
      | ⟨?f, ?g⟩ =>
          refine (product_pair_proper f _ _ g _ _); monad_context_normalize law M
      | context_bind M ?u ?k =>
          refine (context_bind_proper M u _ _ k _ _); monad_context_normalize law M
      | monad_return ?N ?x =>
          refine (monad_return_proper N x _ _); monad_context_normalize law M
      | _ => reflexivity
      end
    | lazymatch goal with
      | |- ?t ≈ _ =>
        first [ let H := law M t in
                etransitivity; [exact H | monad_context_normalize law M]
              | reflexivity ]
      end ]
  end.

(** Normalize both sides and leave their comparison as the goal.
    A caller can extend [monad_context_law] with equations for its operations. *)

(** 分别规范化两边，将两者的比较保留为目标。调用方可为自己的运算补充
    [monad_context_law] 使用的方程。 *)

Ltac monad_context_simpl_with law M :=
  etransitivity; [monad_context_normalize law M |];
  symmetry; etransitivity; [monad_context_normalize law M |]; symmetry.

(** If the two sides still differ, use setoid rewriting under other
    respectful maps and reduce matching binds or returns by congruence. *)

(** 若两边仍有差异，则在其他尊重等价的映射下重写，并用相容性消去两边共有的
    绑定或返回。 *)

Ltac monad_context_simpl M :=
  try lazymatch goal with
      | |- _ ≈ _ => monad_context_simpl_with monad_context_law M
      end;
  first
    [ lazymatch goal with |- ?x ≈ ?y => constr_eq x y end
    | repeat match goal with
      | |- context_bind M ?u _ ≈ context_bind M ?u _ =>
          apply (context_bind_proper M); [reflexivity |]
      | |- monad_return ?N _ ≈ monad_return ?N _ =>
          apply (monad_return_proper N)
      | |- context [?t] =>
          let H := monad_context_law M t in progress rewrite H
      end ].
