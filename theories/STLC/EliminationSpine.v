From Cats.STLC Require Export BindingMarker.

(** * Elimination Trees with an Inferred Source Type

    Fix the type of the head. Each projection or application then fixes
    the next source type, so a forward elimination tree needs no hidden
    type annotation at its nodes. Only leaves retain a family of data.
    Instantiating that family with binding markers records the displayed
    result type without comparing labels. Application arguments are raw.

    This representation is distinct from eta-long normal forms: it does
    not normalize arguments, and it retains unit-valued blocked terms. *)

(** * 从来源类型推断的消去树

    固定头部类型后，每次投影或应用都确定下一个来源类型。因此前向消去树的
    节点不需要隐藏类型注解，只有叶端保留一族数据。将该族取为绑定标记，
    可以记录显示的结果类型，而不比较标签。应用实参仍是原始项。

    此表示区别于 η 长正规形：它不正规化实参，并保留单位类型的阻塞项。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** A Tree over Each Declared Head Type

    Fix a signature and raw argument context. Leaves are small; the tree
    lives at the signature bound because it can contain raw arguments. *)

(** ** 每个声明头类型上的树

    固定签名及原始实参的上下文。叶端是小型的；树可包含原始实参，因此位于
    签名界。 *)

Section EliminationTrees.
Context {B : Type} (Γ : Ctx B).

(** The continuations permitted by a declared type. Each child can stop
    at a leaf or continue, with no dependent constructor annotation. *)

(** 声明类型所允许的后续。每个子项可在叶端停止或继续，无须依赖构造器注解。 *)

Fixpoint EliminationBranches (L : Ty B → Set) (D : Ty B)
  : Type
  := (match D with
      | ty_prod A U =>
          (L A + EliminationBranches L A) + (L U + EliminationBranches L U)
      | ty_arr A U => Tm Γ A * (L U + EliminationBranches L U)
      | _ => Empty_set
      end)%type.

(** A leaf is observable even when the head type remains abstract. *)

(** 即使头部类型仍然抽象，也可以观测叶端。 *)

Definition EliminationTree (L : Ty B → Set) (D : Ty B)
  : Type
  := (L D + EliminationBranches L D)%type.

(** Replace leaves below a continuation, keeping its first elimination. *)

(** 替换后续中的叶端，保持其第一次消去。 *)

Fixpoint elimination_branches_bind {L M : Ty B → Set}
    (f : ∀ D, L D → EliminationTree M D) (D : Ty B)
  : EliminationBranches L D → EliminationBranches M D.
Proof.
  destruct D as [b | | A U | A U]; cbn; intros node;
    try exact (match node with end).
  - destruct node as [[x | node] | [x | node]].
    + exact (inl (f A x)).
    + exact (inl (inr (elimination_branches_bind L M f A node))).
    + exact (inr (f U x)).
    + exact (inr (inr (elimination_branches_bind L M f U node))).
  - destruct node as [a [x | node]].
    + exact (a, f U x).
    + exact (a, inr (elimination_branches_bind L M f U node)).
Defined.

(** Replace every leaf. The leaf case computes at an abstract head type. *)

(** 替换每个叶端。叶端情形在抽象头类型处即可计算。 *)

Definition elimination_tree_bind {L M : Ty B → Set}
    (f : ∀ D, L D → EliminationTree M D) (D : Ty B)
    (p : EliminationTree L D)
  : EliminationTree M D
  := match p with
     | inl x => f D x
     | inr node => inr (elimination_branches_bind f D node)
     end.

(** Interpret a nonempty continuation from a supplied head. *)

(** 从给定头部解释非空后续。 *)

Fixpoint elimination_branches_fold {L : Ty B → Set} {K : Type}
    (leaf : ∀ D, L D → Tm Γ D → K) (D : Ty B)
  : EliminationBranches L D → Tm Γ D → K.
Proof.
  destruct D as [b | | A U | A U]; cbn; intros node head;
    try exact (match node with end).
  - destruct node as [[x | node] | [x | node]].
    + exact (leaf A x (π₁ head)).
    + exact (elimination_branches_fold L K leaf A node (π₁ head)).
    + exact (leaf U x (π₂ head)).
    + exact (elimination_branches_fold L K leaf U node (π₂ head)).
  - destruct node as [a [x | node]].
    + exact (leaf U x (head · a)).
    + exact (elimination_branches_fold L K leaf U node (head · a)).
Defined.

(** Interpret a whole tree. Leaves do not inspect the abstract head type. *)

(** 解释整棵树。叶端不检查抽象的头类型。 *)

Definition elimination_tree_fold {L : Ty B → Set} {K : Type}
    (leaf : ∀ D, L D → Tm Γ D → K) (D : Ty B)
    (p : EliminationTree L D) (head : Tm Γ D)
  : K
  := match p with
     | inl x => leaf D x head
     | inr node => elimination_branches_fold leaf D node head
     end.

(** A pointwise law for replacing leaves extends to the entire tree.
    No equality of leaf-action functions or argument terms is assumed. *)

(** 叶端替换的逐点定律延伸到整棵树，不假设叶端操作函数相等或实参项相等。 *)

Definition elimination_tree_bind_fold {L M : Ty B → Set} {K H : Type}
    (f : ∀ D, L D → EliminationTree M D)
    (leaf : ∀ D, L D → Tm Γ D → K)
    (next : ∀ D, M D → Tm Γ D → H) (g : K → H)
    (law : ∀ D x head, elimination_tree_fold next D (f D x) head =
      g (leaf D x head))
  : ∀ D (p : EliminationTree L D) head,
      elimination_tree_fold next D (elimination_tree_bind f D p) head =
      g (elimination_tree_fold leaf D p head).
Proof.
  induction D as [b | | A ihA U ihU | A ihA U ihU];
    intros [x | node] head.
  all: try exact (law _ x head).
  all: cbn in node; try exact (match node with end).
  - destruct node as [[x | node] | [x | node]].
    + exact (ihA (inl x) (π₁ head)).
    + exact (ihA (inr node) (π₁ head)).
    + exact (ihU (inl x) (π₂ head)).
    + exact (ihU (inr node) (π₂ head)).
  - destruct node as [a [x | node]].
    + exact (ihU (inl x) (head · a)).
    + exact (ihU (inr node) (head · a)).
Defined.

(** Result alignment occurs only at a terminal marker. *)

(** 结果对齐仅发生在终端标记处。 *)

Definition AlignedSpine (D A : Ty B)
  : Type
  := EliminationTree (λ T, NewVar T A) D.

(** Embed the aligned spine applied to its supplied head. *)

(** 嵌入应用于给定头部的对齐消去链。 *)

Definition embed_spine {D A : Ty B} (p : AlignedSpine D A) (head : Tm Γ D)
  : Tm Γ A
  := elimination_tree_fold (λ T x, marker_tm x) D p head.

(** Append a left projection at a leaf. Its hidden right marker is moved
    through the projection by the coherent marker law, not identified. *)

(** 在叶端追加左投影。隐藏的右标记由相干标记定律穿过投影，不被强行识别。 *)

Definition spine_leaf_fst {A U : Ty B} (D : Ty B)
    (x : NewVar D (A × U))
  : AlignedSpine D A.
Proof.
  destruct D as [b | | D V | D V].
  - exact (match product_marker_left (new_var_inv x) with end).
  - exact (match product_marker_left (new_var_inv x) with end).
  - exact (inr (inl (inl (new_var_inv
      (product_marker_left (new_var_inv x)))))).
  - exact (match product_marker_left (new_var_inv x) with end).
Defined.

(** Append the right projection, retaining its own component marker. *)

(** 追加右投影，保留它自己的分量标记。 *)

Definition spine_leaf_snd {A U : Ty B} (D : Ty B)
    (x : NewVar D (A × U))
  : AlignedSpine D U.
Proof.
  destruct D as [b | | D V | D V].
  - exact (match product_marker_right (new_var_inv x) with end).
  - exact (match product_marker_right (new_var_inv x) with end).
  - exact (inr (inr (inl (new_var_inv
      (product_marker_right (new_var_inv x)))))).
  - exact (match product_marker_right (new_var_inv x) with end).
Defined.

(** Append application. The argument is aligned with the declared domain
    and the displayed result retains the codomain marker. *)

(** 追加应用。实参与声明的定义域对齐，显示结果保留陪域标记。 *)

Definition spine_leaf_app {A U : Ty B} (a : Tm Γ A) (D : Ty B)
    (x : NewVar D (A ⇒ U))
  : AlignedSpine D U.
Proof.
  destruct D as [b | | D V | D V].
  - exact (match arrow_marker_domain (new_var_inv x) with end).
  - exact (match arrow_marker_domain (new_var_inv x) with end).
  - exact (match arrow_marker_domain (new_var_inv x) with end).
  - exact (inr (marker_tm (arrow_marker_domain (new_var_inv x)) a,
      inl (new_var_inv (arrow_marker_codomain (new_var_inv x))))).
Defined.

(** The new leaf embeds as the original term's left projection. *)

(** 新叶端嵌入为原项的左投影。 *)

Definition spine_leaf_fst_embed {A U : Ty B} (D : Ty B)
    (x : NewVar D (A × U)) (head : Tm Γ D)
  : embed_spine (spine_leaf_fst D x) head = π₁ (marker_tm x head).
Proof.
  destruct D as [b | | D V | D V];
    try exact (match product_marker_left (new_var_inv x) with end).
  pose proof (marker_tm_fst (new_var_inv x) head) as law.
  rewrite new_var_inv_inv in law. symmetry. exact law.
Defined.

(** The corresponding equation for the right projection. *)

(** 右投影的对应等式。 *)

Definition spine_leaf_snd_embed {A U : Ty B} (D : Ty B)
    (x : NewVar D (A × U)) (head : Tm Γ D)
  : embed_spine (spine_leaf_snd D x) head = π₂ (marker_tm x head).
Proof.
  destruct D as [b | | D V | D V];
    try exact (match product_marker_right (new_var_inv x) with end).
  pose proof (marker_tm_snd (new_var_inv x) head) as law.
  rewrite new_var_inv_inv in law. symmetry. exact law.
Defined.

(** Application respects the same leaf alignment. *)

(** 应用尊重相同的叶端对齐。 *)

Definition spine_leaf_app_embed {A U : Ty B} (a : Tm Γ A) (D : Ty B)
    (x : NewVar D (A ⇒ U)) (head : Tm Γ D)
  : embed_spine (spine_leaf_app a D x) head = marker_tm x head · a.
Proof.
  destruct D as [b | | D V | D V];
    try exact (match arrow_marker_domain (new_var_inv x) with end).
  pose proof (marker_tm_app (new_var_inv x) head a) as law.
  rewrite new_var_inv_inv in law. symmetry. exact law.
Defined.

(** Extend a complete spine by left projection. *)

(** 以左投影延伸完整消去链。 *)

Definition spine_fst {D A U : Ty B} (p : AlignedSpine D (A × U))
  : AlignedSpine D A
  := elimination_tree_bind (λ T x, spine_leaf_fst T x) D p.

(** Extend it by right projection. *)

(** 以右投影延伸消去链。 *)

Definition spine_snd {D A U : Ty B} (p : AlignedSpine D (A × U))
  : AlignedSpine D U
  := elimination_tree_bind (λ T x, spine_leaf_snd T x) D p.

(** Extend it by application to an arbitrary raw argument. *)

(** 以对任意原始实参的应用延伸消去链。 *)

Definition spine_app {D A U : Ty B} (p : AlignedSpine D (A ⇒ U))
    (a : Tm Γ A)
  : AlignedSpine D U
  := elimination_tree_bind (λ T x, spine_leaf_app a T x) D p.

(** Appending left projection recovers that exact raw constructor. *)

(** 追加左投影精确恢复该原始构造器。 *)

Definition embed_spine_fst {D A U : Ty B}
    (p : AlignedSpine D (A × U)) (head : Tm Γ D)
  : embed_spine (spine_fst p) head = π₁ (embed_spine p head)
  := elimination_tree_bind_fold _ _ _ _ spine_leaf_fst_embed D p head.

(** Appending right projection likewise recovers the original syntax. *)

(** 追加右投影同样恢复原始语法。 *)

Definition embed_spine_snd {D A U : Ty B}
    (p : AlignedSpine D (A × U)) (head : Tm Γ D)
  : embed_spine (spine_snd p) head = π₂ (embed_spine p head)
  := elimination_tree_bind_fold _ _ _ _ spine_leaf_snd_embed D p head.

(** Appending application changes only its canonical representation. *)

(** 追加应用只改变其规范表示。 *)

Definition embed_spine_app {D A U : Ty B}
    (p : AlignedSpine D (A ⇒ U)) (a : Tm Γ A) (head : Tm Γ D)
  : embed_spine (spine_app p a) head = embed_spine p head · a
  := elimination_tree_bind_fold _
      (λ T (x : NewVar T (A ⇒ U)), marker_tm x) _
      (λ f : Tm Γ (A ⇒ U), f · a) (spine_leaf_app_embed a) D p head.

End EliminationTrees.

Arguments EliminationTree {B} Γ L D.
Arguments AlignedSpine {B} Γ D A.
Arguments embed_spine {B Γ D A} _ _.
Arguments spine_fst {B Γ D A U} _.
Arguments spine_snd {B Γ D A U} _.
Arguments spine_app {B Γ D A U} _ _.
Arguments embed_spine_fst {B Γ D A U} _ _.
Arguments embed_spine_snd {B Γ D A U} _ _.
Arguments embed_spine_app {B Γ D A U} _ _ _.
