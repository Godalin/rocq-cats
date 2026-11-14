From Cats.STLC Require Export Syntax.

(** * Product Views of Typed Variables

    A variable of product type retains a context position and an indexed
    binding marker. Its two views keep the same position, while recording
    only the left or right component of that marker. Together they recover
    the original variable by native equality.

    The views do not decide equality of base labels or discard equality
    witnesses. Decomposition and reconstruction are coherent operations
    on the existing [NewVar] markers. Like [Var], these views are small
    even when the signature lives in a larger universe. *)

(** * 带类型变量的积视图

    积类型的变量保留上下文位置及带索引的绑定标记。它的两个视图保留同一
    位置，同时各记录标记的左分量或右分量。二者合起来按原生相等恢复原变量。

    这些视图不判定基标签相等，也不丢弃相等见证。分解与重构是既有 [NewVar]
    标记上的相干操作。与 [Var] 一样，即使签名位于较大宇宙，这些视图仍然小。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.

(** ** Decomposing Product Binding Markers

    Fix arbitrary base labels. Reverse a marker to read the declared
    context type, then split its product components. Rebuilding preserves
    the marker itself, rather than just the fact that a marker exists. *)

(** ** 分解积绑定标记

    固定任意基标签。反转标记以读取上下文中声明的类型，再分解积分量。
    重构保持标记本身，而非仅保持存在某个标记这一事实。 *)

Section ProductMarkers.
Context {B : Type}.

(** Reverse the two endpoint types of a binding marker. *)

(** 反转绑定标记两端的类型。 *)

Definition new_var_inv {A U : Ty B} (x : NewVar A U)
  : NewVar U A.
Proof. destruct x. exact new_var. Defined.

(** Reversing twice recovers the original marker. *)

(** 反转两次恢复原标记。 *)

Definition new_var_inv_inv {A U : Ty B} (x : NewVar A U)
  : new_var_inv (new_var_inv x) = x.
Proof. destruct x. reflexivity. Defined.

(** The left component can be aligned only with a product declaration. *)

(** 左分量只能与积类型的声明对齐。 *)

Definition ProductMarkerLeft (A T : Ty B)
  : Set
  := match T with
     | ty_prod D V => NewVar A D
     | _ => Empty_set
     end.

(** The right component retains its own binding marker. *)

(** 右分量保留它自己的绑定标记。 *)

Definition ProductMarkerRight (U T : Ty B)
  : Set
  := match T with
     | ty_prod D V => NewVar U V
     | _ => Empty_set
     end.

(** Read the left component with the target type generalized. *)

(** 泛化目标类型后读取左分量。 *)

Definition product_marker_left {A U T : Ty B}
    (x : NewVar (A × U) T)
  : ProductMarkerLeft A T.
Proof. destruct x. exact new_var. Defined.

(** Read the right component in the same way. *)

(** 以同样方式读取右分量。 *)

Definition product_marker_right {A U T : Ty B}
    (x : NewVar (A × U) T)
  : ProductMarkerRight U T.
Proof. destruct x. exact new_var. Defined.

(** Combine the two component markers into a product marker. *)

(** 将两个分量标记组合为积标记。 *)

Definition product_marker_pair {A U D V : Ty B}
    (x : NewVar A D) (y : NewVar U V)
  : NewVar (A × U) (D × V).
Proof. destruct x, y. exact new_var. Defined.

(** The left observation recovers its supplied component marker. *)

(** 左观测恢复给定的左分量标记。 *)

Definition product_marker_pair_β1 {A U D V : Ty B}
    (x : NewVar A D) (y : NewVar U V)
  : product_marker_left (product_marker_pair x y) = x.
Proof. destruct x, y. reflexivity. Defined.

(** The right observation recovers its supplied component marker. *)

(** 右观测恢复给定的右分量标记。 *)

Definition product_marker_pair_β2 {A U D V : Ty B}
    (x : NewVar A D) (y : NewVar U V)
  : product_marker_right (product_marker_pair x y) = y.
Proof. destruct x, y. reflexivity. Defined.

(** Rebuilding the observed components recovers the marker. Generalizing
    its target type keeps this law free of any uniqueness-of-proofs input. *)

(** 由观测分量重构可恢复原标记。泛化目标类型使此定律无须证明唯一性输入。 *)

Definition product_marker_pair_inv {A U T : Ty B}
    (x : NewVar (A × U) T)
  : match T as T' return NewVar (A × U) T' → Type with
    | ty_prod D V => λ x,
        product_marker_pair (product_marker_left x)
          (product_marker_right x) = x
    | _ => λ _, unit
    end x.
Proof. destruct x. reflexivity. Defined.

(** The two observations jointly identify product markers. *)

(** 两个观测联合识别积标记。 *)

Definition product_marker_projections_injective {A U D V : Ty B}
    (x y : NewVar (A × U) (D × V))
    (left : product_marker_left x = product_marker_left y)
    (right : product_marker_right x = product_marker_right y)
  : x = y.
Proof.
  rewrite <- (product_marker_pair_inv x), <- (product_marker_pair_inv y).
  rewrite left, right. reflexivity.
Defined.

End ProductMarkers.

(** ** Keeping Context Positions

    Keep the same arbitrary signature. Older positions pass through a sum
    inclusion. A newest position uses the two product-marker observations.
    The sum tags distinguish positions before the markers are compared. *)

(** ** 保持上下文位置

    保持同一任意签名。旧位置通过和类型的嵌入保留；最新位置使用两个积标记
    观测。先由和类型标签区分位置，再比较标记。 *)

Section ProductVariables.
Context {B : Type}.

(** Positions with the left component of a product declaration. *)

(** 保留积声明左分量的位置。 *)

Fixpoint LeftProductVar (Γ : Ctx B) (A : Ty B)
  : Set
  := match Γ with
     | ctx_empty => Empty_set
     | ctx_snoc Δ T => LeftProductVar Δ A + ProductMarkerLeft A T
     end.

(** Positions with the right component of the same declaration. *)

(** 保留同一声明右分量的位置。 *)

Fixpoint RightProductVar (Γ : Ctx B) (U : Ty B)
  : Set
  := match Γ with
     | ctx_empty => Empty_set
     | ctx_snoc Δ T => RightProductVar Δ U + ProductMarkerRight U T
     end.

(** Read the left view, retaining older/newest position tags. *)

(** 读取左视图，保留旧位置／最新位置标签。 *)

Fixpoint product_var_left (Γ : Ctx B) (A U : Ty B)
  : Var Γ (A × U) → LeftProductVar Γ A.
Proof.
  destruct Γ as [| Γ T]; cbn; intros x;
    [exact (match x with end) |].
  destruct x as [x | x].
  - exact (inl (product_var_left Γ A U x)).
  - exact (inr (product_marker_left (new_var_inv x))).
Defined.

Arguments product_var_left {Γ A U} _.

(** Read the right view at that same position. *)

(** 在同一位置读取右视图。 *)

Fixpoint product_var_right (Γ : Ctx B) (A U : Ty B)
  : Var Γ (A × U) → RightProductVar Γ U.
Proof.
  destruct Γ as [| Γ T]; cbn; intros x;
    [exact (match x with end) |].
  destruct x as [x | x].
  - exact (inl (product_var_right Γ A U x)).
  - exact (inr (product_marker_right (new_var_inv x))).
Defined.

Arguments product_var_right {Γ A U} _.

(** Matching positions and both component markers recover the variable.
    No label decision or equality of variable-assignment functions is used. *)

(** 相同位置及两个分量标记恢复原变量；不使用标签判定或变量赋值函数相等。 *)

Definition product_var_projections_injective {Γ : Ctx B} {A U : Ty B}
    (x y : Var Γ (A × U))
    (left : product_var_left x = product_var_left y)
    (right : product_var_right x = product_var_right y)
  : x = y.
Proof.
  induction Γ as [| Γ ih T]; cbn in *;
    [exact (match x with end) |].
  destruct x as [x | x], y as [y | y]; cbn in *;
    try discriminate left.
  - injection left as left. injection right as right.
    f_equal. exact (ih x y left right).
  - injection left as left. injection right as right.
    destruct T; cbn in left, right.
    + exact (match product_marker_left (new_var_inv x) with end).
    + exact (match product_marker_left (new_var_inv x) with end).
    + pose proof (product_marker_projections_injective
        (new_var_inv x) (new_var_inv y) left right) as same.
      pose proof (f_equal new_var_inv same) as back.
      rewrite !new_var_inv_inv in back. f_equal. exact back.
    + exact (match product_marker_left (new_var_inv x) with end).
Defined.

End ProductVariables.

Arguments product_var_left {B Γ A U} _.
Arguments product_var_right {B Γ A U} _.
