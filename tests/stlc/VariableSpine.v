From Cats.STLC Require Import VariableSpine.

(** * Inferred Elimination-Spine Interfaces

    Check small markers, signature-sized raw views, independent fold
    result bounds and native reconstruction at abstract component types.
    Raw argument redexes and unit-valued blocked heads must survive. *)

(** * 推断消去链接口

    检查小型标记、签名大小的原始视图、独立的折叠结果界，以及抽象分量类型
    处的原生重构。实参可归约式和单位类型的阻塞头必须保留。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** A Large Signature and Small Leaf Data

    Fix [Set < b]. Stored raw arguments may use [b], while binding
    markers and a fold's output can remain small. *)

(** ** 大签名与小型叶端数据

    固定 [Set < b]。存储的原始实参可使用 [b]，绑定标记及折叠输出可以保持
    小型。 *)

Section LargeSignature.
Universe b.
Constraint Set < b.
Context {B : Type@{b}} {Γ Δ : Ctx B} {D A : Ty B}.

(** A view fits the original syntax bound, without raising it. *)

(** 视图位于原语法界，无须将其提升。 *)

Definition signature_sized_view
  : Type@{b}
  := VariableSpine Γ Δ A.

(** Folding to a small value does not identify the signature with [Set]. *)

(** 折叠到小型值不会将签名界识别为 [Set]。 *)

Definition small_fold_result (p : AlignedSpine Γ D A) (head : Tm Γ D)
  : nat
  := elimination_tree_fold Γ (λ _ _ _, 0) D p head.

End LargeSignature.

(** ** Independent Fold Targets

    Fix [b < k]. A fold can also compute in a larger target, independently
    of both its small leaf witnesses and signature-sized tree. *)

(** ** 独立的折叠目标

    固定 [b < k]。折叠也可计算较大目标，独立于小型叶端见证和签名大小的树。 *)

Section LargeFoldTarget.
Universes b k.
Constraint b < k.
Context {B : Type@{b}} {Γ : Ctx B} {D A : Ty B}.
Context {K : Type@{k}} (value : K).

(** The output level need not equal the raw-term level. *)

(** 输出层级不必等于原始项层级。 *)

Definition large_fold_result (p : AlignedSpine Γ D A) (head : Tm Γ D)
  : K
  := elimination_tree_fold Γ (λ _ _ _, value) D p head.

End LargeFoldTarget.

(** ** Raw Reconstruction at Abstract Types

    Keep the signature, contexts, component types and raw arguments
    abstract. Context positions and head declarations are displayed,
    so the view and its embedding must compute without label decisions. *)

(** ** 抽象类型处的原始重构

    保持签名、上下文、分量类型及原始实参抽象。显示上下文位置与头部声明，
    使视图及其嵌入无须标签判定即可计算。 *)

Section Computation.
Context {B : Type} {Γ : Ctx B} {A U V : Ty B}.

(** A variable function applied to a redex is still a blocked head. *)

(** 变量函数应用于可归约式后，头部仍被阻塞。 *)

Definition blocked_raw_argument (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : Tm (Γ ▻ (V ⇒ (A × U))) (A × U)
  := (# var_zero) · ((ƛ (# var_zero)) · a).

(** The view retains the redex as the canonical-domain argument. *)

(** 视图将该可归约式保留为声明定义域处的实参。 *)

Definition blocked_raw_argument_view (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : variable_spine_view (blocked_raw_argument a) =
      Some (inr (inr (((ƛ (# var_zero)) · a), inl new_var))).
Proof. reflexivity. Defined.

(** Re-embedding the explicit view reconstructs the original application. *)

(** 嵌回显式视图重构原应用。 *)

Definition blocked_raw_argument_embeds (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : @embed_variable_view B (Γ ▻ (V ⇒ (A × U))) (A × U)
      (inr (inr (((ƛ (# var_zero)) · a), inl new_var))) =
      blocked_raw_argument a.
Proof. reflexivity. Defined.

(** The terminal classifier finds that same view without reducing [a]. *)

(** 终止分类器找到同一视图，不归约 [a]。 *)

Definition blocked_raw_argument_classifies
    (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : projT1 (head_terminal_product_spine (blocked_raw_argument a)
      eq_refl eq_refl) =
      inr (inr (((ƛ (# var_zero)) · a), inl new_var)).
Proof. reflexivity. Defined.

(** A nested projection records the declared product branches. *)

(** 嵌套投影记录声明的积类型分支。 *)

Definition nested_projection_view
  : variable_spine_view
      (π₂ (π₁ (# (@var_zero B Γ ((V × (A × U)) × V))))) =
      Some (inr (inr (inl (inr (inr (inl new_var)))))).
Proof. reflexivity. Defined.

(** An older variable keeps its position even beside an equal declaration. *)

(** 旧变量即使位于相同类型的声明旁，也保留自己的位置。 *)

Definition older_function_view (a : Tm (Γ ▻ (V ⇒ A) ▻ (V ⇒ A)) V)
  : variable_spine_view ((# (var_succ var_zero)) · a) =
      Some (inl (inr (inr (a, inl new_var)))).
Proof. reflexivity. Defined.

(** Unit-valued blocked applications remain applications. *)

(** 单位类型的阻塞应用仍然是应用。 *)

Definition unit_blocked_view (a : Tm (Γ ▻ (V ⇒ ⊤)) V)
  : variable_spine_view ((# var_zero) · a) =
      Some (inr (inr (a, inl new_var))).
Proof. reflexivity. Defined.

(** Pair introductions have no variable-headed spine, regardless of
    whether their components happen to be blocked. *)

(** 配对引入没有变量头消去链，无论其分量是否被阻塞。 *)

Definition pair_has_no_spine (a : Tm Γ A) (u : Tm Γ U)
  : variable_spine_view (⟨a, u⟩) = None.
Proof. reflexivity. Defined.

End Computation.
