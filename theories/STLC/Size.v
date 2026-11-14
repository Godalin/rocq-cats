From Cats.STLC Require Export Renaming.

(** * Structural Term Size

    Count syntax nodes, independently of the sizes of type labels and
    contexts. This measure is preserved by every renaming, including
    variable identification, since renaming leaves constructors intact.
    It will measure eta contraction, not beta contraction: substitution
    in a beta contractum may duplicate its argument. *)

(** * 项的结构大小

    计算语法节点数，不依赖类型标签和上下文的大小。每个重命名都保持此度量，
    包括合并变量的重命名，因为它保持构造器。此度量将用于 η 收缩，不用于
    β 收缩：β 收缩结果中的替换可能复制实参。 *)

Local Open Scope stlc_tm_scope.

(** Each constructor contributes one node; binary constructors count
    both occurrences, even if the two subterms are identical. *)

(** 每个构造器贡献一个节点；即使两个子项相同，二元构造器也计算两次出现。 *)

Fixpoint tm_size {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : nat
  := match t with
  | tm_var _ | tm_unit => 1
  | tm_pair p q | tm_app p q => S (tm_size p + tm_size q)
  | tm_fst p | tm_snd p | tm_lam p => S (tm_size p)
  end.

(** Native syntax equality preserves the numerical measure. *)

(** 原生语法相等保持数值度量。 *)

Global Instance tm_size_proper {B : Type} {Γ : Ctx B} {A : Ty B}
  : Proper (eq ==> eq) (@tm_size B Γ A).
Proof. intros t u h. now destruct h. Defined.

(** Renaming, including its lifted action under a binder, preserves size. *)

(** 重命名及其在绑定之下的提升作用保持大小。 *)

Definition tm_size_rename {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ (ρ : Ren Δ Γ), tm_size t⟨ρ⟩ = tm_size t.
Proof.
  induction t; intros Δ ρ; cbn.
  - reflexivity.
  - reflexivity.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Defined.
