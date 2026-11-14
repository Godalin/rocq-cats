From Cats.STLC Require Export
  EtaContraction
  Size.
From Cats.Set.Relation Require Export StrongNormalization.
From Cats.Set.Relation Require Import Compatible.
From Stdlib Require Import Lia.

(** * Strong Normalization of Eta Contraction

    Every function/product eta contraction strictly reduces structural
    syntax size. The general natural-number measure theorem therefore
    constructs a normalization tree for every term, with all contextual
    eta choices represented. This proof is independent of beta SN.

    The same measure does not prove termination of the beta/eta union:
    beta substitution can duplicate terms. A subsequent interaction
    argument must handle the combined relation. *)

(** * η 收缩的强归一化

    每个函数／积 η 收缩都严格减小语法结构大小。因此，一般自然数度量定理
    为每个项构造归一化树，涵盖全部上下文 η 选择。此证明独立于 β 的 SN。

    同一个度量不能证明 βη 之并终止：β 替换可能复制项。组合关系须由后续的
    相互作用论证处理。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Measures in Typed Contexts

    Fix arbitrary labels. Every one-hole constructor is strictly
    monotone in its varying child's size, including the lambda operation
    that changes context. The generic closure fold then propagates any
    root system's size decrease. *)

(** ** 带类型上下文中的度量

    固定任意标签。每个单孔构造器对变化子项的大小严格单调，包括改变上下文
    的 λ 操作。随后一般闭包折叠将任意根规则系统的大小下降传到上下文中。 *)

Section ContextMeasures.
Context {B : Type}.

(** A surrounding constructor preserves a strict decrease of its child. *)

(** 外层构造器保持其子项的严格下降。 *)

Definition tm_size_context_lt {i j : TmIndex B}
    (c : TmOperation i j) {t u : TmAt i}
    (h : tm_size u < tm_size t)
  : tm_size (TmContexts B _ _ c u) < tm_size (TmContexts B _ _ c t).
Proof. destruct c; cbn in *; lia. Defined.

(** Any root system decreasing this measure does so under all contexts.
    Its step evidence need not live in the universe of natural numbers. *)

(** 任意按此度量下降的根系统在全部上下文中仍下降；步骤证据无须位于自然数
    的宇宙。 *)

Definition context_step_size_decrease (R : TmRelation B)
    (hr : ∀ Γ A (t u : Tm Γ A), R Γ A t u → tm_size u < tm_size t)
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A} (h : ContextStep R t u)
  : tm_size u < tm_size t
  := context_closure_preserves (TmContexts B)
      (λ i j c x y p, tm_size_context_lt c p)
      (λ i x y p, hr (fst i) (snd i) x y p) (Γ, A) t u h.

End ContextMeasures.

(** Function expansion adds a lambda, an application and a variable;
    product expansion adds the pair and two projections while repeating
    its argument. Renaming invariance accounts for the fresh binder. *)

(** 函数展开增加一个 λ、一个应用和一个变量；积展开增加配对及两个投影，并
    重复其参数。重命名不变性处理新鲜绑定。 *)

Definition root_eta_contract_size@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootEtaContract@{b e} t u)
  : tm_size u < tm_size t.
Proof.
  destruct h; cbn.
  - rewrite tm_size_rename. lia.
  - lia.
Defined.

(** Context reversal and the generic decrease fold retain the original
    eta derivation while certifying its numerical decrease. *)

(** 上下文反向与一般下降折叠在保留原 η 推导的同时，为其数值下降提供证书。 *)

Definition eta_contract_size@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : EtaContractStep@{b e _} t u)
  : tm_size u < tm_size t
  := context_step_size_decrease (@RootEtaContract@{b e} B)
      (λ Γ A t u h, root_eta_contract_size h) (eta_contract_context h).

(** ** Eta Trees at Independent Sizes

    Fix syntax at [b], eta evidence at [e], trees at [s], and an independent
    classification bound [l]. Only [b <= e <= s] and [e < l] are needed.
    The small size measure does not resize or identify eta witnesses. *)

(** ** 独立大小的 η 树

    固定 [b] 处的语法、[e] 处的 η 证据、[s] 处的树，以及独立分类界 [l]。
    只要求 [b <= e <= s] 和 [e < l]。小的大小度量不缩小或识别 η 见证。 *)

Section EtaTrees.
Universes b e s l.
Constraint b <= e, e <= s, e < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Every typed term is strongly normalizing for eta contraction alone. *)

(** 每个带类型项对单独的 η 收缩都强归一化。 *)

Definition eta_strong_normalization (t : Tm Γ A)
  : SN@{b e s} (@EtaContractStep@{b e l} B Γ A) t
  := sn_measure tm_size (λ x y h, eta_contract_size h) t.

(** The general tree argument excludes an infinite eta-only sequence. *)

(** 一般树论证排除仅含 η 的无限序列。 *)

Definition eta_no_infinite_sequence (f : nat → Tm Γ A)
    (h : ∀ n, EtaContractStep@{b e l} (f n) (f (S n)))
  : Empty_set
  := sn_no_infinite_sequence f h (eta_strong_normalization (f 0)).

End EtaTrees.
