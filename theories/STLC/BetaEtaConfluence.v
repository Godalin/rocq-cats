From Cats.STLC Require Export
  BetaEtaLocal
  EtaLocal
  BetaEtaNormalization.

(** * Beta/Eta Confluence from Product Root Diagrams

    All beta/beta and mixed beta/eta diagrams are already constructed.
    Eta local analysis reduces its remaining obligation to the product
    root/root diagram. Given that explicit input, copair the local cases
    and apply Newman's lemma to combined strong normalization.

    These theorems deliberately retain the unconstructed product-root
    input. They verify the rest of the confluence argument, but do not
    assert that unrestricted beta/eta confluence has been completed. *)

(** * 从积根图式得到 βη 合流

    全部 β／β 及混合 β／η 图式已经构造。η 的局部分析将剩余义务缩减至积的
    根／根图式。给定此显式输入后，对局部情形作余配对，再对组合强归一化
    应用 Newman 引理。

    这些定理特意保留尚未构造的积根输入。它们验证合流论证的其他部分，但不
    断言无限制的 βη 合流已经完成。 *)

Local Open Scope relation_scope.

(** ** Assembling the Local Peaks

    Fix arbitrary base labels and independent step, path, normalization
    tree and classification bounds. Supply the remaining product-root
    operation explicitly; no global instance or axiom provides it. *)

(** ** 组装局部分叉

    固定任意基标签，以及独立的步骤、路径、归一化树和分类界。显式提供剩余
    的积根操作；没有全局实例或公理提供它。 *)

Section ConditionalConfluence.
Universes b e p s l.
Constraint b <= e, e <= s, e < l.
Context {B : Type@{b}}.
Context (product_roots : @is_eta_product_root_joinable@{b e p l} B).

(** Copair beta/beta, the two mixed orders, and eta/eta diagrams. *)

(** 对 β／β、两种混合次序及 η／η 图式作余配对。 *)

Definition beta_eta_locally_confluent_of_product_roots
    (Γ : Ctx B) (A : Ty B)
  : is_locally_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A).
Proof.
  intros t u v [h | h] [k | k].
  - exact (join_preserves (λ x, x) (λ x y q, inl q)
      (beta_locally_confluent Γ A t u v h k)).
  - exact (beta_eta_locally_joinable Γ A t u v h k).
  - exact (join_sym (beta_eta_locally_joinable Γ A t v u k h)).
  - exact (eta_eta_joinable_of_product_roots product_roots Γ A t u v h k).
Defined.

(** Newman uses an independent normalization-tree bound. The sole
    unresolved input remains visible in this theorem's type. *)

(** Newman 使用独立的归一化树界；唯一未解决的输入仍在定理类型中可见。 *)

Definition beta_eta_confluent_of_product_roots (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := newman (beta_eta_locally_confluent_of_product_roots Γ A)
      (λ t, (beta_eta_strong_normalization t :
        SN@{b e s} (@BetaEtaContractStep@{b e l} B Γ A) t)).

(** Given the same product-root input, any two supplied irreducible
    endpoints of one term coincide by native syntax equality. *)

(** 给定同一积根输入后，同一项的任意两个给定不可约终点按语法原生相等重合。 *)

Definition beta_eta_irreducible_unique_of_product_roots
    {Γ : Ctx B} {A : Ty B} {t u v : Tm Γ A}
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t u)
    (k : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t v)
    (hu : is_irreducible BetaEtaContractStep@{b e l} u)
    (hv : is_irreducible BetaEtaContractStep@{b e l} v)
  : u = v
  := confluent_irreducible_unique
      (beta_eta_confluent_of_product_roots Γ A t) h k hu hv.

End ConditionalConfluence.
