From Cats.STLC Require Export
  EtaInteraction
  EtaNormalization
  StrongNormalization.
From Cats.Set.Relation Require Export QuasiCommutation.

(** * Strong Normalization of Beta/Eta Contraction

    Every typed term is strongly normalizing for the full contextual sum
    of beta contraction and function/product eta contraction. Separate
    termination is only part of the proof: the interaction diagram in
    [beta_eta_quasi_commuting] allows the general quasi-commutation theorem
    to assemble a tree containing every mixed reduction choice.

    Beta may duplicate arguments; product eta has two copies to account
    for. Their residual work is a finite mixed path, not a single edge.
    The generic proof follows those paths to existing subtrees and needs
    neither a numerical beta bound nor choice or witness irrelevance.

    Unit terms remain in the syntax, but no unit contraction is added.
    This theorem does not assert confluence or completeness for all of
    [TmEq], which also contains the separate unit equation. *)

(** * βη 收缩的强归一化

    每个带类型项对完整上下文 β 收缩与函数／积 η 收缩之和都强归一化。
    分别终止只是证明的一部分：[beta_eta_quasi_commuting] 的相互作用图使
    一般准交换定理能够组装涵盖每种混合归约选择的树。

    β 可能复制实参，积 η 则有两个副本须处理。剩余工作是有限混合路径，而非
    单独一条边。一般证明沿这些路径取得既有子树，无须 β 的数值界、选择或
    见证无关性。

    单位项仍保留在语法中，但不加入单位收缩。此定理不声称合流，也不声称对
    包含独立单位方程的整个 [TmEq] 完备。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** All Typed Terms

    Fix syntax at [b], mixed steps at [e], trees at [s] and an independent
    classification bound [l]. Only [b <= e <= s] and [e < l] are required.
    Intermediate path bounds can be inferred inside the construction. *)

(** ** 所有带类型项

    固定 [b] 处的语法、[e] 处的混合步骤、[s] 处的树及独立分类界 [l]。
    只要求 [b <= e <= s] 和 [e < l]；中间路径的界可在构造内部推导。 *)

Section BetaEtaTrees.
Universes b e s l.
Constraint b <= e, e <= s, e < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The normalization tree covers all interleavings, including beta and
    eta under unapplied binders. No strategy is chosen. *)

(** 归一化树覆盖全部交错，包括尚未应用的绑定之下的 β 与 η；不选择策略。 *)

Definition beta_eta_strong_normalization (t : Tm Γ A)
  : SN@{b e s} (@BetaEtaContractStep@{b e l} B Γ A) t
  := sn_sum_quasi_commuting (beta_eta_quasi_commuting Γ A)
      (λ u, eta_strong_normalization u) (beta_strong_normalization t).

(** An infinite sequence of arbitrary mixed choices contradicts the
    constructed tree. This is a consequence, not the definition of SN. *)

(** 任意混合选择的无限序列与所构造的树矛盾；这是结论，而非 SN 的定义。 *)

Definition beta_eta_no_infinite_sequence (f : nat → Tm Γ A)
    (h : ∀ n, BetaEtaContractStep@{b e l} (f n) (f (S n)))
  : Empty_set
  := sn_no_infinite_sequence f h (beta_eta_strong_normalization (f 0)).

End BetaEtaTrees.
