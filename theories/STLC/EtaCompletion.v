From Cats.STLC Require Export
  BetaEtaConfluence
  EtaHead
  SpineRecovery.

(** * Unconditional Function/Product Beta/Eta Confluence

    The remaining product-root diagram is now constructed. At a blocked
    non-pair head, the two native projection equations recover its typed
    variable-headed spine and hence the raw term. The targets already
    coincide, so this last endpoint diagram needs no residual steps.

    For an arbitrary target, beta strong normalization supplies a finite
    selected head path. The existing projection synchronization follows
    that path on the competing target. Pair and variable endpoints were
    already solved; spine recovery solves the remaining endpoints. The
    existing local diagrams and constructive Newman theorem then give
    combined confluence and uniqueness of irreducible endpoints.

    The relation contracts beta redexes and function/product eta redexes
    in all contexts. Unit is a syntax type, but there is no unit
    contraction. Thus these results do not identify this convertibility
    with the whole equational theory [TmEq], which also has unit laws. *)

(** * 无条件的函数／积 βη 合流

    现在构造剩余的积根图式。在被阻塞的非配对头部，两个原生投影等式恢复其
    带类型变量头消去链，继而恢复原始项。两目标已经重合，因此最后这个端点
    图式不需要剩余步骤。

    对任意目标，β 强归一化提供有限的选定头路径。已有的投影同步在竞争目标
    上跟随该路径。配对和变量端点已解决，消去链恢复解决剩余端点。随后由
    已有局部图式及构造性 Newman 定理得到组合合流与不可约终点唯一性。

    该关系在全部上下文中收缩 β 及函数／积 η 红式。单位仍是语法类型，但
    没有单位收缩。因此这些结果不将此可转换性识别为包含单位定律的整个
    等式理论 [TmEq]。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Closing the Head-Terminal Root Diagram

    Fix arbitrary labels with independent syntax and root-evidence
    bounds. Only the first target must have a terminal non-pair head;
    its raw arguments may contain redexes. *)

(** ** 完成头部终止的根图式

    固定任意标签，保持语法界与根证据界独立。只要求第一目标具有终止的
    非配对头部，其原始实参中仍可包含可归约式。 *)

Section HeadTerminalRoots.
Universes b e.
Constraint b <= e.
Context {B : Type@{b}}.

(** Competing product roots at a blocked head have identical targets.
    No normalization or label decision is performed on their arguments. *)

(** 阻塞头部处的竞争积根具有相同目标。不正规化实参，也不判定标签相等。 *)

Definition root_eta_head_terminal_unique {Γ : Ctx B} {A U : Ty B}
    (t v : Tm Γ (A × U))
    (root : RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v)
    (parts : pair_parts t = None) (terminal : head_contractum t = None)
  : t = v.
Proof.
  destruct (root_eta_product_projections t v root) as [left right].
  exact (head_terminal_product_projections_injective t v terminal parts
    left right).
Defined.

End HeadTerminalRoots.

(** ** Unconditional Root and Local Diagrams

    Keep evidence and path bounds independent of classification. The
    former missing endpoint operation is a transparent zero-step join;
    the existing head-path construction supplies the general operation. *)

(** ** 无条件的根图式与局部图式

    证据界与路径界独立于分类界。原先缺失的端点操作现在是透明的零步汇合；
    已有的头路径构造提供一般操作。 *)

Section CompletedDiagrams.
Universes b e p l.
Constraint b <= e, e <= p, e < l.
Context {B : Type@{b}}.

(** Supply the restricted interface without an additional assumption.
    Its absent-variable observation is accepted for interface compatibility;
    joint spine recovery also works when the head is itself a variable. *)

(** 无额外假设地提供受限接口。接口中的变量观测缺失输入仍予接受；联合消去
    链恢复在头部本身为变量时也成立。 *)

Definition eta_head_elimination_roots
  : @is_eta_head_elimination_root_joinable@{b e p l} B.
Proof.
  intros Γ A U t v root parts position terminal.
  pose proof (root_eta_head_terminal_unique t v root parts terminal)
    as same.
  subst v. exact (join_refl _).
Defined.

(** Every competing product-root pair now has a constructed join.
    Beta normalization and projection synchronization remain the single
    existing construction, reused through its former conditional interface. *)

(** 每对竞争积根现在都有已构造的汇合。通过原先的条件接口复用 β 正规化与
    投影同步，保持唯一的既有构造。 *)

Definition eta_product_roots
  : @is_eta_product_root_joinable@{b e p l} B
  := eta_product_roots_of_head_eliminations eta_head_elimination_roots.

(** Eta/eta peaks join using the combined relation. Their residual paths
    may contain beta steps; this is not eta-only confluence. *)

(** η／η 分叉使用组合关系汇合。剩余路径可包含 β 步骤，此处不是纯 η 合流。 *)

Definition eta_eta_joinable (Γ : Ctx B) (A : Ty B)
  : is_locally_joinable@{b e e e p _}
      (@EtaContractStep@{b e l} B Γ A) (@EtaContractStep@{b e l} B Γ A)
      (@BetaEtaContractStep@{b e l} B Γ A)
  := eta_eta_joinable_of_product_roots eta_product_roots Γ A.

(** Assemble beta/beta, both mixed orders, and the completed eta/eta
    diagrams, with no residual diagram premise in the result. *)

(** 组装 β／β、两种混合次序及已完成的 η／η 图式，结果不再含剩余图式前提。 *)

Definition beta_eta_locally_confluent (Γ : Ctx B) (A : Ty B)
  : is_locally_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_locally_confluent_of_product_roots eta_product_roots Γ A.

End CompletedDiagrams.

(** ** Global Confluence and Irreducible Uniqueness

    Fix an independent strong-normalization tree bound. Apply the
    existing constructive Newman theorem to the completed local diagrams.
    Neither a global choice nor equality of reduction witnesses
    is needed. Irreducible endpoints are supplied, not decided. *)

(** ** 全局合流与不可约唯一性

    固定独立的强归一化树界。将已完成的局部图式交给已有的构造性 Newman
    定理。无须全局选择或归约见证相等。不可约终点由外部给定，而非作判定。 *)

Section CompletedConfluence.
Universes b e p s l.
Constraint b <= e, e <= p, e <= s, e < l.
Context {B : Type@{b}}.

(** Full contextual beta plus function/product eta contraction is
    confluent for arbitrary base labels and open typed terms. *)

(** 对任意基标签与开放带类型项，完整上下文 β 加函数／积 η 收缩合流。 *)

Definition beta_eta_confluent (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := newman (beta_eta_locally_confluent Γ A)
      (λ t, (beta_eta_strong_normalization t :
        SN@{b e s} (@BetaEtaContractStep@{b e l} B Γ A) t)).

(** Two supplied irreducible endpoints of one term coincide by native
    syntax equality. This does not compare their path or law witnesses. *)

(** 同一项的两个给定不可约终点按语法原生相等重合，不比较路径或定律见证。 *)

Definition beta_eta_irreducible_unique
    {Γ : Ctx B} {A : Ty B} {t u v : Tm Γ A}
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t u)
    (k : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t v)
    (hu : is_irreducible BetaEtaContractStep@{b e l} u)
    (hv : is_irreducible BetaEtaContractStep@{b e l} v)
  : u = v
  := confluent_irreducible_unique
      (beta_eta_confluent Γ A t) h k hu hv.

End CompletedConfluence.
