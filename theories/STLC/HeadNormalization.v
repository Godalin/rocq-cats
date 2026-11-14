From Cats.STLC Require Export
  HeadReduction
  StrongNormalization.

(** * Constructive Head Normalization

    The selected head successor is computable. A full beta SN tree bounds
    its iteration, giving a terminal head and a finite strategy path.
    Neither arbitrary successor choice nor a classical termination
    principle is needed. Head normality is weaker than beta normality. *)

(** * 构造性头部正规化

    选定头部后继可计算。完整 β 强归一化树限制其迭代，给出终止头部与有限
    策略路径，无须任意后继选择或经典终止原理。头正规性弱于 β 正规性。 *)

(** ** Retained Strategy Paths

    The result needs only signature and path bounds. Its selected edges
    are small; beta evidence and SN trees enter the construction below. *)

(** ** 保留策略路径

    结果只需签名界与路径界。选定边是小型的；β 证据及强归一化树在以下构造
    才引入。 *)

Section HeadResults.
Universes b p.
Constraint b <= p.
Context {B : Type@{b}}.

(** The result retains the exact endpoint, strategy path and terminal
    observation. It asserts nothing about redexes below that head. *)

(** 结果保留精确端点、策略路径及终止观测，不断言该头部之下没有可归约式。 *)

Record HeadResult {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : Type@{p}
  := {
  head_result_term : Tm Γ A;

  head_result_path : ReflTransClosure@{b Set p} HeadBetaStep
    t head_result_term;

  head_result_terminal : head_contractum@{b b} head_result_term = None
}.

End HeadResults.

Arguments head_result_term {B Γ A t} _.
Arguments head_result_path {B Γ A t} _.
Arguments head_result_terminal {B Γ A t} _.

(** ** Forgetting the Strategy Restriction

    A full beta path contains beta edge witnesses, so its bound contains
    their bound. This requirement belongs to the map, not to head results. *)

(** ** 忘却策略限制

    完整 β 路径包含 β 边见证，因此其界容纳边界。此要求属于映射，而非头部
    结果本身。 *)

Section BetaPathMapping.
Universes b e p l.
Constraint b <= e, e <= p, e < l.
Context {B : Type@{b}}.

(** Strategy paths map to full contextual beta paths edge by edge. *)

(** 策略路径逐边映为完整上下文 β 路径。 *)

Definition head_beta_path_beta {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : ReflTransClosure@{b Set p} HeadBetaStep t u)
  : ReflTransClosure@{b e p} BetaStep@{b e l b} t u
  := rtc_preserves (λ x, x)
      (λ x y k, rtc_step (head_beta_step_beta k)) h.

End BetaPathMapping.

(** ** Following an SN Tree

    Keep beta evidence, strategy paths, SN trees and classification
    independent. The small strategy path need not contain beta evidence,
    and neither tree nor path needs to contain the other. *)

(** ** 跟随强归一化树

    β 证据、策略路径、强归一化树及分类界各自独立。小型策略路径无须容纳
    β 证据，树界与路径界也不必相互容纳。 *)

Section HeadNormalization.
Universes b e p s l.
Constraint b <= e, b <= p, e <= s, e < l.
Context {B : Type@{b}}.

(** Follow the chosen edge through the supplied SN tree. In particular,
    no decidability assumption about the full beta relation is used. *)

(** 沿给定强归一化树跟随选定边；特别地，不假设完整 β 关系可判定。 *)

Definition head_normalize_sn {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
    (tree : SN@{b e s} BetaStep@{b e l b} t)
  : HeadResult@{b p} t.
Proof.
  induction tree as [t next ih].
  destruct (head_contractum t) as [u |] eqn:step.
  - destruct (ih u (head_contractum_beta t u step)) as [z path terminal].
    refine {|head_result_term := z
           ; head_result_path := rtc_cons
               {|head_beta_observation := step|} path
           ; head_result_terminal := terminal
           |}.
  - exact {|head_result_term := t
          ; head_result_path := rtc_refl t
          ; head_result_terminal := step
          |}.
Defined.

(** The established all-term beta SN theorem supplies the tree. *)

(** 既有的全项 β 强归一化定理提供所需树。 *)

Definition head_normalize {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : HeadResult@{b p} t
  := head_normalize_sn t (beta_strong_normalization t).

End HeadNormalization.
