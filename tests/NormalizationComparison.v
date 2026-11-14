From Cats.STLC Require Import NormalizationComparison.
From Cats Require Import
  STLC.Set
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Contraction Comparison Universe Regressions

    Keep the path bound independent of world-law classification. A chosen
    normalization isomorphism is sufficient; no semantic bound is forced
    into the comparison API. *)

(** * 收缩比较的宇宙回归

    路径界独立于世界定律的分类界。给定正规化同构已经足够，比较接口不强制
    引入语义界限。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Paths below World Laws

    Fix [b < r < e < p < l]. The path need not contain the larger world
    law bound. Both endpoints use the same selected inverse. *)

(** ** 路径低于世界定律

    固定 [b < r < e < p < l]。路径不需要容纳较大的世界定律界；两个终点
    使用同一个选定逆。 *)

Section SmallPaths.
Universes b r e p l.
Constraint b < r, r < e, e < p, p < l.
Context {B : Type@{b}} (A : Ty B).
Context (I : (NfEmbedN A) ⦂
    (NfPsh A : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{b e _ _ _ _ _}) ≅N TmRenamingPsh A).

(** Neither endpoint's irreducibility is needed for agreement. *)

(** 终点一致性不需要任一终点的不可约性。 *)

Definition small_path_long_comparison {Γ : Ctx B} {t u v : Tm Γ A}
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t u)
    (k : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t v)
  : ContractionLongN A I Γ u = ContractionLongN A I Γ v
  := contraction_endpoints_long A I h k.

End SmallPaths.

(** ** Paths above World Laws

    Fix [b < e < r < l < p]. World hom equality may exceed equation
    witnesses; the comparison also supports paths above world laws. *)

(** ** 路径高于世界定律

    固定 [b < e < r < l < p]。世界 Hom 相等可超过等式见证；比较同样支持
    高于世界定律的路径见证。 *)

Section LargePaths.
Universes b e r l p.
Constraint b < e, e < r, r < l, l < p.
Context {B : Type@{b}} (A : Ty B).
Context (I : (NfEmbedN A) ⦂
    (NfPsh A : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{b e _ _ _ _ _}) ≅N TmRenamingPsh A).

(** Irreducibility certificates and paths retain their own bounds. *)

(** 不可约证书及路径保持各自的界限。 *)

Definition large_path_short_comparison {Γ : Ctx B} (t : Tm Γ A)
    (s : ShortForm Γ A)
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t s.1)
  : ContractionLongN A I Γ t = short_to_long A I s
  := short_endpoint_comparison A I t s h.

End LargePaths.

(** ** The Constructed Normalizer

    The general comparison accepts the actual normalization isomorphism.
    This checks the connection to the executable algorithm. *)

(** ** 已构造的正规化器

    一般比较接受实际的正规化同构；此处检查其与可执行算法的连接。 *)

Section ActualNormalizer.
Context {B : Type}.

(** The chosen inverse of the constructed isomorphism computes as NbE. *)

(** 已构造同构的选定逆按 NbE 计算。 *)

Definition constructed_comparison_computes {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A)
  : ContractionLongN A (NormalFormsIsoN A).2 Γ t = nf t
  := eq_refl.

End ActualNormalizer.
