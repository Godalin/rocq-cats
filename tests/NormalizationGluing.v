From Cats.STLC Require Import Gluing.
From Cats Require Import
  STLC.Set
  Instance.Set.Core
  Instance.Set.Lift.

(** * Normalization Gluing Regressions

    Both projections of one glued value must retain independently chosen
    syntax/equation and semantic bounds. Check the two orders, world laws
    above and below semantics, and equal computational levels. *)

(** * 正规化粘合回归

    同一个粘合值的两个投影必须保持独立选定的语法／等式界和语义界。检查两种
    次序、世界定律高于或低于语义，以及相等的计算层级。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Semantics above Equations

    Fix [b < r < e < s < p < u < l]. Stored values and equation witnesses
    must remain independent; world laws may exceed the glued carrier. *)

(** ** 语义高于等式

    固定 [b < r < e < s < p < u < l]。所存值与等式见证必须独立；世界定律
    可以超过粘合载体。 *)

Section LargeSemantics.
Universes b r e s p u l.
Constraint b < r, r < e, e < s, s < p, p < u, u < l.
Context {B : Type@{b}}.

(** One input simultaneously determines both projection bounds. *)

(** 同一个输入同时确定两个投影的界。 *)

Definition separated_gluing_projections (A : Ty B) (Γ : Ctx B)
    (x : (NormalizationGluingF A : Fct
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _}) Γ)
  : (LiftS@{b e u p} (TmS@{b e} Γ A) *
      LiftS@{s s u p} ((SemF A : Fct
        ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}) Γ))%type
  := (GluingSyntaxN A Γ x, GluingValuesN A Γ x).

End LargeSemantics.

(** ** Equations above Semantics

    Fix [b < r < l < s < e < u < p]. Equality and semantics are reversed;
    semantic values exceed world laws, while ambient equality exceeds
    the glued carrier. *)

(** ** 等式高于语义

    固定 [b < r < l < s < e < u < p]。相等与语义的次序反转；语义值超过世界
    定律，而环境相等超过粘合载体。 *)

Section LargeEquations.
Universes b r l s e u p.
Constraint b < r, r < l, l < s, s < e, e < u, u < p.
Context {B : Type@{b}}.

(** The same interface supports the opposite ordering. *)

(** 同一接口支持相反的次序。 *)

Definition reversed_gluing_projections (A : Ty B) (Γ : Ctx B)
    (x : (NormalizationGluingF A : Fct
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _}) Γ)
  : (LiftS@{b e u p} (TmS@{b e} Γ A) *
      LiftS@{s s u p} ((SemF A : Fct
        ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}) Γ))%type
  := (GluingSyntaxN A Γ x, GluingValuesN A Γ x).

End LargeEquations.

(** ** Equal Computational Bounds

    Syntax, semantics, evidence and glued values may share [b]. Only the
    auxiliary world-law bound is strictly larger. *)

(** ** 相等的计算界

    语法、语义、证据与粘合值可以共用 [b]；只有辅助世界定律界严格更大。 *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}}.

(** No strict separation is required by the gluing construction. *)

(** 粘合构造不要求严格分离。 *)

Definition equal_gluing_projections (A : Ty B) (Γ : Ctx B)
    (x : (NormalizationGluingF A : Fct
      ((RenamingCat B : Cat@{b b b l l})^op)
        SetCat@{b b _ _ _ _ _}) Γ)
  : (LiftS@{b b b b} (TmS@{b b} Γ A) *
      LiftS@{b b b b} ((SemF A : Fct
        ((RenamingCat B)^op) SetCat@{b b _ _ _ _ _}) Γ))%type
  := (GluingSyntaxN A Γ x, GluingValuesN A Γ x).

End EqualLevels.

(** ** Executable Recovery of Normal Forms

    Fix a signature and a base label. Normal forms supplied directly,
    rather than through a prior normalization call, satisfy the retraction.
    The gluing quote of a reflected base neutral is its normal wrapper. *)

(** ** 可执行的正规形恢复

    固定签名及基标签。直接给定、而非通过此前正规化调用生成的正规形满足
    回缩。粘合对反射基中性项的引用，得到其正规包装。 *)

Section Computations.
Context {B : Type} (a : B).

(** The retraction applies to any supplied long normal form. *)

(** 回缩适用于任意给定的长正规形。 *)

Definition supplied_normal_retract {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
  : nf (embed_nf v) = v
  := nf_embed_nf v.

(** A neutral identity abstraction is already a long normal form. *)

(** 中性恒等抽象已经是长正规形。 *)

Example normal_identity_computes
  : nf (embed_nf (nf_lam (nf_base
      (ne_var (var_zero : Var ((ctx_empty : Ctx B) ▻ ty_base a)
        (ty_base a)))))) = nf_lam (nf_base (ne_var var_zero)).
Proof. reflexivity. Defined.

End Computations.
