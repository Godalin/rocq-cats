From Cats Require Export
  STLC.Normalization
  Cat.Functor.RelationGluing.
From Cats Require Import
  STLC.LogicalRelation
  STLC.EvaluationEquivalence
  Instance.Set.Core
  Instance.Set.Lift
  Instance.Set.Kripke.

(** * A Relation Gluing Model for Normalization

    Glue equational syntax to semantic values using the existing logical
    relation. The general diagram construction retains related pairs and
    supplies their natural projections and lifting property. The
    fundamental lemma lifts open evaluation into this glued diagram.

    Quoting the value of any glued pair agrees with normalizing its
    syntax. This comparison is natural in renaming worlds and recovers
    the implemented NbE algorithm on the evaluation lift. It uses the
    retraction on every long normal form, not just algorithm outputs.

    The construction is relation gluing over renaming presheaves. Its
    result is a normalization comparison; a general cartesian closed
    Artin-gluing construction is a separate categorical theorem. All
    relatedness witnesses are retained and their equality is not assumed. *)

(** * 正规化的关系粘合模型

    使用既有逻辑关系，将等式语法与语义值粘合。一般图式构造保留相关配对，
    并提供自然投影和提升性质。基本引理将开放项求值提升到这个粘合图式中。

    任意粘合配对的语义值经引用，等于其语法经正规化。该比较在重命名世界上
    自然，并在求值提升上恢复已经实现的 NbE 算法。这里使用每个长正规形上的
    回缩，不限于算法的输出。

    此构造是重命名预层上的关系粘合，所得结果是正规化比较；一般笛卡尔闭的
    Artin 粘合构造是另一个范畴论定理。全部关联见证均保留，不假定见证相等。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** ** A Common Ambient Presheaf Category

    Fix arbitrary base labels, world and semantic bounds, and an
    equational bound [e] independent of the semantic bound [s]. Explicit
    lifts put syntax and values into a common carrier bound [u] and
    equality bound [p]. The carrier also contains realization evidence;
    no witness is resized downward and no law compares its fields. *)

(** ** 共同环境预层范畴

    固定任意基类型标签、世界和语义界限，以及独立于语义界 [s] 的等式界
    [e]。显式提升将语法与值放入共同载体界 [u] 和相等界 [p]。载体还容纳
    实现证据，不向下重设见证大小，也不使用比较见证字段的定律。 *)

Section NormalizationGluing.
Universes b r s l e u p.
Constraint b <= e.
Context {B : Type@{b}}.

(** Raise equational syntax, retaining its original equation witnesses. *)

(** 提升等式语法，保留原有等式见证。 *)

Definition GluingSyntaxF (A : Ty B)
  : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{u p _ _ _ _ _}
  := LiftF ∘F (TmRenamingPsh A : Functor
      ((RenamingCat B)^op) SetCat@{b e _ _ _ _ _}).

(** Raise the existing semantic presheaf, preserving its value equality. *)

(** 提升既有语义预层，保持其值相等。 *)

Definition GluingValuesF (A : Ty B)
  : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{u p _ _ _ _ _}
  := LiftF ∘F (SemF A : Functor
      ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}).

(** The same ambient category also contains lifted long normal syntax. *)

(** 同一环境范畴也容纳提升后的长正规语法。 *)

Definition GluingNormalF (A : Ty B)
  : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{u p _ _ _ _ _}
  := LiftF ∘F (NfPsh A : Functor
      ((RenamingCat B)^op) SetCat@{b e _ _ _ _ _}).

(** Realization is a respectful diagram relation: equation and semantic
    transport give respectfulness; world transport gives the arrow action.
    No new relation or fundamental lemma is introduced. *)

(** 实现关系是保相等的图式关系：等式和语义运输给出保相等性，世界运输给出
    箭头作用。不引入另一套关系或基本引理。 *)

Program Definition NormalizationRelation (A : Ty B)
  : DiagramRelation (GluingSyntaxF A) (GluingValuesF A)
  :=
  {|diagram_relation Γ t v := Realizes A Γ (lower t) (lower v)
  ; diagram_relation_map Γ Δ ρ t v h :=
      realizes_rename A Γ Δ ρ (lower t) (lower v) h
  |}.
Next Obligation.
  intros [t] [t'] [h] [v] [v'] [k].
  exact (Realizes_proper A X t t' h v v' k).
Defined.

(** A realized syntax/value pair, by the general relation-gluing functor. *)

(** 由一般关系粘合函子得到的已实现语法与值配对。 *)

Definition NormalizationGluingF (A : Ty B)
  : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{u p _ _ _ _ _}
  := RelationGluingF (GluingSyntaxF A) (GluingValuesF A)
      (NormalizationRelation A).

(** The first projection remembers syntax and forgets its realization. *)

(** 第一投影保留语法，忘却其实现见证。 *)

Definition GluingSyntaxN (A : Ty B)
  : NormalizationGluingF A ⇒ GluingSyntaxF A
  := RelationGluingLeftN _ _ (NormalizationRelation A).

(** The second projection remembers the semantic value. *)

(** 第二投影保留语义值。 *)

Definition GluingValuesN (A : Ty B)
  : NormalizationGluingF A ⇒ GluingValuesF A
  := RelationGluingRightN _ _ (NormalizationRelation A).

(** Evaluate an open term in its reflected initial environment. The
    explicit lifts retain independent syntax and semantic sizes. *)

(** 在反射初始环境中求值开放项；显式提升保留独立的语法与语义大小。 *)

Program Definition OpenEvaluationN (A : Ty B)
  : GluingSyntaxF A ⇒ GluingValuesF A
  :=
  {|nt Γ :=
     {|func t := {|lower := EvalN (lower t) Γ (initial_env Γ)
                 |}
     |}
  |}.
Next Obligation.
  intros [t] [t'] [h]. refine {|lower := _
                            |}.
  exact (eval_tm_eq h Γ (initial_env Γ)).
Defined.
Next Obligation.
  intros [t]. refine {|lower := _
                     |}. apply eval_initial_rename.
Defined.

(** The evaluation fundamental lemma supplies the membership needed by
    the generic lift. Its syntax projection is the identity. *)

(** 求值基本引理提供一般提升所需的隶属见证；其语法投影为恒等。 *)

Definition OpenEvaluationGlueN (A : Ty B)
  : GluingSyntaxF A ⇒ NormalizationGluingF A.
Proof.
  refine (RelationGluingPairN _ _ (NormalizationRelation A)
    idN (OpenEvaluationN A) _).
  intros Γ [t].
  apply eval_reflected_realizes.
  intros U x. exact (reflected_env_lookup Γ Γ idRen U x).
Defined.

(** The first projection of the lift recovers the input syntax. *)

(** 提升的第一投影恢复输入语法。 *)

Definition gluing_evaluation_syntax (A : Ty B)
  : (GluingSyntaxN A ∘Nv OpenEvaluationGlueN A) ≈N idN.
Proof. apply relation_gluing_pair_β1. Defined.

(** The second projection recovers ordinary open evaluation. *)

(** 第二投影恢复通常的开放项求值。 *)

Definition gluing_evaluation_values (A : Ty B)
  : (GluingValuesN A ∘Nv OpenEvaluationGlueN A) ≈N OpenEvaluationN A.
Proof. apply relation_gluing_pair_β2. Defined.

(** Quote the value projection with the already constructed lifted
    reification, keeping exactly one underlying quotation algorithm. *)

(** 用已经构造的提升实化引用值投影，保留唯一的底层引用算法。 *)

Definition GluingQuoteN (A : Ty B)
  : NormalizationGluingF A ⇒ GluingNormalF A
  := ReifyN (lift_reification (TypeReification A)) ∘Nv GluingValuesN A.

(** Every realized pair has one canonical long tree: quoting its value
    agrees with normalizing its syntax. Soundness of reification and the
    normal-form retraction supply the comparison. *)

(** 每个已实现配对具有同一个典范长语法树：引用其值，等于正规化其语法。
    比较由实化可靠性及正规形回缩给出。 *)

Definition gluing_quote_normalize (A : Ty B)
  : GluingQuoteN A ≈N
      ((LiftF ∘Nl NormalizeN A) ∘Nv GluingSyntaxN A).
Proof.
  intros Γ [[[t] [v]] h]. refine {|lower := _
                               |}.
  pose proof (nf_tm_eq (realizes_reify A Γ t v h)) as normal.
  rewrite nf_embed_nf in normal. symmetry. exact normal.
Defined.

(** Restricting the comparison to the evaluation lift recovers NbE as
    a natural transformation, with the same executable normalizer. *)

(** 将比较限制到求值提升，就按自然变换恢复使用同一可执行正规化器的 NbE。 *)

Definition gluing_evaluation_quote (A : Ty B)
  : (GluingQuoteN A ∘Nv OpenEvaluationGlueN A) ≈N
      (LiftF ∘Nl NormalizeN A).
Proof.
  intros Γ t. exact (gluing_quote_normalize A Γ (OpenEvaluationGlueN A Γ t)).
Defined.

End NormalizationGluing.
