From Cats.STLC Require Export
  Normalization
  EtaSource.
From Cats.Set.Relation Require Export Confluence.
From Cats.STLC Require Import ReductionSource.
From Cats Require Import
  STLC.Set
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Contraction Results and Long Normal Forms

    A short result is an irreducible endpoint for function/product beta
    and eta contraction. A long normal form represents full equational
    equality, including the unit equation. These are different notions.
    Contraction paths preserve the long representative, but this map is
    not injective: a unit variable and the unit constant are distinct
    irreducible terms with the same long representative.

    Use any chosen inverse of the normal embedding. The natural
    isomorphism constructed by normalization supplies this input, while
    the comparison itself uses only respectfulness and its inverse laws.
    No reduction strategy or equality decision is assumed. *)

(** * 收缩结果与长正规形

    短结果是函数／积 βη 收缩的不可约终点。长正规形表示完整的等式相等，
    包括单位方程。这是不同的概念。收缩路径保持长代表元，但此映射不是单射：
    单位类型的变量与单位常量是不同的不可约项，却有同一个长代表元。

    使用正规嵌入的任意选定逆映射。正规化构造的自然同构提供此输入，比较本身
    仅使用保相等性及互逆律。不假定归约策略或相等判定。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Irreducible Endpoints

    Fix arbitrary base labels and independent step and classification
    bounds. The witness stores the term and the absence of outgoing steps;
    it does not choose a reduct for every input. *)

(** ** 不可约终点

    固定任意基类型标签及独立的步骤界和分类界。见证保存项及向外步骤不存在的
    证明；它不为每个输入选定归约结果。 *)

Section ShortResults.
Universes b e l.
Context {B : Type@{b}}.

(** An irreducible term with its Type-valued certificate. *)

(** 带 Type 值证书的不可约项。 *)

Definition ShortForm (Γ : Ctx B) (A : Ty B)
  : Type
  := ∃ t : Tm Γ A, is_irreducible BetaEtaContractStep@{b e l} t.

(** Variables have neither beta nor eta successors. *)

(** 变量既没有 β 后继，也没有 η 后继。 *)

Definition beta_eta_var_irreducible {Γ : Ctx B} {A : Ty B}
    (x : Var Γ A)
  : is_irreducible BetaEtaContractStep@{b e l} (# x).
Proof.
  intros u [h | h].
  - exact (beta_step_var_absurd x h).
  - exact (eta_contract_var_absurd x h).
Defined.

(** The unit constant is also irreducible for the specified rule set. *)

(** 单位常量对此指定规则集同样不可约。 *)

Definition beta_eta_unit_irreducible (Γ : Ctx B)
  : is_irreducible BetaEtaContractStep@{b e l} (tm_unit (Γ := Γ)).
Proof.
  intros u [h | h].
  - exact (beta_step_unit_absurd h).
  - exact (eta_contract_unit_absurd h).
Defined.

End ShortResults.

(** ** Comparison through a Chosen Normalization Isomorphism

    Fix one result type and a chosen inverse of its normal embedding.
    World equality, equation witnesses and finite contraction paths have
    independent bounds. Irreducible terms are not made into a renaming
    presheaf: a renaming can create an eta redex by identifying variables. *)

(** ** 经选定正规化同构作比较

    固定一个结果类型及其正规嵌入的选定逆。世界相等、等式见证和有限收缩路径
    各有独立界限。不将不可约项组织成重命名预层：重命名可能因识别变量而产生
    η 可归约式。 *)

Section LongComparison.
Universes b r e p l.
Context {B : Type@{b}} (A : Ty B).
Context (I : (NfEmbedN A) ⦂
    (NfPsh A : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{b e _ _ _ _ _}) ≅N TmRenamingPsh A).

(** The inverse retains the chosen long-normalization algorithm. *)

(** 此逆映射保留选定的长正规化算法。 *)

Definition ContractionLongN
  : TmRenamingPsh A ⇒ NfPsh A
  := (NfEmbedN A)^-1N I.

(** The chosen representative embeds back to an equationally equal term.
    This is the right inverse law of the supplied natural isomorphism. *)

(** 选定代表元嵌入后与原项等式相等。这是给定自然同构的右逆律。 *)

Definition contraction_long_sound {Γ : Ctx B} (t : Tm Γ A)
  : TmEq@{b e _} t (embed_nf (ContractionLongN Γ t)).
Proof. symmetry. exact (snd (I Γ).2 t). Defined.

(** Every supplied normal tree is recovered by the chosen inverse. *)

(** 选定逆恢复每个给定正规语法树。 *)

Definition contraction_long_retract {Γ : Ctx B} (v : Nf Γ A)
  : ContractionLongN Γ (embed_nf v) = v.
Proof. exact (fst (I Γ).2 v). Defined.

(** A contraction edge preserves the long representative because its
    equation is respected by the inverse natural transformation. *)

(** 收缩边保持长代表元，因为逆自然变换保持该边给出的等式。 *)

Definition contraction_long_step {Γ : Ctx B} {t u : Tm Γ A}
    (h : BetaEtaContractStep@{b e _} t u)
  : ContractionLongN Γ t = ContractionLongN Γ u.
Proof.
  exact (@func_proper _ _ (ContractionLongN Γ) t u
    (beta_eta_contract_to_tm_eq h)).
Defined.

(** Every finite path has the same invariance, including empty paths. *)

(** 每条有限路径均有同样的不变性，包括空路径。 *)

Definition contraction_long_path {Γ : Ctx B} {t u : Tm Γ A}
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e _} t u)
  : ContractionLongN Γ t = ContractionLongN Γ u.
Proof.
  induction h as [t | t u v h k IH].
  - reflexivity.
  - exact (eq_trans (contraction_long_step h) IH).
Defined.

(** Forgetting the irreducibility certificate gives a long representative.
    Distinct certificates need not be identified. *)

(** 忘掉不可约证书后得到长代表元；不需要识别不同的证书。 *)

Definition short_to_long {Γ : Ctx B} (s : ShortForm Γ A)
  : Nf Γ A
  := ContractionLongN Γ s.1.

(** Any supplied short endpoint agrees with the long result of its input.
    The statement does not choose a path or an endpoint. *)

(** 任意给定短终点都与其输入的长结果一致。此陈述不选定路径或终点。 *)

Definition short_endpoint_comparison {Γ : Ctx B} (t : Tm Γ A)
    (s : ShortForm Γ A)
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e _} t s.1)
  : ContractionLongN Γ t = short_to_long s
  := contraction_long_path h.

(** Any two supplied contraction endpoints have equal long representatives,
    whether or not either endpoint is already irreducible. This follows
    from invariance, not from confluence of contraction. *)

(** 任意两个给定收缩终点都有相等的长代表元，无论终点是否已经不可约。
    此结论来自不变性，而不是收缩关系的合流性。 *)

Definition contraction_endpoints_long {Γ : Ctx B} {t u v : Tm Γ A}
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e _} t u)
    (k : ReflTransClosure@{b e p} BetaEtaContractStep@{b e _} t v)
  : ContractionLongN Γ u = ContractionLongN Γ v
  := eq_trans (eq_sym (contraction_long_path h)) (contraction_long_path k).

End LongComparison.

(** ** The Unit Boundary

    In a context with one unit variable, that variable and the constant
    are different raw trees and both are short. Every respectful long
    normalization identifies them by the unit equation. Thus uniqueness
    of contraction endpoints, once proved, cannot imply a bijection with
    full equational long normal forms. *)

(** ** 单位类型的边界

    在含一个单位变量的上下文中，该变量与常量是不同的原始语法树，且两者都
    是短结果。任意保相等的长正规化均由单位方程识别它们。因此，即使证明了
    收缩终点的唯一性，也不能由此得到与完整等式长正规形的双射。 *)

Section UnitBoundary.
Universes b r e l.
Context {B : Type@{b}}.

(** The variable short form retains its irreducibility witness. *)

(** 变量短正规形保留其不可约见证。 *)

Definition UnitVariableShort
  : ShortForm (∅ ▻ ⊤) (ty_unit (B := B))
  := existT _ (# var_zero) (beta_eta_var_irreducible var_zero).

(** The constant is another short form in the same judgement. *)

(** 常量是同一类型判断中的另一个短正规形。 *)

Definition UnitConstantShort
  : ShortForm (∅ ▻ ⊤) (ty_unit (B := B))
  := existT _ ⋆ (beta_eta_unit_irreducible _).

(** Native inequality distinguishes the two raw constructors. *)

(** 原生不相等区分两个原始构造器。 *)

Definition unit_short_distinct
  : UnitVariableShort.1 = UnitConstantShort.1 → Empty_set.
Proof. intros h. discriminate h. Defined.

(** Every long representative map identifies these distinct short forms. *)

(** 每个长代表元映射都会识别这两个不同的短正规形。 *)

Definition unit_short_long_equal
    (Q : (TmRenamingPsh (ty_unit (B := B)) : Functor
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{b e _ _ _ _ _}) ⇒ NfPsh ⊤)
  : Q (∅ ▻ ⊤) UnitVariableShort.1 = Q (∅ ▻ ⊤) UnitConstantShort.1.
Proof.
  exact (@func_proper _ _ (Q (∅ ▻ ⊤)) _ _ (tm_eq_unit_η _)).
Defined.

(** Even injectivity on the underlying short terms is impossible. The
    conclusion makes no comparison between irreducibility certificates. *)

(** 即使仅要求对底层短项单射也不可能。此结论不比较不可约证书。 *)

Definition unit_short_long_not_injective
    (Q : (TmRenamingPsh (ty_unit (B := B)) : Functor
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{b e _ _ _ _ _}) ⇒ NfPsh ⊤)
    (injective : ∀ s t : ShortForm (∅ ▻ ⊤) (ty_unit (B := B)),
      Q (∅ ▻ ⊤) s.1 = Q (∅ ▻ ⊤) t.1 → s.1 = t.1)
  : Empty_set
  := unit_short_distinct (injective _ _ (unit_short_long_equal Q)).

End UnitBoundary.
