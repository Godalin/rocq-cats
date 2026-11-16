From Cats Require Export
  STLC.Gluing.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Pullback
  Cat.Gluing.CCC
  Cat.Functor.Pullback
  Cat.Functor.FiniteProducts
  Instance.Set.Core
  Instance.Set.Lift
  STLC.LogicalRelation
  Instance.Set.PresheafExponential
  Instance.Set.Pullback
  Instance.Set.Terminal
  Instance.Set.Product.

(** * Categorical Gluing and the Existing Normalizer

    Use the identity functor on renaming presheaves as a concrete gluing
    model. Its objects are arrows of presheaves; its morphisms are commuting
    squares. The original realized syntax/value pairs give one such arrow,
    their syntax projection. Evaluation and quotation become squares whose
    composite is exactly the existing NbE comparison.

    This identifies a categorical home for the relation construction, not
    a new normalization proof. In particular, no closure of the subclass of
    logical-relation objects under exponentials is asserted. The full
    identity gluing has an explicitly enabled CCC at sufficient common
    size bounds. The normalization squares themselves retain the weaker,
    independently lifted carrier and equality bounds. *)

(** * 范畴粘合与既有正规化器

    以重命名预层上的恒等函子给出具体粘合模型。其对象是预层箭头，态射是
    交换方形。原有已实现语法/值配对的语法投影给出这样的箭头；求值与引用
    成为方形，其复合恰好是既有 NbE 比较。

    这里为关系构造确定范畴归属，不另证正规化；尤其不声称逻辑关系对象子类
    对指数封闭。完整恒等粘合在充分的共同大小界下有显式启用的 CCC；正规化
    方形本身则保留更弱、分别提升的载体与相等界。 *)

Local Open Scope stlc_ty_scope.

(** ** Realization as an Object and Evaluation as a Square

    Fix independent semantic and equation bounds, with sufficient ambient
    bounds for their lifts and realization evidence. Bind the original
    evaluation lift once, then use its actual domain and codomain. This
    keeps its internal semantic parameters shared by the objects and maps;
    no equality between reconstructed functor-law records is required. *)

(** ** 实现关系作为对象，求值作为方形

    固定独立的语义与等式界，环境界须足以容纳提升及实现证据。只绑定一次
    原求值提升，再使用其实际定义域与陪域，使对象及映射共享内部语义参数；
    不要求重建后的函子定律记录相等。 *)

Section NormalizationSquares.
Universes b r s l e u p.
Constraint b <= e.
Context {B : Type@{b}}.

Let W : Cat
  := RenamingCat B : Cat@{b b r l l}.
Let P : Cat
  := FctCat (W^op) SetCat@{u p _ _ _ _ _}.
Let G : Cat
  := Gluing (@IdF P).

Let source {X Y : @Ob P} (_ : (@Hom P) X Y)
  : @Ob P
  := X.
Let target {X Y : @Ob P} (_ : (@Hom P) X Y)
  : @Ob P
  := Y.
Let evaluation (A : Ty B)
  : (@Hom P) _ _
  := OpenEvaluationGlueN@{b r s l e u p
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _} A.
Let syntax (A : Ty B)
  : @Ob P
  := source (evaluation A).
Let related (A : Ty B)
  : @Ob P
  := target (evaluation A).

(** Equational syntax over itself, with its identity arrow. *)

(** 以恒等箭头将等式语法放在自身之上。 *)

Program Definition NormalizationSourceOb (A : Ty B)
  : @Ob G
  :=
  {|comma_left_ob := syntax A
  ; comma_right_ob := syntax A
  ; comma_arrow := IdN
  |}.

(** Retain both realized values and their evidence, over their syntax. *)

(** 在语法之上保留已实现的配对值及其证据。 *)

Program Definition NormalizationRelationOb (A : Ty B)
  : @Ob G
  :=
  {|comma_left_ob := related A
  ; comma_right_ob := syntax A
  ; comma_arrow := GluingSyntaxN A
  |}.

(** Long normal forms lie over syntax by the original embedding. Equality
    on the base is [TmEq], rather than structural equality of terms. *)

(** 长正规形通过原嵌入位于语法之上；基上的相等是 [TmEq]，而非项的结构相等。 *)

Program Definition NormalizationNormalOb (A : Ty B)
  : @Ob G
  :=
  {|comma_left_ob := GluingNormalF A
  ; comma_right_ob := syntax A
  ; comma_arrow := LiftF ∘Nl NfEmbedN A
  |}.

(** The original fundamental lemma supplies a square over identity syntax. *)

(** 原基本引理给出等式语法恒等箭头之上的方形。 *)

Program Definition CategoricalEvaluationM (A : Ty B)
  : (@Hom G)
      (NormalizationSourceOb A) (NormalizationRelationOb A)
  :=
  {|comma_left := evaluation A
  ; comma_right := IdN
  |}.
Next Obligation.
  intros Γ t. symmetry. exact (gluing_evaluation_syntax A Γ t).
Defined.

(** Reification soundness makes quotation commute with syntax embedding.
    This uses the existing realization witness, without inspecting its
    equality or repeating the induction defining realization. *)

(** 实化可靠性使引用与语法嵌入交换；这里使用已有实现见证，不检查见证相等，
    也不重复定义实现关系的归纳。 *)

Program Definition CategoricalQuoteM (A : Ty B)
  : (@Hom G)
      (NormalizationRelationOb A) (NormalizationNormalOb A)
  :=
  {|comma_left := GluingQuoteN A
  ; comma_right := IdN
  |}.
Next Obligation.
  intros Γ [[[t] [v]] h]. refine {|lower := _
                               |}.
  exact (realizes_reify A Γ t v h).
Defined.

(** Normalization soundness is precisely the remaining square. *)

(** 正规化可靠性恰好给出另一个方形。 *)

Program Definition CategoricalNormalizeM (A : Ty B)
  : (@Hom G)
      (NormalizationSourceOb A) (NormalizationNormalOb A)
  :=
  {|comma_left := LiftF ∘Nl NormalizeN A
  ; comma_right := IdN
  |}.
Next Obligation.
  intros Γ [t]. exact {|lower := nf_sound t
                       |}.
Defined.

(** Composing the evaluation and quotation squares recovers the old NbE
    comparison on the left and identity syntax on the right. *)

(** 复合求值与引用方形，左边恢复原 NbE 比较，右边保持恒等语法。 *)

Definition categorical_evaluation_quote (A : Ty B)
  : @HomEq (G) _ _
      (CategoricalQuoteM A ∘ CategoricalEvaluationM A)
      (CategoricalNormalizeM A).
Proof.
  split.
  - exact (gluing_evaluation_quote A).
  - intros Γ t. reflexivity.
Defined.

(** Embed normal forms into equational syntax as a square. *)

(** 将正规形嵌入等式语法，形成方形。 *)

Program Definition CategoricalNormalInclusionM (A : Ty B)
  : (@Hom G)
      (NormalizationNormalOb A) (NormalizationSourceOb A)
  :=
  {|comma_left := LiftF ∘Nl NfEmbedN A
  ; comma_right := IdN
  |}.
Next Obligation. intros Γ t. reflexivity. Defined.

(** The original normal-form retraction and soundness make this an
    isomorphism over equational syntax. This says nothing about an
    inverse on terms with structural equality. Use [nf_sound] at the
    selected equation bound and [nf_embed_nf] on every normal form. *)

(** 原正规形回缩与可靠性使它成为等式语法之上的同构；这不声称在项的结构
    相等下存在逆。在选定等式界处使用 [nf_sound]，并在每个正规形上使用
    [nf_embed_nf]。 *)

Definition categorical_normalization_iso (A : Ty B)
  : is_iso (CategoricalNormalizeM A).
Proof.
  exists (CategoricalNormalInclusionM A). split; split.
  - intros Γ [t]. refine {|lower := _
                         |}. symmetry. exact (nf_sound t).
  - intros Γ t. reflexivity.
  - intros Γ [v]. refine {|lower := _
                         |}. exact (nf_embed_nf v).
  - intros Γ t. reflexivity.
Defined.

End NormalizationSquares.

(** ** The Same Semantic Function Space

    At the original semantic bound, enable precisely the pointwise products
    and Kripke exponentials already packaged for presheaves. Application
    and abstraction from [EvalN] use these very evaluation and transpose
    maps. No equality between functor-law records is needed. *)

(** ** 同一个语义函数空间

    在原语义界限处，恰好启用已为预层打包的逐点积和 Kripke 指数。[EvalN]
    的应用与抽象使用的就是这些求值与转置映射，无须比较函子定律记录相等。 *)

Section SemanticOperations.
Universes b r s l.
Context {B : Type@{b}}.
Let W : Cat
  := RenamingCat B : Cat@{b b r l l}.
Let P : Cat
  := FctCat (W^op) SetCat@{s s _ _ _ _ _}.
Local Instance semantic_products
  : HasProduct P
  := @FctCat_HasProduct _ _ SetCat_HasProduct.
Local Instance semantic_exponentials
  : HasExponential semantic_products
  := Psh_HasExponential W.

(** The semantic arrow presheaf is the selected exponential, compared by
    the identity natural isomorphism on its original Kripke data. *)

(** 语义箭头预层就是选定指数，通过原 Kripke 数据上的恒等自然同构比较。 *)

Definition SemanticArrowIsoN (A U : Ty B)
  : SemF (A ⇒ U) ≅N (@exp P semantic_products semantic_exponentials
      (SemF U) (SemF A)).
Proof. exists IdN. apply nat_id_iso. Defined.

(** Semantic application is the selected evaluation, pointwise. *)

(** 语义应用逐点就是选定求值。 *)

Definition semantic_application_eval (A U : Ty B)
  : SemanticApplyN A U ≈N
      (@Cats.Cat.Exponential.Core.eval P semantic_products
        semantic_exponentials (SemF A) (SemF U)).
Proof. intros Γ [k a]. reflexivity. Defined.

(** Semantic abstraction is the selected transpose, for any parameter
    presheaf and body map, not only maps produced by syntax evaluation. *)

(** 对任意参数预层和函数体映射，语义抽象就是选定转置；不限于语法求值所得
    的映射。 *)

Definition semantic_abstraction_curry (A U : Ty B)
    (H : Fct (W^op) SetCat@{s s _ _ _ _ _})
    (α : PointwiseProductF H (SemF A) ⇒ SemF U)
  : SemanticCurryN A U H α ≈N
      (@Cats.Cat.Exponential.Core.curry P semantic_products
        semantic_exponentials (SemF A) (SemF U) H α).
Proof. intros Γ z Δ ρ a. reflexivity. Defined.

End SemanticOperations.

(** ** Explicit CCC of the Full Ambient Gluing

    For this chosen structure only, use a common value/equality bound [u]
    containing the world objects, arrows and equality. World laws remain
    separate. Choose the existing pointwise pullbacks and the same Kripke
    exponentials; identity preserves the supplied product cones by their
    original universal property. Importing the module enables no choice. *)

(** ** 完整环境粘合的显式 CCC

    仅为此选定结构，使用容纳世界对象、箭头与相等的共同值/相等界 [u]；世界
    定律仍然独立。选择已有逐点拉回和同一个 Kripke 指数；恒等函子由原泛性质
    保持给定积锥。导入模块不会启用任何选择。 *)

Section ChosenAmbientCCC.
Universes b r l u.
Context (B : Type@{b}).
Let W : Cat
  := RenamingCat B : Cat@{b b r l l}.
Let P : Cat
  := FctCat (W^op) SetCat@{u u _ _ _ _ _}.
Local Instance ambient_products
  : HasProduct P
  := @FctCat_HasProduct _ _ SetCat_HasProduct.
Local Instance ambient_exponentials
  : HasExponential ambient_products
  := Psh_HasExponential W.
Local Instance ambient_terminal
  : HasTerminal P
  := @FctCat_HasTerminal _ _ SetCat_HasTerminal.
Local Instance ambient_pullbacks
  : HasPullback P
  := @FctCat_HasPullback _ _ SetCat_HasPullback.

(** This is the general pullback construction specialized to the identity
    functor, without another exponential universal-property proof. Its
    scope is all arrows of presheaves, not only realization projections. *)

(** 这是一般拉回构造在恒等函子上的专化，不另证指数泛性质；其范围是全部
    预层箭头，而不仅是实现关系的投影。 *)

Definition RenamingGluing_CCC
  : CCC (Gluing (@IdF P))
  := GluingPullback_CCC (@IdF P) (λ A U, product_universal).

End ChosenAmbientCCC.
