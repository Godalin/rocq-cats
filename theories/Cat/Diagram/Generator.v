From Cats Require Export
  Cat.Free.
From Cats Require Import
  Cat.FreeObject.Adjunction
  Cat.CatCat.

(** * Graph Interpretations and Free Diagrams

    Fix a graph [G] and a target category [C]. Interpretations have arbitrary
    vertex maps. A morphism consists of arrows between their vertex images,
    natural on generating edges; equality is pointwise Hom equality. Thus
    this category keeps natural transformations as morphisms, rather than
    treating arbitrary natural isomorphisms as equality of graph maps.

    Restriction from functors on [FreeCat G] has chosen free objects, hence
    an ordinary adjunction by the comma-initial theorem. This is a valid
    diagram-level version of the free-category universal property; it does
    not assert a global adjunction in [CatCat]. *)

(** * 图解释与自由图式

    固定图 [G] 及目标范畴 [C]。解释允许任意顶点映射；态射由顶点像之间的箭头
    组成，并在生成边上自然，相等使用逐点 Hom 相等。因此此范畴将自然变换保留
    为态射，不将任意自然同构视作图映射相等。

    从 [FreeCat G] 上的函子作限制得到的函子具有选定自由对象，因而由逗号始性
    定理得到普通伴随。这是自由范畴泛性质的有效图式版本，不声称在 [CatCat]
    中获得全局伴随。 *)

Class GeneratorNat {G : Graph} {C : Cat}
    (D E : G →G UnderlyingGraph C)
  :=
  { generator_component :> ∀ x, Hom (D x) (E x)
  ; generator_naturality : ∀ x y (e : Edge x y),
      generator_component y ∘ edge_map D e ≈
        edge_map E e ∘ generator_component x
  }.

Arguments generator_component {_ _ _ _} _ _.
Arguments generator_naturality {_ _ _ _} _ {_ _} _.

Notation "D '⇒G' E" := (GeneratorNat D E)
  (at level 50, no associativity) : type_scope.

(** Interpretations are compared componentwise, ignoring naturality witnesses. *)

(** 解释之间的态射逐分量比较，忽略自然性见证。 *)

Definition GeneratorNatEq {G : Graph} {C : Cat}
    {D E : G →G UnderlyingGraph C} (α β : D ⇒G E)
  : Type
  := ∀ x, α x ≈ β x.

Infix "≈NG" := GeneratorNatEq (at level 50, no associativity) : cat_scope.

(** Pointwise equality is an equivalence relation. *)

(** 逐点相等是等价关系。 *)

Global Instance GeneratorNatEq_Equivalence {G : Graph} {C : Cat}
    {D E : G →G UnderlyingGraph C}
  : Equivalence (@GeneratorNatEq G C D E).
Proof.
  split.
  - intros α x. reflexivity.
  - intros α β H x. symmetry. apply H.
  - intros α β γ H K x. transitivity (β x); [apply H | apply K].
Defined.

(** The canonical hom-set keeps all component arrows and their square laws. *)

(** 典范 Hom 广集保留全部分量箭头及其方形定律。 *)

Program Canonical GeneratorNatS {G : Graph} {C : Cat}
    (D E : G →G UnderlyingGraph C)
  : SetC
  :=
  {|carrier := D ⇒G E
  ; carrier_equiv := GeneratorNatEq
  ; carrier_setoid := GeneratorNatEq_Equivalence
  |}.

(** Identity vertex arrows are natural on every generator. *)

(** 顶点处的恒等箭头在每条生成边上自然。 *)

Program Definition GeneratorId {G : Graph} {C : Cat}
    (D : G →G UnderlyingGraph C)
  : D ⇒G D
  :=
  {|generator_component x := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.

(** Compose at vertices; associativity supplies the generator squares. *)

(** 在顶点处复合，结合律给出生成边方形。 *)

Program Definition GeneratorComp {G : Graph} {C : Cat}
    {D E H : G →G UnderlyingGraph C} (β : E ⇒G H) (α : D ⇒G E)
  : D ⇒G H
  :=
  {|generator_component x := β x ∘ α x
  |}.
Next Obligation.
  rewrite comp_assoc, (generator_naturality α e), <- comp_assoc,
    (generator_naturality β e), comp_assoc. reflexivity.
Defined.

(** A category of interpretations of a fixed generating graph. *)

(** 固定生成图的解释范畴。 *)

Program Definition GeneratorDiagramCat (G : Graph) (C : Cat)
  : Cat
  :=
  {|Ob := G →G UnderlyingGraph C
  ; HomSet := GeneratorNatS
  ; id := GeneratorId
  ; comp D E H := GeneratorComp
  |}.
Next Obligation. intros α α' Hα β β' Hβ x. apply comp_proper; auto. Defined.
Next Obligation. intros x. apply comp_id_r. Defined.
Next Obligation. intros x. apply comp_id_l. Defined.
Next Obligation. intros x. apply comp_assoc. Defined.

(** Restrict functors and natural transformations to the generating graph. *)

(** 将函子及自然变换限制到生成图。 *)

Program Definition RestrictGeneratorF (G : Graph) (C : Cat)
  : Functor (Fct (FreeCat G) C) (GeneratorDiagramCat G C)
  :=
  {|F0 := RestrictGraph
  ; F1 F H α := {|generator_component := α
                  |}
  |}.
Next Obligation. exact (nt_naturality α (path_edge e)). Defined.
Next Obligation. intros α β E x. exact (E x). Defined.
Next Obligation. intros x. reflexivity. Defined.
Next Obligation. intros x. reflexivity. Defined.

(** Extend generator naturality by the existing path induction theorem. *)

(** 用已有路径归纳定理延拓生成边自然性。 *)

Definition GeneratorExtendN {G : Graph} {C : Cat}
    {D : G →G UnderlyingGraph C} {F : Functor (FreeCat G) C}
    (α : D ⇒G RestrictGraph F)
  : FreeF D ⇒ F
  := @FreeN G C (FreeF D) F α
      (λ x y e, generator_naturality α e).

(** The free diagram retains every assigned vertex and edge. *)

(** 自由图式保留每个指定顶点及生成边。 *)

Program Definition GeneratorUnit {G : Graph} {C : Cat}
    (D : G →G UnderlyingGraph C)
  : D ⇒G RestrictGraph (FreeF D)
  :=
  {|generator_component x := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.

(** This unit is universal for restriction. Uniqueness compares actual
    vertex components, never complete object functions or proof fields. *)

(** 此单位对于限制函子满足泛性质；唯一性比较实际顶点分量，不比较整个对象
    函数或证明字段。 *)

Definition generator_unit_universal {G : Graph} {C : Cat}
    (D : G →G UnderlyingGraph C)
  : GeneratorUnit D ⦂ UnivArr(RestrictGeneratorF G C).
Proof.
  intros F α. exists (GeneratorExtendN α).
  refine {|this := _
          ; that := _
          |}.
  - intros x. apply comp_id_r.
  - intros β H x. specialize (H x).
    change (β x ∘ id ≈ α x) in H.
    rewrite comp_id_r in H. exact H.
Defined.

(** Chosen free diagrams instantiate the general comma-initial interface.
    Enabling this structure is explicit. *)

(** 选定自由图式实例化一般逗号始性接口，启用此结构必须显式进行。 *)

Definition GeneratorFreeObjects (G : Graph) (C : Cat)
  : HasFreeObjects (RestrictGeneratorF G C)
  := FreeObjectsFromUniversal (RestrictGeneratorF G C) FreeF GeneratorUnit
      generator_unit_universal.

(** The free functor extends interpretations and generator transformations. *)

(** 自由函子延拓解释及生成边自然变换。 *)

Definition ExtendGeneratorF (G : Graph) (C : Cat)
  : Functor (GeneratorDiagramCat G C) (Fct (FreeCat G) C)
  := @FreeFunctor _ _ _ (GeneratorFreeObjects G C).

(** The ordinary extension/restriction adjunction is obtained generically.
    Its left object map is [FreeF]; mediator components are unchanged. *)

(** 普通的延拓／限制伴随由一般定理得到；左伴随的对象映射是 [FreeF]，中介
    分量保持不变。 *)

Definition GeneratorFreeAdjunction (G : Graph) (C : Cat)
  : ExtendGeneratorF G C ⊣ RestrictGeneratorF G C
  := @FreeAdjunction _ _ _ (GeneratorFreeObjects G C).

(** Reading back a freely extended interpretation has an identity-component
    comparison in the reverse direction as well. *)

(** 读回自由延拓后的解释，也有分量恒等的逆向比较。 *)

Program Definition generator_unit_inverse {G : Graph} {C : Cat}
    (D : G →G UnderlyingGraph C)
  : RestrictGraph (FreeF D) ⇒G D
  :=
  {|generator_component x := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.

(** The adjunction unit is pointwise invertible, with explicit inverse data. *)

(** 伴随单位逐点可逆，并带有显式逆数据。 *)

Definition generator_adjunction_unit_iso (G : Graph) (C : Cat)
  : adjunction_unit (GeneratorFreeAdjunction G C)
      ⦂ IdF ≅N (RestrictGeneratorF G C ∘F ExtendGeneratorF G C).
Proof.
  intros D. exists (generator_unit_inverse D). split; intros x;
    cbn; rewrite !comp_id_l; reflexivity.
Defined.

(** The counit uses the existing path-extension comparison; its vertex
    components are identities, although its functor records need not be equal. *)

(** 余单位使用已有路径延拓比较，其顶点分量为恒等，但函子记录无需相等。 *)

Definition generator_adjunction_counit_iso (G : Graph) (C : Cat)
  : adjunction_counit (GeneratorFreeAdjunction G C)
      ⦂ (ExtendGeneratorF G C ∘F RestrictGeneratorF G C) ≅N IdF.
Proof.
  intros F. apply NatIso_is_iso. intros x.
  exact ((free_extend_nat_iso F).2 x).
Defined.

(** Generator diagrams and free-category diagrams are equivalent. Both
    categories retain all natural transformations and compare them pointwise. *)

(** 生成图解释与自由范畴图式等价；两个范畴均保留全部自然变换并逐点比较。 *)

Definition generator_diagram_equiv (G : Graph) (C : Cat)
  : GeneratorDiagramCat G C ≃C Fct (FreeCat G) C
  := (ExtendGeneratorF G C; (RestrictGeneratorF G C;
      (symmetry (adjunction_unit (GeneratorFreeAdjunction G C);
         generator_adjunction_unit_iso G C),
       (adjunction_counit (GeneratorFreeAdjunction G C);
         generator_adjunction_counit_iso G C)))).
