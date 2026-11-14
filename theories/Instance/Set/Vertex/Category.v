From Cats Require Export
  Instance.Set.Vertex.Functor.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core.

(** * The Category of Specified Object Presentations

    A presentation bundles its label setoid, ambient category and coherent
    object action. Morphisms are the existing transport-preserving functors;
    their equality retains prescribed-component natural isomorphisms.
    Native label and hom sizes are independent. Auxiliary bounds [l], [a]
    and [b] store category and action laws separately, without identifying
    carrier and equality universes. *)

(** * 指定对象呈现的范畴

    呈现捆绑标签广集、环境范畴及相干对象作用。态射为已有的保运输函子；
    其相等保留分量为指定运输的自然同构。原生标签及 Hom 大小相互独立；
    辅助界 [l]、[a] 和 [b] 分别存储范畴与作用定律，不识别载体与相等宇宙。 *)

Class VertexPresentation@{x e o h p l a b}
  :=
  (** Labels carry their specified Type-valued equality. *)

  (** 标签带有指定的 Type 值相等。 *)

  { vertex_labels : SetC@{x e}
  (** The ambient category retains independent object, hom and hom-equality
      sizes. Its laws are bounded separately by [l]. *)

  (** 环境范畴保留独立的对象、Hom 及 Hom 相等大小，其定律另以 [l] 为界。 *)

  ; vertex_ambient : Cat@{o h p l l}
  (** The unique coercion exposes the coherent object-action functor.
      Parallel label-equality witnesses act by equal transport arrows.
      Its respectfulness and composition-law bounds [a] and [b] are
      independent of the ambient category-law bound [l]. *)

  (** 唯一强制转换暴露相干对象作用函子；平行标签相等见证作用为相等运输箭头。
      其保相等与复合定律界 [a] 和 [b] 独立于环境范畴定律界 [l]。 *)

  ; vertex_action :> Fct@{x e Set e a b o h p l}
      (EqGpd@{x e e} vertex_labels) vertex_ambient
  }.

Arguments vertex_labels _ : clear implicits.
Arguments vertex_ambient _ : clear implicits.
Arguments vertex_action _ : clear implicits.

(** Bundle an existing action by copying its maps and checking its laws
    pointwise at the common bound. Input law universes stay independent. *)

(** 复制已有作用的映射，并在共同界中逐点检查其定律，从而捆绑该作用；输入的
    定律宇宙保持独立。 *)

Program Definition VertexPresentationOf@{x e o h p l a b q c d}
    {X : SetC@{x e}} {C : Cat@{o h p l l}}
    (T : Fct@{x e Set q c d o h p l} (EqGpd@{x e q} X) C)
  : VertexPresentation@{x e o h p l a b}
  :=
  {|vertex_labels := X
  ; vertex_ambient := C
  ; vertex_action :=
      {|F0 i := T i
      ; F1 i j f := fmap T f
      ; functor_fmap_proper i j f g H :=
          @functor_fmap_proper _ _ T i j f g H
      |}
  |}.
Next Obligation. exact (@functor_id _ _ T X0). Defined.
Next Obligation. exact (@functor_comp _ _ T X0 Y Z f g). Defined.

(** Presentations and their existing morphisms form a category. The
    native hom-setoid and all category laws reuse the vertex-functor theory;
    no equality of presentations, functions or proof fields is imposed. *)

(** 呈现及其已有态射构成范畴。原生 Hom 广集和全部范畴定律复用顶点函子理论，
    不要求呈现、函数或证明字段的相等。 *)

Program Canonical VertexPresentationCat@{x e o h p l a b +}
  : Cat
  :=
  {|Ob := VertexPresentation@{x e o h p l a b}
  ; HomSet P Q := VtxFctS P Q
  ; id P := VertexIdF P
  ; comp P Q R G F := G ∘Fᵥ F
  ; comp_proper P Q R := vertex_comp_proper
  |}.
Next Obligation. exact (vertex_comp_id_r f). Defined.
Next Obligation. exact (vertex_comp_id_l f). Defined.
Next Obligation. exact (vertex_comp_assoc f g h). Defined.

(** Repackage an existing presentation morphism between bundled actions.
    Maps are retained; pointwise laws avoid equating input proof universes
    with the category's common bounds. *)

(** 将已有呈现态射重新包装为捆绑作用之间的态射。保留映射，并逐点证明定律，
    避免将输入证明宇宙与范畴的共同界识别。 *)

Program Definition VertexPresentationMap@{x e o h p l a b +}
    {X Y : SetC@{x e}} {C D : Cat@{o h p l l}}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D} (F : T →ᵥ U)
  : VertexPresentationOf@{x e o h p l a b _ _ _} T →ᵥ
      VertexPresentationOf@{x e o h p l a b _ _ _} U
  :=
  {|vertex_functor :=
      {|F0 i := F i
      ; F1 i j f := fmap F f
      ; functor_fmap_proper i j f g H :=
          @functor_fmap_proper _ _ F i j f g H
      |}
  ; vertex_functor_ob_proper := vertex_functor_ob_proper F
  |}.
Next Obligation. exact (@functor_id _ _ F X0). Defined.
Next Obligation. exact (@functor_comp _ _ F X0 Y0 Z f g). Defined.
Next Obligation. exact (vertex_functor_transport F p). Defined.

(** Repackaging preserves prescribed-component comparisons, including
    their Type-valued label witnesses. *)

(** 重新包装保持指定分量比较，包括其 Type 值标签见证。 *)

Global Instance vertex_presentation_map_proper
    {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
  : Proper (VtxFctEq ==> VtxFctEq)
      (@VertexPresentationMap _ _ _ _ T U).
Proof. intros F G [e H]. exists e. intros i j f. exact (H i j f). Defined.

(** Repackaging sends the original identity to the bundled identity in
    prescribed comparison, without comparing the identity-law fields. *)

(** 重新包装在指定比较下将原恒等送到捆绑恒等，不比较恒等律字段。 *)

Lemma vertex_presentation_map_id {X : SetC} {C : Cat}
    (T : Fct (EqGpd X) C)
  : VtxFctEq (VertexPresentationMap (VertexIdF T))
      (VertexIdF (VertexPresentationOf T)).
Proof.
  exists (λ i, reflexivity (i : X)). intros i j f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** Repackaging commutes with composition in the same comparison. *)

(** 重新包装在同一比较下与复合交换。 *)

Lemma vertex_presentation_map_comp {X Y Z : SetC} {C D E : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {V : Fct (EqGpd Z) E} (G : U →ᵥ V) (F : T →ᵥ U)
  : VtxFctEq (VertexPresentationMap (G ∘Fᵥ F))
      (VertexPresentationMap G ∘Fᵥ VertexPresentationMap F).
Proof.
  exists (λ i, reflexivity (G (F i) : Z)). intros i j f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.
