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

(** A fixed label setoid can carry different ambient categories and
    coherent actions. This component stores each category and action once;
    it never replaces the label equality or selects a global model. *)

(** 固定标签广集可以带有不同的环境范畴及相干作用。这个组件将每个范畴及作用
    各保存一次，不替换标签相等，也不全局选定模型。 *)

Minks.Mixin HasVtxAction@{x e o h p l a b} (X : SetC@{x e})
  :=
  { vertex_ambient : Cat@{o h p l l}
  ; vertex_action :> Fct@{x e Set e a b o h p l}
      (EqGpd@{x e e} X) vertex_ambient
  }.

Arguments vertex_ambient {_} _.
Arguments vertex_action {_} _.

(** The complete presentation reuses its native label setoid. Its callable
    view is the stored action through [hasVtxAction]; the ambient category
    remains explicit, avoiding a second competing object-type view. *)

(** 完整呈现复用原生标签广集；可调用视图通过 [hasVtxAction] 读取保存的作用。
    环境范畴保持显式，避免引入第二条相互竞争的对象类型视图。 *)

Minks.Struct VtxPresentation@{x e o h p l a b}
  extends SetC@{x e}
  with  hasVtxAction as hasVtxAction : HasVtxAction@{x e o h p l a b}.

Coercion hasVtxAction : VtxPresentation >-> HasVtxAction.

(** Bundle an existing action by copying its maps and checking its laws
    pointwise at the common bound. Input law universes stay independent. *)

(** 复制已有作用的映射，并在共同界中逐点检查其定律，从而捆绑该作用；输入的
    定律宇宙保持独立。 *)

Program Definition VtxPresentationOf@{x e o h p l a b q c d}
    {X : SetC@{x e}} {C : Cat@{o h p l l}}
    (T : Fct@{x e Set q c d o h p l} (EqGpd@{x e q} X) C)
  : VtxPresentation@{x e o h p l a b}
  := MakeVtxPresentation X
    {|vertex_ambient := C
    ; vertex_action :=
        {|fobj i := T i
        ; fmap i j f := fmap T f
        ; isFct :=
            {|fmap_proper i j f g H :=
                @fmap_proper _ _ _ _ (isFct T) i j f g H
            ; fmap_id := _
            ; fmap_comp := _
            |}
        |}
    |}.
Next Obligation. exact (@fmap_id _ _ _ _ (isFct T) X0). Qed.
Next Obligation. exact (@fmap_comp _ _ _ _ (isFct T) X0 Y Z f g). Qed.

(** Presentations and their existing morphisms form a category. The
    native hom-setoid and all category laws reuse the vertex-functor theory;
    no equality of presentations, functions or proof fields is imposed. *)

(** 呈现及其已有态射构成范畴。原生 Hom 广集和全部范畴定律复用顶点函子理论，
    不要求呈现、函数或证明字段的相等。 *)

Program Canonical VtxPresentationCat@{x e o h p l a b +}
  : Cat
  :=
  {|Ob := VtxPresentation@{x e o h p l a b}
  ; HomSet P Q := VtxFctS P Q
  ; id P := VtxIdF P
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

Program Definition VtxPresentationMap@{x e o h p l a b +}
    {X Y : SetC@{x e}} {C D : Cat@{o h p l l}}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D} (F : T →ᵥ U)
  : VtxPresentationOf@{x e o h p l a b _ _ _} T →ᵥ
      VtxPresentationOf@{x e o h p l a b _ _ _} U
  := MakeVtxFct
    {|fobj i := F i
    ; fmap i j f := fmap F f
    ; isFct :=
        {|fmap_proper i j f g H :=
            @fmap_proper _ _ _ _ (isFct F) i j f g H
        ; fmap_id := _
        ; fmap_comp := _
        |}
    |}
    {|vertex_fct_ob_proper := vertex_fct_ob_proper (isVtxFct F)
    ; vertex_fct_transport := _
    |}.
Next Obligation. exact (@fmap_id _ _ _ _ (isFct F) X0). Defined.
Next Obligation. exact (@fmap_comp _ _ _ _ (isFct F) X0 Y0 Z f g). Defined.
Next Obligation. exact (vertex_fct_transport (isVtxFct F) p). Defined.

(** Repackaging preserves prescribed-component comparisons, including
    their Type-valued label witnesses. *)

(** 重新包装保持指定分量比较，包括其 Type 值标签见证。 *)

Global Instance vertex_presentation_map_proper
    {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
  : Proper (VtxFctEq ==> VtxFctEq)
      (@VtxPresentationMap _ _ _ _ T U).
Proof. intros F G [e H]. exists e. intros i j f. exact (H i j f). Defined.

(** Repackaging sends the original identity to the bundled identity in
    prescribed comparison, without comparing the identity-law fields. *)

(** 重新包装在指定比较下将原恒等送到捆绑恒等，不比较恒等律字段。 *)

Lemma vertex_presentation_map_id {X : SetC} {C : Cat}
    (T : Fct (EqGpd X) C)
  : VtxFctEq (VtxPresentationMap (VtxIdF T))
      (VtxIdF (VtxPresentationOf T)).
Proof.
  exists (λ i, reflexivity (i : X)). intros i j f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** Repackaging commutes with composition in the same comparison. *)

(** 重新包装在同一比较下与复合交换。 *)

Lemma vertex_presentation_map_comp {X Y Z : SetC} {C D E : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {V : Fct (EqGpd Z) E} (G : U →ᵥ V) (F : T →ᵥ U)
  : VtxFctEq (VtxPresentationMap (G ∘Fᵥ F))
      (VtxPresentationMap G ∘Fᵥ VtxPresentationMap F).
Proof.
  exists (λ i, reflexivity (G (F i) : Z)). intros i j f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.
