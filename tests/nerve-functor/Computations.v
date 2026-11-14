From Cats Require Import
  Instance.Set.Simplicial.Vertex.Category
  Instance.Set.Simplicial.Vertex.Monoid
  Instance.Bool.Group
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

Local Open Scope nat_scope.

(** * Computing through the Fully Faithful Nerve Functor

    Identity images and chosen preimages must retain the nonidentity xor
    loop, even after bundling and extracting the fullness witness. *)

(** * 穿过全忠实 nerve 函子进行计算

    恒等像及选定原像须保留异或群的非恒等环路，即使经过捆绑及满性见证提取。 *)

(** Bundle the existing singleton-labelled boolean action. *)

(** 捆绑已有的带单元素标签布尔作用。 *)

Definition BooleanPresentation
  : VertexPresentation@{Set Set Set Set Set Set Set Set}
  := VertexPresentationOf (MonoidObjF BoolS (HM := BoolS_Monoid)).

(** All values remain at the small carrier and equality levels. *)

(** 全部值保留在小载体及相等层级。 *)

Definition BooleanNerveFunctor
  : Fct
      VertexPresentationCat@{Set Set Set Set Set Set Set Set _ _ _ _ _ _ _ _ _ _}
      (FctCat (Δ^op) SetCat@{Set Set _ _ _ _ _})
  := VertexNerveF.

(** The general full-faithfulness proof specializes without new choices. *)

(** 通用全忠实性证明在特化时不引入新选择。 *)

Definition BooleanNerveFullyFaithful
  : is_fully_faithful BooleanNerveFunctor
  := vertex_nerve_fully_faithful.

(** Existing unbundled maps enter the new category without changing arrows. *)

(** 已有未捆绑映射进入新范畴时不改变箭头。 *)

Definition BooleanIdentity
  : (@Hom VertexPresentationCat) BooleanPresentation BooleanPresentation
  := VertexPresentationMap
      (VertexIdF (MonoidObjF BoolS (HM := BoolS_Monoid))).

Example bundled_existing_map_computes
  : fmap BooleanIdentity
      (true : (@Hom (VertexCat BooleanPresentation)) tt tt) = true.
Proof. reflexivity. Qed.

(** The image of the presentation identity computes on a nonidentity edge. *)

(** 呈现恒等的像可在非恒等边上计算。 *)

Example nerve_identity_computes
  : let P := BooleanPresentation in
    let e := △₁[P; tt; tt] true in
    fmap (lower (fmap BooleanNerveFunctor
      (@Cats.Cat.Core.id VertexPresentationCat P) 1 e))
      (ordinal_step fin_first) = true.
Proof. reflexivity. Qed.

(** Fullness returns an actual presentation morphism with a computable
    arrow map, rather than an opaque existence witness. *)

(** 满性返回实际的呈现态射及其可计算箭头映射，而非不透明存在见证。 *)

Example nerve_fullness_preimage_computes
  : fmap (fst BooleanNerveFullyFaithful
      BooleanPresentation BooleanPresentation idN).1
      (true : (@Hom (VertexCat BooleanPresentation)) tt tt) = true.
Proof. reflexivity. Qed.
