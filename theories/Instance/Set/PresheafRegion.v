From Cats Require Export
  Instance.Set.PresheafDescent
  Cat.Pushout.
From Cats Require Import
  Cat.Morphism
  Cat.Core.
From Cats.Set Require Export
  Subset.

(** * Regions of Arbitrary Presheaves

    A region retains membership data, invariant under the presheaf's
    specified equality and closed under restriction. Its realization
    inherits exactly that equality, ignoring the membership witnesses.
    Unlike a sieve, the ambient presheaf need not be representable.

    Region unions are formed with a retained alternative and intersections
    with a retained pair. Their gluing uses
    %\coqref{Cats.Instance.Set.PresheafDescent.PresheafDescendN}
    {%[PresheafDescendN]%}%; it will provide a reusable prerequisite for
    actual triangle-horn stage presheaves and attachment squares. *)

(** * 任意预层的区域

    区域保留隶属数据，在预层的指定相等下不变，并在限制下封闭。其实现恰好
    继承该相等，忽略隶属见证。与筛不同，环境预层无需可表。

    区域的并保留一个分支，交保留一对见证。粘合复用
    %\coqref{Cats.Instance.Set.PresheafDescent.PresheafDescendN}
    {%[PresheafDescendN]%}%，作为实际三角 horn 阶段预层及附着方形的通用前置。 *)

(** Membership and its laws form one interface on the supplied ambient
    presheaf. The membership universe is independent of value equality. *)

(** 隶属及其定律在给定环境预层上组成一个接口；隶属宇宙与取值相等独立。 *)

Class PresheafRegion {C : Cat} (Q : Fct (C^op) SetCat)
  :=
  { region_member {X : @Ob C} : Q X → Type

  (** Specified-equal values transport membership in both directions. *)

  (** 指定相等的值在两个方向上运输隶属。 *)

  ; region_member_proper {X}
    :: Proper (carrier_equiv (Q X) ==> iffT) (@region_member X)

  (** Restriction retains an actual witness in the same region. *)

  (** 限制保留同一区域中的实际见证。 *)

  ; region_precomp {X Y} (f : (@Hom C) Y X) (x : Q X)
    : region_member x → region_member (fmap Q f x)
  }.

Arguments region_member {_ _} _ {_} _.
Arguments region_member_proper {_ _} _ {_} _ _ _.
Arguments region_precomp {_ _} _ {_ _} _ _ _.

(** ** Realization and Maps

    Fix independent value carrier/equality bounds and an ambient presheaf.
    Realization requires its carrier bound to contain the membership data;
    no resizing or equality of membership witnesses is used. *)

(** ** 实现及映射

    固定独立的取值载体／相等界及环境预层。实现要求载体界容纳隶属数据，
    不使用大小重设或隶属见证相等。 *)

Section Regions.
Universes u p.
Context {C : Cat} {Q : Fct (C^op) SetCat@{u p _ _ _ _ _}}.

(** Realize the region by the existing setoid subset in each degree. *)

(** 在每维使用已有广集子集实现区域。 *)

Program Definition RegionPsh (R : PresheafRegion Q)
  : Fct (C^op) SetCat@{u p _ _ _ _ _}
  :=
  {|fobj X := SubsetS (Q X) (region_member R)
  ; fmap X Y f :=
      {|func x := (fmap Q f x.1; region_precomp R f x.1 x.2)
      |}
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros x y E. exact (@func_proper _ _ (fmap Q f) _ _ E). Defined.
Next Obligation.
  intros f g E x. exact (fmap_proper (IsFct := isFct Q) f g E x.1).
Defined.
Next Obligation. intros x. exact (fmap_id (IsFct := isFct Q) x.1). Defined.
Next Obligation. intros x. exact (fmap_comp (IsFct := isFct Q) f g x.1). Defined.

(** Forget membership by the original respectful subset inclusion. *)

(** 通过原保相等子集包含忘却隶属。 *)

Program Definition RegionInclusionN (R : PresheafRegion Q)
  : RegionPsh R ⇒ Q
  :=
  {|nt X := subset_inclusion_resp
  |}.
Next Obligation. intros x. reflexivity. Qed.

(** Containment changes only membership, retaining the underlying value. *)

(** 包含关系只改变隶属，保留底层值。 *)

Program Definition RegionMapN {R : PresheafRegion Q} {S : PresheafRegion Q}
    (H : ∀ (X : @Ob C) (x : Q X), region_member R x → region_member S x)
  : RegionPsh R ⇒ RegionPsh S
  :=
  {|nt X :=
      {|func x := (x.1; H X x.1 x.2)
      |}
  |}.
Next Obligation. intros x y E. exact E. Defined.
Next Obligation.
  intros x. change (fmap Q f x.1 ≈S fmap Q f x.1). reflexivity.
Defined.

(** Containment commutes with the two inclusions in specified equality. *)

(** 包含关系按指定相等与两个包含映射交换。 *)

Definition region_map_comm {R : PresheafRegion Q} {S : PresheafRegion Q}
    (H : ∀ (X : @Ob C) (x : Q X), region_member R x → region_member S x)
  : (RegionInclusionN S ∘Nv RegionMapN H) ≈N RegionInclusionN R.
Proof. intros X x. reflexivity. Defined.

(** The realized inclusion is monic without comparing membership records. *)

(** 实现后的包含是单态射，无需比较隶属记录。 *)

Definition region_inclusion_mono (R : PresheafRegion Q)
  : @is_mono (FctCat (C^op) SetCat@{u p _ _ _ _ _}) _ _ (RegionInclusionN R).
Proof. intros P α β E X x. exact (E X x). Defined.

(** A given map whose values belong to the region lifts transparently. *)

(** 给定映射若取值属于区域，则透明地提升到该区域。 *)

Program Definition RegionFactorN {P : Fct (C^op) SetCat@{u p _ _ _ _ _}}
    (R : PresheafRegion Q) (α : P ⇒ Q)
    (H : ∀ X x, region_member R (α X x))
  : P ⇒ RegionPsh R
  :=
  {|nt X := subset_pair_resp (α X) (H X)
  |}.
Next Obligation. intros x. exact (nat_naturality α f x). Qed.

(** The lift has exactly the given underlying map. *)

(** 提升的底层映射恰为给定映射。 *)

Definition region_factor_comm {P : Fct (C^op) SetCat@{u p _ _ _ _ _}}
    (R : PresheafRegion Q) (α : P ⇒ Q)
    (H : ∀ X x, region_member R (α X x))
  : (RegionInclusionN R ∘Nv RegionFactorN R α H) ≈N α.
Proof. intros X x. reflexivity. Defined.

(** ** Intersections and Unions

    Fix two regions of this same ambient presheaf. Only their membership
    data change; all realized equalities still use the underlying values. *)

(** ** 交及并

    固定同一环境预层的两个区域；只有隶属数据改变，实现的相等仍使用底层值。 *)

Context (R : PresheafRegion Q).
Context (S : PresheafRegion Q).

(** An intersection retains both membership witnesses. *)

(** 交保留两份隶属见证。 *)

Program Definition RegionIntersection
  : PresheafRegion Q
  :=
  {|region_member X x := (region_member R x * region_member S x)%type
  ; region_precomp X Y f x H :=
      (region_precomp R f x (fst H), region_precomp S f x (snd H))
  |}.
Next Obligation.
  intros x y E. split; intros [H K]; split.
  - exact (fst (region_member_proper R x y E) H).
  - exact (fst (region_member_proper S x y E) K).
  - exact (snd (region_member_proper R x y E) H).
  - exact (snd (region_member_proper S x y E) K).
Defined.

(** A union retains which region supplied its witness. *)

(** 并保留提供见证的区域分支。 *)

Program Definition RegionUnion
  : PresheafRegion Q
  :=
  {|region_member X x := (region_member R x + region_member S x)%type
  ; region_precomp X Y f x H := match H with
      | inl K => inl (region_precomp R f x K)
      | inr K => inr (region_precomp S f x K)
      end
  |}.
Next Obligation.
  intros x y E. split; intros [H | H].
  - left. exact (fst (region_member_proper R x y E) H).
  - right. exact (fst (region_member_proper S x y E) H).
  - left. exact (snd (region_member_proper R x y E) H).
  - right. exact (snd (region_member_proper S x y E) H).
Defined.

(** The two projections only forget one intersection witness. *)

(** 两个投影仅忘却一份交的见证。 *)

Definition RegionInterLeftN
  : RegionPsh RegionIntersection ⇒ RegionPsh R
  := RegionMapN (R := RegionIntersection) (S := R) (λ X x H, fst H).

(** The second projection preserves the same underlying value. *)

(** 第二投影保留同一底层值。 *)

Definition RegionInterRightN
  : RegionPsh RegionIntersection ⇒ RegionPsh S
  := RegionMapN (R := RegionIntersection) (S := S) (λ X x H, snd H).

(** Include the left region using its retained branch. *)

(** 使用保留的左分支包含左区域。 *)

Definition RegionUnionLeftN
  : RegionPsh R ⇒ RegionPsh RegionUnion
  := RegionMapN (R := R) (S := RegionUnion) (λ X x H, inl H).

(** Include the right region using its retained branch. *)

(** 使用保留的右分支包含右区域。 *)

Definition RegionUnionRightN
  : RegionPsh S ⇒ RegionPsh RegionUnion
  := RegionMapN (R := S) (S := RegionUnion) (λ X x H, inr H).

End Regions.
