From Cats.Set Require Import
  Subset.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Groupoid.Core.

(** * The Core Groupoid of a Category

    Keep all objects and retain only invertible arrows, including their
    chosen inverse data. Equality is the original hom equality, without
    comparing inverse witnesses. All operations reuse the existing
    isomorphism theory. *)

(** * 范畴的核心群胚

    保留全部对象，仅保留可逆态射及其选定逆数据。相等沿用原 Hom 相等，
    不比较逆见证；所有运算复用已有同构理论。 *)

(** The core keeps the same object type, so clients name its ambient
    category explicitly instead of selecting it by the object type alone. *)

(** 核心沿用相同对象类型，客户端须显式指定环境范畴，不只凭对象类型选取。 *)

Program Definition CoreCat (C : Cat)
  : Cat
  :=
  {|Ob := @Ob C
  ; HomSet X Y := SubsetS (HomSet X Y) (@is_iso C X Y)
  ; id X := @iso_refl C X
  ; comp X Y Z g f := iso_trans f g
  |}.
Next Obligation.
  intros f f' Hf g g' Hg.
  exact (@comp_proper C _ _ _ f.1 f'.1 Hf g.1 g'.1 Hg).
Defined.
Next Obligation. exact (@comp_id_r C _ _ f.1). Defined.
Next Obligation. exact (@comp_id_l C _ _ f.1). Defined.
Next Obligation. exact (@comp_assoc C _ _ _ _ f.1 g.1 h.1). Defined.

(** Invert each retained isomorphism using its stored inverse. *)

(** 使用保存的逆反转每个保留的同构。 *)

Program Definition CoreCat_IsGpd (C : Cat)
  : IsGpd (CoreCat C)
  :=
  {|gpd_iso X Y f := (iso_symm f; f.2.2)
  |}.

(** Bundle the same category and its derived inverse witnesses. *)

(** 打包同一范畴及其导出的逆见证。 *)

Definition CoreGpd (C : Cat)
  : Gpd
  := GpdOfCat (CoreCat C) (CoreCat_IsGpd C).

(** Forget invertibility evidence and retain the original arrow. *)

(** 忘掉可逆性证据，保留原态射。 *)

Program Definition CoreInclusionF (C : Cat)
  : Fct (CoreCat C) C
  :=
  {|fobj X := X
  ; fmap X Y f := f.1
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros f g H. exact H. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** Inclusion reflects exactly the specified arrow equality. *)

(** 嵌入恰好反映指定的态射相等。 *)

Lemma core_inclusion_faithful (C : Cat)
  : is_faithful (CoreInclusionF C).
Proof. intros X Y f g H. exact H. Defined.
