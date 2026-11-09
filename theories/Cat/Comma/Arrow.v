From Cats Require Export
  Cat.Comma.Core.
From Cats Require Import
  Cat.Arrow.Core
  Cat.CatCat.

(** * The Arrow Category as a Comma Category

    Identity/identity comma objects and arrows encode the same squares as
    [Arr]. We compare the categories by functors and natural isomorphisms,
    without identifying their record representations. *)

(** * 箭头范畴作为逗号范畴

    恒等／恒等逗号范畴与 [Arr] 编码相同方形；通过函子和自然同构比较，不等同
    两种记录表示。 *)

Program Definition CommaArrowF (C : Cat)
  : Functor ((@IdF C) ↓C IdF) (Arr C)
  :=
  {|F0 X :=
     {|arrow_dom := comma_left_ob X
     ; arrow_cod := comma_right_ob X
     ; arrow_map := comma_arrow X
     |}
  ; F1 X Y f :=
      {|arrow_top := comma_left f
      ; arrow_bottom := comma_right f
      ; arrow_comm := symmetry (comma_comm f)
      |}
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. split; reflexivity. Defined.
Next Obligation. split; reflexivity. Defined.

(** Read an arrow-category square as an identity/identity comma square. *)

(** 将箭头范畴方形读作恒等／恒等逗号方形。 *)

Program Definition ArrowCommaF (C : Cat)
  : Functor (Arr C) ((@IdF C) ↓C IdF)
  :=
  {|F0 X :=
     {|comma_left_ob := arrow_dom X
     ; comma_right_ob := arrow_cod X
     ; comma_arrow := arrow_map X
     |}
  ; F1 X Y f :=
      {|comma_left := arrow_top f
      ; comma_right := arrow_bottom f
      ; comma_comm := symmetry (arrow_comm f)
      |}
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. split; reflexivity. Defined.
Next Obligation. split; reflexivity. Defined.

(** Identity side maps compare the comma round trip to its original object. *)

(** 恒等侧边比较逗号范畴中的往返对象与原对象。 *)

Program Definition CommaArrowRoundtripN (C : Cat)
  : (ArrowCommaF C ∘F CommaArrowF C) ⇒ IdF
  :=
  {|nt X := {|comma_left := id
             ; comma_right := id
             |}
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.
Next Obligation. split; cbn; rewrite comp_id_l, comp_id_r; reflexivity. Defined.

(** The reverse comparison keeps the same identity side maps. *)

(** 逆向比较使用同样的恒等侧边。 *)

Program Definition comma_arrow_inverse (C : Cat)
    (X : @Ob ((@IdF C) ↓C IdF))
  : (@Hom ((@IdF C) ↓C IdF)) X
      ((ArrowCommaF C ∘F CommaArrowF C) X)
  :=
  {|comma_left := id
  ; comma_right := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.

(** The comma round trip is naturally isomorphic to the identity. *)

(** 逗号范畴中的往返自然同构于恒等。 *)

Definition comma_arrow_roundtrip_iso (C : Cat)
  : (ArrowCommaF C ∘F CommaArrowF C) ≅N IdF.
Proof.
  exists (CommaArrowRoundtripN C). intros X.
  exists (comma_arrow_inverse C X). split; split; apply comp_id_l.
Defined.

(** Identity sides also compare the arrow-category round trip. *)

(** 恒等侧边也比较箭头范畴中的往返。 *)

Program Definition ArrowCommaRoundtripN (C : Cat)
  : (CommaArrowF C ∘F ArrowCommaF C) ⇒ IdF
  :=
  {|nt X := {|arrow_top := id
             ; arrow_bottom := id
             |}
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.
Next Obligation. split; cbn; rewrite comp_id_l, comp_id_r; reflexivity. Defined.

(** The reverse arrow-category comparison. *)

(** 箭头范畴中的逆向比较。 *)

Program Definition arrow_comma_inverse (C : Cat) (X : ArrowOb C)
  : (@Hom (Arr C)) X ((CommaArrowF C ∘F ArrowCommaF C) X)
  :=
  {|arrow_top := id
  ; arrow_bottom := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.

(** The arrow-category round trip is naturally isomorphic to the identity. *)

(** 箭头范畴中的往返自然同构于恒等。 *)

Definition arrow_comma_roundtrip_iso (C : Cat)
  : (CommaArrowF C ∘F ArrowCommaF C) ≅N IdF.
Proof.
  exists (ArrowCommaRoundtripN C). intros X.
  exists (arrow_comma_inverse C X). split; split; apply comp_id_l.
Defined.

(** The existing arrow category is equivalent to the identity comma category. *)

(** 已有箭头范畴等价于恒等逗号范畴。 *)

Definition comma_arrow_equiv (C : Cat)
  : ((@IdF C) ↓C IdF) ≃C Arr C
  := (CommaArrowF C; (ArrowCommaF C;
      (comma_arrow_roundtrip_iso C, arrow_comma_roundtrip_iso C))).
