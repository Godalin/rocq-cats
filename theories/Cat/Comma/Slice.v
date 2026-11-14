From Cats Require Export
  Cat.Comma.Structured.
From Cats Require Import
  Cat.Slice.Core
  Cat.CatCat.

(** * Slices through Opposite Structured Arrows

    An arrow into [X] is a structured arrow out of [X] in the opposite
    category. The existing slice is equivalent to this opposite comma
    category; no independent dual comma construction is introduced. *)

(** * 通过反结构箭头刻画切片

    指向 [X] 的箭头就是反范畴中从 [X] 出发的结构箭头。已有切片等价于这个
    反逗号范畴，不另行定义独立的对偶逗号构造。 *)

Program Definition SliceCommaF (C : Cat) (X : @Ob C)
  : Fct (C /C X) ((X ↓[(@IdF (C^op))])^op)
  :=
  {|F0 A := @StructuredOb (C^op) (C^op) IdF X (slice_dom A)
      (slice_arrow A)
  ; F1 A B f :=
      {|comma_left := tt
      ; comma_right := slice_map f
      |}
  |}.
Next Obligation. rewrite comp_id_l. exact (slice_comm f). Defined.
Next Obligation. intros f g E. split; [exact tt | exact E]. Defined.
Next Obligation. split; [exact tt | reflexivity]. Defined.
Next Obligation. split; [exact tt | reflexivity]. Defined.

(** Read the opposite structured arrow as a slice object and triangle. *)

(** 将反结构箭头读作切片对象及交换三角形。 *)

Program Definition CommaSliceF (C : Cat) (X : @Ob C)
  : Fct ((X ↓[(@IdF (C^op))])^op) (C /C X)
  :=
  {|F0 A := {|slice_dom := comma_right_ob A
             ; slice_arrow := comma_arrow A
             |}
  ; F1 A B f := {|slice_map := comma_right f
                |}
  |}.
Next Obligation.
  pose proof (comma_comm f) as E. cbn in E.
  rewrite comp_id_l in E. exact E.
Defined.
Next Obligation. intros f g E. exact (snd E). Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** The slice round trip is compared by identity underlying maps. *)

(** 用底层恒等映射比较切片中的往返。 *)

Program Definition SliceCommaRoundtripN (C : Cat) (X : @Ob C)
  : (CommaSliceF C X ∘F SliceCommaF C X) ⇒ IdF
  :=
  {|nt A := {|slice_map := id
             |}
  |}.
Next Obligation. apply comp_id_r. Defined.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.

(** The reverse slice comparison uses the same underlying identity. *)

(** 切片的逆向比较使用同一底层恒等映射。 *)

Program Definition slice_comma_inverse (C : Cat) (X : @Ob C)
    (A : SliceOb C X)
  : (@Hom (C /C X)) A ((CommaSliceF C X ∘F SliceCommaF C X) A)
  :=
  {|slice_map := id
  |}.
Next Obligation. apply comp_id_r. Defined.

(** The slice round trip is naturally isomorphic to its identity. *)

(** 切片往返自然同构于其恒等函子。 *)

Definition slice_comma_roundtrip_iso (C : Cat) (X : @Ob C)
  : (CommaSliceF C X ∘F SliceCommaF C X) ≅N IdF.
Proof.
  exists (SliceCommaRoundtripN C X). intros A.
  exists (slice_comma_inverse C X A). split; apply comp_id_l.
Defined.

(** The comma round trip keeps a singleton side and an identity side. *)

(** 逗号范畴中的往返保留单元素侧边与恒等侧边。 *)

Program Definition CommaSliceRoundtripN (C : Cat) (X : @Ob C)
  : (SliceCommaF C X ∘F CommaSliceF C X) ⇒ IdF
  :=
  {|nt A := {|comma_left := tt
             ; comma_right := id
             |}
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.
Next Obligation.
  split; [exact tt |]. cbn. rewrite comp_id_l, comp_id_r. reflexivity.
Defined.

(** The reverse comma comparison retains the same two sides. *)

(** 逆向逗号比较保留同样两条侧边。 *)

Program Definition comma_slice_inverse (C : Cat) (X : @Ob C)
    (A : @Ob ((X ↓[(@IdF (C^op))])^op))
  : (@Hom ((X ↓[(@IdF (C^op))])^op)) A
      ((SliceCommaF C X ∘F CommaSliceF C X) A)
  :=
  {|comma_left := tt
  ; comma_right := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.

(** The comma round trip is naturally isomorphic to its identity. *)

(** 逗号范畴中的往返自然同构于其恒等函子。 *)

Definition comma_slice_roundtrip_iso (C : Cat) (X : @Ob C)
  : (SliceCommaF C X ∘F CommaSliceF C X) ≅N IdF.
Proof.
  exists (CommaSliceRoundtripN C X). intros A.
  exists (comma_slice_inverse C X A). split; split;
    [exact tt | apply comp_id_l | exact tt | apply comp_id_l].
Defined.

(** The existing slice and the opposite structured-arrow category are
    equivalent, including their chosen comparison transformations. *)

(** 已有切片与反结构箭头范畴等价，并保留选定比较自然变换。 *)

Definition slice_comma_equiv (C : Cat) (X : @Ob C)
  : (C /C X) ≃C ((X ↓[(@IdF (C^op))])^op)
  := (SliceCommaF C X; (CommaSliceF C X;
      (slice_comma_roundtrip_iso C X, comma_slice_roundtrip_iso C X))).
