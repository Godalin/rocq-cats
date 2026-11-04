From Cats Require Import
  Algebra.Monoid.Action
  Algebra.Group.Category
  Cat.Core
  Cat.Functor.Core
  Cat.Groupoid.Core
  Cat.Groupoid.Functor
  Instance.Set.Core
  Instance.Bool.Group.

(** * A Non-Thin Groupoid and Its Boolean Action *)

(** * 非薄群胚及其布尔作用 *)

Local Existing Instance BoolS_Group.

(** The one-object category of the xor group retains two distinct loops. *)

(** 异或群的单对象范畴保留两条不同的环路。 *)

Definition BoolGroupoid
  : Cat
  := B(BoolS).

(** Explicitly enable the groupoid structure inherited from the xor group. *)

(** 显式启用从异或群继承的群胚结构。 *)

Definition BoolGroupoid_IsGroupoid
  : BoolGroupoid ⦂ Gpd
  := MonoidCat_IsGroupoid BoolS.

(** The nonidentity loop of the boolean groupoid. *)

(** 布尔群胚的非恒等环路。 *)

Definition bool_loop
  : (@Hom BoolGroupoid) tt tt
  := true.

(** The two loops remain distinct under the specified categorical equality. *)

(** 两条环路在指定的范畴相等下仍不同。 *)

Lemma bool_loop_not_id
  : bool_loop ≉ @Cats.Cat.Core.id BoolGroupoid tt.
Proof. intros H. discriminate H. Qed.

(** The regular action specializes the generic covariant hom construction. *)

(** 正则作用直接实例化通用的协变 Hom 构造。 *)

Definition BoolActionF
  : Functor BoolGroupoid SetCat
  := RegularActionF BoolS.

(** Faithfulness follows from the general regular-action argument. *)

(** 忠实性直接来自一般正则作用论证。 *)

Definition bool_action_faithful
  : is_faithful BoolActionF
  := regular_action_faithful BoolS.

(** The nonidentity loop swaps boolean elements. *)

(** 非恒等环路交换布尔元素。 *)

Lemma bool_action_loop (b : bool)
  : fmap BoolActionF bool_loop b ≈S negb b.
Proof. destruct b; reflexivity. Qed.

(** This transport is not the identity map in the set category. *)

(** 此运输在集合范畴中不是恒等映射。 *)

Lemma bool_action_not_id
  : ¬ (fmap BoolActionF bool_loop ≈ id_resp).
Proof. intros H. specialize (H false). discriminate H. Qed.

(** Invertibility of the action is inherited from functoriality out of a
    groupoid; no separate permutation or inverse proof is needed. *)

(** 作用的可逆性由源于群胚的函子性继承，无需单独证明置换或构造逆。 *)

Definition bool_action_loop_iso
  : is_iso (fmap BoolActionF bool_loop)
  := groupoid_fmap_iso (HC := BoolGroupoid_IsGroupoid) BoolActionF bool_loop.

(** Applying the loop twice is the identity, by the original inverse laws. *)

(** 由原有互逆定律，环路作用两次即为恒等。 *)

Lemma bool_action_loop_twice (b : bool)
  : fmap BoolActionF bool_loop (fmap BoolActionF bool_loop b) ≈S b.
Proof. exact (fst bool_action_loop_iso.2 b). Qed.
