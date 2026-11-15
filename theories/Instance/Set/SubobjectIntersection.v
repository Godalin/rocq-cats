From Cats Require Import
  Cat.Core
  Cat.Morphism
  Cat.Pullback
  Cat.SubobjectIntersection
  Instance.Set.Subobject.

(** * Inverse Images Preserve Finite Intersections

    Work in an arbitrary category with a named pullback choice. The
    existing subobject inverse image preserves largest subobjects and
    binary intersections. These are equivalences of subobjects, retaining
    comparison factors; no classifier, CCC or ETCS axioms are required. *)

(** * 逆像保持有限交

    在具有具名拉回选择的任意范畴中，既有子对象逆像保持最大子对象及二元交。
    这些是保留比较因子的子对象等价，不要求分类子、CCC 或 ETCS 公理。 *)

Section InverseImage.
Context {C : Cat} `{HP : !HasPullback C}.

(** A factor through an inverse image is exactly a factor of the composite
    through the original subobject. Both directions keep their arrows. *)

(** 经过逆像分解，恰好等价于复合后经过原子对象分解；两个方向均保留箭头。 *)

Definition sub_inverse_factor {X Y} (f : Hom X Y)
    (r : Sub X) (s : Sub Y)
  : r ≲Sub Sub_fmap f s ↔ is_factored_through s (f ∘ r).
Proof.
  split.
  - intros [k Hk].
    change (r ≈ pb1 f s ∘ k) in Hk.
    exists (pb2 f s ∘ k).
    rewrite Hk, <- comp_assoc, pullback_comm, comp_assoc.
    reflexivity.
  - intros [k Hk]. exists (pb r k Hk).
    simpl. symmetry. apply pb_β1.
Defined.

(** Inverse image preserves subobject inclusion with its chosen
    factorization witness. *)

(** 逆像保持子对象包含关系及其选定分解见证。 *)

Definition sub_inverse_le {X Y} (f : Hom X Y) {s t : Sub Y}
    (H : s ≲Sub t)
  : Sub_fmap f s ≲Sub Sub_fmap f t.
Proof.
  apply (snd (sub_inverse_factor f (Sub_fmap f s) t)).
  destruct H as [a Ha]. exists (a ∘ pb2 f s).
  simpl. transitivity (s ∘ pb2 f s).
  - apply pullback_comm.
  - transitivity ((t ∘ a) ∘ pb2 f s).
    + apply comp_proper; [exact Ha | reflexivity].
    + apply comp_assoc.
Defined.

(** The largest subobject pulls back to the largest subobject, up to the
    specified mutual-factorization equality. *)

(** 最大子对象的拉回按指定的相互分解相等仍为最大子对象。 *)

Definition sub_inverse_top {X Y} (f : Hom X Y)
  : Sub_fmap f id_Sub ~Sub id_Sub.
Proof.
  split; [apply sub_top |].
  apply (snd (sub_inverse_factor f id_Sub id_Sub)).
  exists f. simpl. rewrite comp_id_l, comp_id_r. reflexivity.
Defined.

(** Pullback preserves the intersection universal property: a lower
    bound of the two inverse images factors through the inverse image of
    the intersection, and conversely. *)

(** 拉回保持交的泛性质：两个逆像的共同下界经过交的逆像分解，反之亦然。 *)

Definition sub_inverse_intersection {X Y} (f : Hom X Y) (s t : Sub Y)
  : Sub_fmap f (s ∩Sub t) ~Sub Sub_fmap f s ∩Sub Sub_fmap f t.
Proof.
  split.
  - apply (snd (sub_intersection_universal
      (Sub_fmap f s) (Sub_fmap f t) (Sub_fmap f (s ∩Sub t)))).
    split; apply sub_inverse_le;
      [apply sub_intersection_left | apply sub_intersection_right].
  - apply (snd (sub_inverse_factor f
      (Sub_fmap f s ∩Sub Sub_fmap f t) (s ∩Sub t))).
    apply (snd (sub_intersection_factor s t
      (f ∘ (Sub_fmap f s ∩Sub Sub_fmap f t)))).
    split.
    + apply (fst (sub_inverse_factor f _ s)).
      apply sub_intersection_left.
    + apply (fst (sub_inverse_factor f _ t)).
      apply sub_intersection_right.
Defined.

End InverseImage.
