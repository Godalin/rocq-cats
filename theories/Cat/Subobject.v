From Cats Require Import
  Cat.Core
  Cat.Pullback
  Cat.Morphism.

(** * Pullback Stability of Subobjects

    Work with a given pullback square in an arbitrary category. The
    monomorphism property is inherited by the opposite projection, without
    assuming a classifier or making choices of other pullbacks. *)

(** * 子对象的拉回稳定性

    在任意范畴中固定一个拉回方形；单态射的性质由对边投影继承，
    不假定分类子，也不为其他拉回作选择。 *)

(** Pulling back a monomorphism gives a monomorphism. *)

(** 单态射的拉回仍为单态射。 *)

Theorem pullback_mono {C : Cat} {X Y Z P : C}
    {f : Hom X Z} {g : Hom Y Z}
    {p1 : Hom P X} {p2 : Hom P Y}
    (HP : is_pullback f g P p1 p2)
    (Hg : is_mono g)
  : is_mono p1.
Proof.
  intros Q x y Hxy. apply (pullback_hom_ext HP x y).
  - exact Hxy.
  - apply Hg.
    rewrite <- !comp_assoc, <- (fst HP), !comp_assoc, Hxy.
    reflexivity.
Qed.

(** Bundle the first projection of the given square with its inherited
    monomorphism property. Its underlying arrow is unchanged. *)

(** 将给定方形的第一投影与继承的单态射性质组合；底层箭头保持原样。 *)

Program Definition PullbackMono {C : Cat} {X Y Z P : C}
    {f : Hom X Z} {m : Y ↣ Z}
    {p1 : Hom P X} {p2 : Hom P Y}
    (HP : is_pullback f m P p1 p2)
  : P ↣ X
  :=
  {|mor := p1
  |}.
Next Obligation.
  apply (pullback_mono HP). apply mor_mono.
Qed.

(** Replace the displayed subobject of a pullback by an equivalent one.
    Its comparison factors are inverse by monicity; transport the existing
    universal property along that isomorphism. *)

(** 将拉回中展示的子对象替换为等价子对象。比较因子由单态性互逆，
    沿此同构传递已有泛性质。 *)

Definition pullback_subobject {C : Cat} {X Y Z : C}
    {f : Hom X Z} {g : Hom Y Z} {i j : Sub X}
    {a : Hom i Y} (HP : is_pullback f g i i a)
    (H : i ~Sub j)
  : ∃ b : Hom j Y, is_pullback f g j j b.
Proof.
  destruct H as [[u Hu] [v Hv]].
  assert (Hv_iso : is_iso v).
  { exists u. split.
    - apply (sub_mono _ j).
      rewrite <- comp_assoc, <- Hu, <- Hv, comp_id_r. reflexivity.
    - apply (sub_mono _ i).
      rewrite <- comp_assoc, <- Hv, <- Hu, comp_id_r. reflexivity. }
  exists (a ∘ v).
  exact (pullback_iso v Hv_iso (symmetry Hv) (reflexivity _) HP).
Defined.

(** ** Chosen Subobject Inverse Images

    A chosen pullback gives an inverse image along every base arrow.
    Its universal property turns factorizations through the inverse image
    into factorizations after composition with the base arrow. *)

(** ** 选定的子对象逆像

    选定拉回给出沿每条基底箭头的逆像。拉回的泛性质将经过逆像的分解与
    沿基底箭头复合后的分解联系起来。 *)

Section SubobjectInverseImages.
Context {C : Cat} `{HP : !HasPullback C}.

(** Pull back the displayed subobject along the base map.

<<
    sX ------> sY
    v          v
    |          |
    |          s
    |          |
    v          v
    X ---f---> Y
>>
*)

(** 将 Y 的子对象 s 沿 f 拉回，得到 X 的子对象及其指向 s 的比较映射。 *)

Program Definition Sub_fmap {X Y : C}
    (f : Hom X Y) (sY : Sub Y)
  : Sub X
  :=
  {|sub := Pb f sY
  ; sub_mono := PullbackMono pullback_universal
  |}.

(** The chosen inverse-image subobject has the selected pullback as its
    domain. *)

(** 选定逆像子对象以指定拉回作为定义域。 *)

Proposition Sub_fmap_Ob {X Y : C}
    {f : Hom X Y} {r : Sub Y}
  : sub (Sub_fmap f r) = X ×[f,r] (sub r).
Proof. reflexivity. Qed.

(** A factor through an inverse image is exactly a factor of the composite
    through the original subobject. Both directions keep their arrows. *)

(** 经过逆像分解，恰好等价于复合后经过原子对象分解；两个方向均保留箭头。 *)

Definition sub_inverse_factor {X Y : C}
    (f : Hom X Y) (r : Sub X) (s : Sub Y)
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

Definition sub_inverse_le {X Y : C}
    (f : Hom X Y) {s t : Sub Y} (H : s ≲Sub t)
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

End SubobjectInverseImages.

Arguments Sub_fmap {_ H _ _} _ _ : rename.
Arguments Sub_fmap_Ob {_ H _ _ _ _} : rename.
