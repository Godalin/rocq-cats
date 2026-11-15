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

Theorem pullback_mono {C : Cat} {X Y Z P : @Ob C}
    {f : Hom X Z} {g : Hom Y Z}
    {p1 : Hom P X} {p2 : Hom P Y}
    (HP : is_pullback f g P p1 p2) (Hg : is_mono g)
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

Program Definition PullbackMono {C : Cat} {X Y Z P : @Ob C}
    {f : Hom X Z} {m : Y ↣ Z}
    {p1 : Hom P X} {p2 : Hom P Y}
    (HP : is_pullback f m P p1 p2)
  : P ↣ X
  :=
  {|mor := p1
  |}.
Next Obligation. apply (pullback_mono HP). apply mor_mono. Qed.

(** Replace the displayed subobject of a pullback by an equivalent one.
    Its comparison factors are inverse by monicity; transport the existing
    universal property along that isomorphism. *)

(** 将拉回中展示的子对象替换为等价子对象。比较因子由单态性互逆，
    沿此同构传递已有泛性质。 *)

Definition pullback_subobject {C : Cat} {X Y Z : @Ob C}
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
