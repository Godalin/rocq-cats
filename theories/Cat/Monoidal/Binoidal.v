From Cats Require Export
  Cat.Monoidal.Core
  Cat.Binoidal.Center.

Local Open Scope monoidal_scope.

(** * Monoidal Categories as Binoidal Categories

    A genuine bifunctor provides separately functorial context actions.
    Its interchange law makes every arrow central. This is an explicit
    adapter, not a competing parent view of the monoidal structure. *)

(** * 幺半范畴作为双侧张量范畴

    真正的双函子给出分别具有函子性的上下文作用，其交换律使每个态射都是
    中心态射。这是显式适配器，不是幺半结构的另一竞争父视图。 *)

Section Monoidal.
Context {C : Cat} `{MC : !MonoidalCat C}.

(** Reuse the same object tensor, fixing one identity arrow at a time. *)

(** 复用同一对象张量，每次固定一侧恒等态射。 *)

Program Definition MonoidalBinoidal
  : BinoidalCat C
  :=
  {|binoidal_tensor X Y := X ⊗ Y
  ; binoidal_left X Y Z f := id ⊗m f
  ; binoidal_right X Y Z f := f ⊗m id
  |}.
Next Obligation. intros f g H. rewrite H. reflexivity. Defined.
Next Obligation. intros f g H. rewrite H. reflexivity. Defined.
Next Obligation. apply tensor_map_id. Defined.
Next Obligation. apply tensor_map_id. Defined.
Next Obligation.
  rewrite <- tensor_map_comp, comp_id_l. reflexivity.
Defined.
Next Obligation.
  rewrite <- tensor_map_comp, comp_id_l. reflexivity.
Defined.

(** Both execution orders agree by bifunctoriality. No new assumptions
    are imposed on the original monoidal category. *)

(** 由双函子性，两种执行次序相等，不对原幺半范畴增加新前提。 *)

Definition monoidal_arrow_central {X Y : @Ob C} (f : Hom X Y)
  : @is_central C MonoidalBinoidal X Y f.
Proof.
  intros Z W g. split.
  - change ((f ⊗m @id W) ∘ (@id X ⊗m g) ≈
      (@id Y ⊗m g) ∘ (f ⊗m @id Z)).
    rewrite <- !tensor_map_comp, !comp_id_l, !comp_id_r. reflexivity.
  - change ((@id W ⊗m f) ∘ (g ⊗m @id X) ≈
      (g ⊗m @id Y) ∘ (@id Z ⊗m f)).
    rewrite <- !tensor_map_comp, !comp_id_l, !comp_id_r. reflexivity.
Defined.

End Monoidal.
