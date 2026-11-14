From Cats Require Export
  Cat.Computational.Arrow.Pairing
  Cat.Monoidal.Functor.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Terminal
  Instance.Set.Product.

Local Open Scope computation_scope.
Local Open Scope monoidal_scope.

(** * Global Computations as a Lax Monoidal Functor

    Fix an Arrow from a value category with selected finite products into
    a computation category. Terminal-input computations form setoids; pure
    postcomposition and ordered pairing make them a lax monoidal functor.
    The result is setoid-valued, not generally an endofunctor on values. *)

(** * 全局计算作为 lax 幺半函子

    固定从选定有限积的值范畴进入计算范畴的 Arrow。终输入计算组成广集，纯
    后合成及有序配对使其成为 lax 幺半函子。结果为广集值函子，一般并非值
    范畴上的自函子。 *)

Section Global.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** Apply the existing covariant Hom functor at the pure terminal object,
    then precompose with the pure-arrow functor. Computation hom and equality
    sizes remain those of [K], independent of the value category. *)

(** 在纯终对象处使用已有协变 Hom 函子，再与纯箭头函子复合。计算 Hom 及相等
    大小保留 [K] 的层级，独立于值范畴。 *)

Definition ArrowGlobalF
  : Fct C SetCat
  := Hom(A 1,-) ∘F A.

(** Ordered fanout is a respectful pairing of terminal-input computations. *)

(** 有序 fanout 给出终输入计算的保相等配对。 *)

Program Definition arrow_global_pair (X Y : @Ob C)
  : (ArrowGlobalF X ×S ArrowGlobalF Y) →r ArrowGlobalF (X × Y)%ob
  := {|func fg := fst fg &&&[A] snd fg|}.
Next Obligation.
  intros [f g] [f' g'] [Hf Hg].
  apply arrow_fanout_proper; assumption.
Defined.

(** Pure result naturality supplies the tensorator. Derived tensor maps
    are compared with the chosen product maps before applying pairing laws. *)

(** 纯结果自然性给出 tensorator；先比较派生张量映射与选定积映射，再应用
    配对定律。 *)

Program Definition ArrowGlobalTensorN
  : (tensorF (@CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct)
      ∘F (ArrowGlobalF ×F ArrowGlobalF)) ⇒
      (ArrowGlobalF ∘F tensorF (@CartesianMonoidal C HT HP))
  := {|nt XY := arrow_global_pair (fst XY) (snd XY)|}.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g]. intros [u v].
  pose proof (@cartesian_tensor_map SetCat SetCat_HasTerminal
    SetCat_HasProduct _ _ _ _ (fmap ArrowGlobalF f)
    (fmap ArrowGlobalF g) (u,v)) as Ht.
  etransitivity.
  - exact (@func_proper _ _ (arrow_global_pair Y1 Y2) _ _ Ht).
  - change ((arr[A; f] ∘ u) &&&[A] (arr[A; g] ∘ v) ≈
      arr[A; @tensor_map C (@CartesianMonoidal C HT HP) _ _ _ _ f g] ∘
        (u &&&[A] v)).
    etransitivity; [symmetry; apply arrow_fanout_post |].
    apply comp_proper; [| reflexivity]. apply functor_fmap_proper.
    symmetry. apply cartesian_tensor_map.

Defined.

(** Pure identity is the global unit computation. *)

(** 纯恒等为全局单位计算。 *)

Program Definition arrow_global_unit
  : UnitS →r ArrowGlobalF 1
  := {|func _ := @id (A 1)|}.
Next Obligation. intros x y H. reflexivity. Defined.

(** The terminal-input Hom functor is lax monoidal from values to setoids.
    Unit and associativity diagrams are precisely the general pairing laws;
    no internal representation of the hom-setoids is assumed. *)

(** 终输入 Hom 函子是从值到广集的 lax 幺半函子。单位及结合图恰为一般配对律，
    不假设这些 Hom 广集可在值范畴内部表示。 *)

Program Definition ArrowGlobalLax
  : LaxMonoidalFct (@CartesianMonoidal C HT HP)
      (@CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct)
  := {|LaxMonoidalF := ArrowGlobalF
     ; lax_unit := arrow_global_unit
     ; lax_tensorN := ArrowGlobalTensorN|}.
Next Obligation.
  intros [u f].
  change (arr[A; (π2 : Hom (1 × X) X)] ∘ ((@id (A 1)) &&&[A] f) ≈ f).
  apply arrow_fanout_unit_l.
Defined.
Next Obligation.
  intros [f u].
  change (arr[A; (π1 : Hom (X × 1) X)] ∘ (f &&&[A] (@id (A 1))) ≈ f).
  apply arrow_fanout_unit_r.
Defined.
Next Obligation.
  intros [[f g] h].
  change (arr[A; (@product_assoc C HP X Y Z).1] ∘
    ((f &&&[A] g) &&&[A] h) ≈ f &&&[A] (g &&&[A] h)).
  apply arrow_fanout_assoc.
Defined.

End Global.
