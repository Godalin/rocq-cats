From Cats Require Import
  Cat.Core
  Cat.CCC
  Cat.Monoidal.Core
  Cat.Groupoid.Core
  Cat.Groupoid.Preorder
  Instance.Set.Core
  Instance.Set.Groupoid
  Instance.Bool.Group
  Instance.Bool.Action.

(** * Bundled Groupoid Interfaces

    Check dependent objects, inherited inverses and the unique category view.
    Merely importing a concrete model must not choose an unrelated structure. *)

(** * 群胚打包接口

    检查依赖对象、继承的逆及唯一范畴视图；仅导入具体模型不得替无关范畴选择结构。 *)

Fail Definition unchosen_groupoid_bundle
  : Gpd
  := ltac:(typeclasses eauto).

Fail Definition unchosen_set_groupoid
  : IsGpd SetCat
  := ltac:(typeclasses eauto).

(** ** Inherited Inverse Witnesses

    A groupoid value supplies its own object type and inverse witnesses;
    no separately enabled property instance is needed. *)

(** ** 继承的逆见证

    群胚值提供自己的对象类型与逆见证，无须另行启用性质实例。 *)

Section BundledInverses.
Context (G : Gpd) {X Y : G}.

Definition inferred_inverse (f : Hom X Y)
  : Hom Y X
  := gpd_inv f.

Definition inferred_inverse_l (f : Hom X Y)
  : inferred_inverse f ∘ f ≈ id
  := gpd_inv_l f.

Definition inferred_inverse_r (f : Hom X Y)
  : f ∘ inferred_inverse f ≈ id
  := gpd_inv_r f.

End BundledInverses.

(** ** Independent Choices on One Category

    Packaging either supplied property must keep exactly its own inverse
    computation. No equality of the two property records is assumed. *)

(** ** 同一范畴上的独立选择

    打包任一给定性质时须恰好保留其自己的逆计算，不假定两份性质记录相等。 *)

Section IndependentChoices.
Context (C : Cat) (H K : IsGpd C) {X Y : C} (f : Hom X Y).

(** The constructor preserves both its category and its supplied property
    by conversion, independently of other witnesses on that category. *)

(** 构造器按定义保留底层范畴及给定性质，不受同一范畴上其他见证的影响。 *)

Example first_parent_is_selected
  : GpdToCat (GpdOfCat C H) = C.
Proof. reflexivity. Qed.

Example first_property_is_selected
  : isGpd (GpdOfCat C H) = H.
Proof. reflexivity. Qed.

Example first_inverse_is_selected
  : @gpd_inv _ (isGpd (GpdOfCat C H)) X Y f =
      @gpd_inv C H X Y f.
Proof. reflexivity. Qed.

Example second_inverse_is_selected
  : @gpd_inv _ (isGpd (GpdOfCat C K)) X Y f =
      @gpd_inv C K X Y f.
Proof. reflexivity. Qed.

End IndependentChoices.

(** ** Concrete Inverse Computations

    Reusing opposite/product constructors must retain the transparent xor
    inverses; equality-groupoid objects remain the original setoid elements. *)

(** ** 具体逆计算

    复用反范畴／乘积构造须保持透明的异或群逆；相等群胚的对象仍是原广集元素。 *)

Example bool_inverse_computes
  : @gpd_inv BoolGpd _ tt tt bool_loop = true.
Proof. reflexivity. Qed.

Example opposite_inverse_computes
  : @gpd_inv (OpGpd BoolGpd) _ tt tt true = true.
Proof. reflexivity. Qed.

Example product_inverse_computes
  : @gpd_inv (ProdGpd BoolGpd BoolGpd) _
      (tt,tt) (tt,tt) (true,false) = (true,false).
Proof. reflexivity. Qed.

Definition equality_groupoid_object (X : SetC) (x : X)
  : EqGpd X
  := x.

(** ** Existing Category Views

    Cartesian closed and monoidal structures reach their objects through
    their existing unique category chains; no additional sort edge is needed. *)

(** ** 已有范畴视图

    笛卡尔闭及幺半结构经已有唯一范畴链到达对象类型，无须额外类型转换边。 *)

Section ExistingViews.
Context (C : Cat) (HC : CCC C) (MC : MonoidalCat C).

Definition closed_object_view (x : HC)
  : C
  := x.

Definition monoidal_object_view (x : MC)
  : C
  := x.

End ExistingViews.

(** ** Independent Arrow and Equality Sizes

    Keep both strict size orders and larger law universes while packaging
    groupoids and their product. Their objects still inhabit the original sort. *)

(** ** 独立的箭头与相等大小

    打包群胚及其乘积时保留两种严格大小次序与更大的定律宇宙，对象仍属于原类型。 *)

Section IndependentUniverses.
Universes o h p l.
Constraint h < p.
Constraint p < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l})
    (HC : IsGpd C) (HD : IsGpd D).

Definition high_equality_bundle
  : Gpd
  := GpdOfCat C HC.

Definition low_equality_bundle
  : Gpd
  := GpdOfCat D HD.

Definition mixed_size_bundle
  : Gpd
  := ProdGpd high_equality_bundle low_equality_bundle.

Definition high_object_view (x : high_equality_bundle)
  : C
  := x.

Definition low_object_view (x : low_equality_bundle)
  : D
  := x.

End IndependentUniverses.
