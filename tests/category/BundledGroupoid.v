From Cats Require Import
  Cat.Core
  Cat.CCC.Core
  Cat.Monoidal.Monoidal
  Cat.Groupoid.Core
  Cat.Groupoid.Preorder
  Instance.Set.Core
  Instance.Set.Groupoid
  Instance.Bool.Group
  Instance.Bool.Action.

(** * Bundled Groupoid Interfaces

    Check dependent objects, inherited inverses and the unique category view.
    Merely importing a concrete model must not choose an unrelated structure. *)

Fail Definition unchosen_groupoid_bundle
  : Gpd
  := ltac:(typeclasses eauto).

Fail Definition unchosen_set_groupoid
  : IsGpd SetCat
  := ltac:(typeclasses eauto).

(** ** Inherited Inverse Witnesses

    A groupoid value supplies its own object type and inverse witnesses;
    no separately enabled property instance is needed. *)

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

Section IndependentChoices.
Context (C : Cat) (H K : IsGpd C) {X Y : C} (f : Hom X Y).

(** The constructor preserves both its category and its supplied property
    by conversion, independently of other witnesses on that category. *)

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

Section ExistingViews.
Context (C : CCC) (MC : MonoidalCat).

Definition closed_object_view (x : C)
  : C
  := x.

Definition monoidal_object_view (x : MC)
  : MonoidalCatToPremonoidalCat MC
  := x.

(** The two generated views recover the same binoidal ancestor. *)

Example monoidal_binoidal_views_agree
  : MagmoidalCatToBinoidalCat (MonoidalCatToMagmoidalCat MC)
    = MonoidalCatToBinoidalCat MC
  := eq_refl.

Example premonoidal_binoidal_view_agrees
  : PremonoidalCatToBinoidalCat (MonoidalCatToPremonoidalCat MC)
    = MonoidalCatToBinoidalCat MC
  := eq_refl.

End ExistingViews.

(** ** Independent Arrow and Equality Sizes

    Keep both strict size orders and larger law universes while packaging
    groupoids and their product. Their objects still inhabit the original sort. *)

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
