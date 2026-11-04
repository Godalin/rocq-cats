From Cats Require Import
  Cat.Functor.Core
  Cat.Groupoid.Core
  Cat.Groupoid.Preorder
  Cat.Preorder.
From Cats.Set Require Import
  Core.

(** * The Equality Groupoid of a Setoid

    Objects are elements and arrows are specified equality witnesses. All
    parallel witnesses are equal in the hom-setoid. The resulting groupoid
    is thin even when equality witnesses form a nontrivial Type. *)

(** * 广集的相等群胚

    对象是元素，箭头是指定相等的见证，全部平行见证在 Hom 广集中相等。因此，
    即使相等见证构成非平凡的 Type，所得群胚仍是薄群胚。 *)

Definition EqGpd (X : SetC)
  : Cat
  := @PreorderCat X (carrier_equiv X)
      (equivalence_preorder (carrier_equiv X)).

(** Symmetry of setoid equality supplies inverses. Enable this instance
    explicitly; importing the model does not select a groupoid structure. *)

(** 广集相等的对称性提供逆；此实例须显式启用，导入模型不自动选择群胚结构。 *)

Definition EqGpd_IsGroupoid (X : SetC)
  : EqGpd X ⦂ Gpd
  := @PreorderCat_IsGroupoid X (carrier_equiv X)
      (equivalence_preorder (carrier_equiv X)) Equivalence_Symmetric.

(** Parallel equality witnesses agree in the hom-setoid, regardless of their
    native equality. This is the thinness used by coherent families. *)

(** 平行相等见证在 Hom 广集中相等，无论其原生相等如何；相干族使用的正是此
    薄性。 *)

Lemma eq_gpd_thin {X : SetC} {x y : X} (p q : x ≈S y)
  : @HomEq (EqGpd X) x y p q.
Proof. exact tt. Defined.

(** A respectful map induces a functor of equality groupoids. *)

(** 保相等映射诱导相等群胚之间的函子。 *)

Definition EqGpdF {X Y : SetC} (f : X →r Y)
  : Functor (EqGpd X) (EqGpd Y)
  := PreorderF
      (HR := equivalence_preorder (carrier_equiv X))
      (HS := equivalence_preorder (carrier_equiv Y))
      f (λ x y p, @func_proper X Y f x y p).
