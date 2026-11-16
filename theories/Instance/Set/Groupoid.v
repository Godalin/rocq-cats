From Cats Require Export
  Cat.Groupoid.Core.
From Cats Require Import
  Cat.Functor.Core
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
  : Gpd
  := @PreorderGpd X (carrier_equiv X)
      (equivalence_preorder (carrier_equiv X)) Equivalence_Symmetric.

(** Read the inverses already stored by the equality groupoid. This explicit
    property view uses exactly the same category and symmetry witnesses. *)

(** 读取相等群胚已保存的逆；此显式性质视图使用恰好相同的范畴与对称见证。 *)

Definition EqGpd_IsGpd (X : SetC)
  : EqGpd X ⦂ Gpd
  := @isGpd (EqGpd X).

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
  : Fct (EqGpd X) (EqGpd Y)
  := PreorderF
      (HR := equivalence_preorder (carrier_equiv X))
      (HS := equivalence_preorder (carrier_equiv Y))
      f (λ x y p, @func_proper X Y f x y p).
