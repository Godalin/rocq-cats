From Cats Require Export
  Cat.Functor.Core.
From Cats Require Import
  Cat.Core
  Cat.Natural
  Cat.Induced
  Cat.Product.Core.

(** * Pairing Functors and Pointwise Products

    Product-valued diagrams use the existing product category. Pointwise
    products then use the chosen product bifunctor in the target category;
    no new universal-property proof is needed. *)

(** * 函子配对与逐点积

    积值图式使用已有的乘积范畴；逐点积随后使用目标范畴的选定积双函子，
    无需另证泛性质。 *)

(** The first projection keeps the first object and arrow components. *)

(** 第一投影保留对象及箭头的第一分量。 *)

Program Definition FstF (C : Cat) (D : Cat)
  : Functor (C ×C D) C
  :=
  {|F0 := fst
  ; F1 X Y := fst
  |}.
Next Obligation. intros [f g] [h k] [H K]. exact H. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** The second projection keeps the second components. *)

(** 第二投影保留第二分量。 *)

Program Definition SndF (C : Cat) (D : Cat)
  : Functor (C ×C D) D
  :=
  {|F0 := snd
  ; F1 X Y := snd
  |}.
Next Obligation. intros [f g] [h k] [H K]. exact K. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Pair two diagrams with a common source, retaining both arrow maps. *)

(** 将同源图式配对，保留两个箭头映射。 *)

Program Definition PairF {J : Cat} {C : Cat} {D : Cat}
    (F : Functor J C) (G : Functor J D)
  : Functor J (C ×C D)
  :=
  {|F0 i := (F i, G i)
  ; F1 i j f := (fmap F f, fmap G f)
  |}.
Next Obligation.
  intros f g H. split; apply functor_fmap_proper; exact H.
Defined.
Next Obligation. split; apply functor_id. Defined.
Next Obligation. split; apply functor_comp. Defined.

(** Repackage a product-labelled induced category as a product of induced
    categories. The object and arrow maps are identities; category law
    fields need not be natively equal. *)

(** 将带积标签的诱导范畴重新包装为诱导范畴的积。对象及箭头映射均为恒等，
    不要求范畴定律字段原生相等。 *)

Program Definition InducedProductF {C : Cat} {D : Cat} (X : Type) (Y : Type)
    (j : X → @Ob C) (k : Y → @Ob D)
  : Functor (InducedCat (C := C ×C D) (X * Y)
      (λ xy, (j (fst xy), k (snd xy))))
      (InducedCat X j ×C InducedCat Y k)
  :=
  {|F0 xy := xy
  ; F1 x y f := f
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. split; reflexivity. Defined.
Next Obligation. split; reflexivity. Defined.

(** The reverse repackaging retains the same computational data. *)

(** 反向重新包装保留相同的计算数据。 *)

Program Definition InducedProductInvF {C : Cat} {D : Cat} (X : Type) (Y : Type)
    (j : X → @Ob C) (k : Y → @Ob D)
  : Functor (InducedCat X j ×C InducedCat Y k)
      (InducedCat (C := C ×C D) (X * Y)
        (λ xy, (j (fst xy), k (snd xy))))
  :=
  {|F0 xy := xy
  ; F1 x y f := f
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. split; reflexivity. Defined.
Next Obligation. split; reflexivity. Defined.

(** Pointwise products reuse the chosen product bifunctor of the target. *)

(** 逐点积复用目标范畴的选定积双函子。 *)

Definition PointwiseProductF {J : Cat} {C : Cat} `{HP : !HasProduct C}
    (F G : Functor J C)
  : Functor J C
  := ProductF ∘F PairF F G.

(** Component maps induce a map of pointwise products. *)

(** 分量映射诱导逐点积之间的映射。 *)

Program Definition PointwiseProductN {J : Cat} {C : Cat} `{HP : !HasProduct C}
    {F F' G G' : Functor J C} (α : F ⇒ F') (β : G ⇒ G')
  : PointwiseProductF F G ⇒ PointwiseProductF F' G'
  :=
  {|nt i := α i × β i
  |}.
Next Obligation.
  change ((α Y × β Y) ∘ (fmap F f × fmap G f) ≈
    (fmap F' f × fmap G' f) ∘ (α X × β X)).
  rewrite <- !cross_comp, !nt_naturality. reflexivity.
Defined.
