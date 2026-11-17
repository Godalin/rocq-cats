From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.CatCat
  Cat.Induced
  Cat.Groupoid.Core
  Cat.Groupoid.CoreGpd.

(** * Groupoids and Equivalences of Groupoids

    The object-indexed category of groupoids has ordinary functors as
    arrows. Taking its core keeps equivalences with chosen quasi-inverses
    and natural-isomorphism witnesses. This is a complete groupoid whose
    objects are smaller complete groupoids. *)

(** * 群胚及群胚等价

    按群胚对象索引的范畴以普通函子为态射；取其核心后保留带选定拟逆及
    自然同构见证的等价。这是一个完整群胚，其对象为更小的完整群胚。 *)

(** Keep complete groupoids as objects and functors as arrows. *)

(** 保留完整群胚作为对象，以函子为态射。 *)

Definition GpdCat
  : Cat
  := InducedCat (C := CatCat) Gpd GpdToCat.

(** Equivalences form the core; their inverse data remains transparent. *)

(** 等价组成核心，其逆数据保持透明。 *)

Definition GpdGpd
  : Gpd
  := CoreGpd GpdCat.

(** Smaller instances are objects of larger ones. Each right-associated
    annotation uses a fresh universe instance and the object-type coercion. *)

(** 较小实例是较大实例的对象；每个右结合的类型标注使用新的宇宙实例，
    并通过强制转换取得对象类型。 *)

Check GpdGpd : GpdGpd : GpdGpd : GpdGpd.

(** Forget inverse data and then the groupoid structures. *)

(** 先忘掉逆数据，再忘掉群胚结构。 *)

Definition GpdForgetF
  : Fct GpdGpd CatCat
  := InducedInclusionF (C := CatCat) Gpd GpdToCat ∘F CoreInclusionF GpdCat.
