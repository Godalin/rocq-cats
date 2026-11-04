From Cats Require Import
  Cat.Groupoid.Core
  Cat.Preorder.

(** * Thin Groupoids

    Symmetry supplies inverse arrows in a preorder category. Parallel relation
    witnesses are already equal in its hom-setoid, without proof irrelevance. *)

(** * 薄群胚

    对称性给出预序范畴的逆箭头。平行关系见证已在 Hom 广集中相等，无需证明
    无关性。 *)

Program Definition PreorderCat_IsGroupoid {X : Type} (R : crelation X)
    `{HR : !PreOrder R} `{HS : !Symmetric R}
  : PreorderCat R ⦂ Gpd
  :=
  {|groupoid_iso x y f := (symmetry f; (tt, tt))
  |}.

(** A codiscrete category is a groupoid, with the unique reverse arrow. *)

(** 余离散范畴是群胚，以唯一的反向箭头为逆。 *)

Program Definition CodiscreteCat_IsGroupoid (X : Type)
  : CodiscreteCat X ⦂ Gpd
  :=
  {|groupoid_iso x y f := (tt; (tt, tt))
  |}.
