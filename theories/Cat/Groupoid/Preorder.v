From Cats Require Export
  Cat.Groupoid.Core.
From Cats Require Import
  Cat.Preorder.

(** * Thin Groupoids

    Symmetry supplies inverse arrows in a preorder category. Parallel relation
    witnesses are already equal in its hom-setoid, without proof irrelevance. *)

(** * 薄群胚

    对称性给出预序范畴的逆箭头。平行关系见证已在 Hom 广集中相等，无需证明
    无关性。 *)

Program Definition PreorderCat_IsGpd {X : Type}
    (R : crelation X)
    `{HR : !PreOrder R} `{HS : !Symmetric R}
  : (PreorderCat R) ⦂ Gpd
  :=
  {|gpd_iso x y f := (symmetry f; (tt, tt))
  |}.

(** A codiscrete category is a groupoid, with the unique reverse arrow. *)

(** 余离散范畴是群胚，以唯一的反向箭头为逆。 *)

Program Definition CodiscreteCat_IsGpd (X : Type)
  : (CodiscreteCat X) ⦂ Gpd
  :=
  {|gpd_iso x y f := (tt; (tt, tt))
  |}.

(** A symmetric preorder gives a complete thin groupoid, using its original
    relation witnesses as arrows and the supplied symmetry as inversion. *)

(** 对称预序给出完整薄群胚，以原关系见证为箭头，以给定对称性取逆。 *)

Definition PreorderGpd {X : Type} (R : crelation X)
    `{HR : !PreOrder R} `{HS : !Symmetric R}
  : Gpd
  := GpdOfCat (PreorderCat R) (PreorderCat_IsGpd R).

(** Package the codiscrete category with its unique reverse arrows. *)

(** 将余离散范畴与其唯一反向箭头打包。 *)

Definition CodiscreteGpd (X : Type)
  : Gpd
  := GpdOfCat (CodiscreteCat X)
    (CodiscreteCat_IsGpd X).
