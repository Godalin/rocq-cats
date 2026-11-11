From Cats Require Export
  Algebra.Group.Core
  Algebra.Monoid.Category.
From Cats Require Import
  Cat.Groupoid.Core.

Local Open Scope monoid_scope.

(** * Groups as Single-Object Groupoids

    Reuse the monoid category, selecting group inverses as arrow inverses.
    Enable the resulting groupoid structure explicitly. *)

(** * 群的单对象群胚解释

    复用幺半群范畴，以群逆作为箭头的逆，所得群胚结构须显式启用。 *)

Program Definition MonoidCat_IsGroupoid (G : SetC) `{HG : !Group G}
  : B(G) ⦂ Gpd
  :=
  {|groupoid_iso X Y g := (g⁻¹; (group_inv_l g, group_inv_r g))
  |}.

(** Endomorphisms at any specified object of a groupoid form a group.
    This construction requires no equality of object representatives. *)

(** 群胚任意指定对象处的自态射构成群，不要求对象代表之间原生相等。 *)

Program Definition EndGroup (C : Cat) `{HC : !IsGroupoid C} (X : @Ob C)
  : Group (HomSet X X)
  :=
  {|GroupM := EndMonoid C X
  ; group_inv f := @groupoid_inv C HC X X f
  ; group_inv_l := @groupoid_inv_l C HC X X
  ; group_inv_r := @groupoid_inv_r C HC X X
  |}.
