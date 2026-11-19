From Cats Require Export
  Cat.Core
  Cat.Functor.Core.

(** * Functor Laws on Fixed Maps

    Separate preservation evidence from supplied object and arrow maps.
    Context actions can share one object tensor while using this same law
    interface independently on the left and right. *)

(** * 固定映射上的函子律

    为给定的对象与态射映射单独提供保持性见证。上下文作用可以共享一个对象
    张量，并在左右两侧分别使用同一个定律接口。 *)

Class IsFct {C D : Cat} (obj : C → D)
    (map : ∀ {X Y : C}, Hom X Y → Hom (obj X) (obj Y))
  :=
  (** Respect the specified equality on each hom-set. *)

  (** 保持每个 Hom 广集的指定相等。 *)

  { fct_map_proper {X Y : C}
    :: Proper (≈[X,Y] ==> ≈[obj X,obj Y]) (@map X Y)

  (** Preserve identities and composition on these same maps. *)

  (** 在同一组映射上保持恒等及复合。 *)

  ; fct_map_id (X : C) : map (id[X]) ≈ id[obj X]
  ; fct_map_comp {X Y Z : C} (g : Hom Y Z) (f : Hom X Y)
    : map (g ∘ f) ≈ map g ∘ map f
  }.

(** Bundle the given maps without replacing their computational data. *)

(** 打包给定映射，不替换其可计算数据。 *)

Program Definition FctOfMaps {C D : Cat} (obj : C → D)
    (map : ∀ {X Y : C}, Hom X Y → Hom (obj X) (obj Y))
    (H : IsFct obj (@map))
  : Fct C D
  :=
  {|F0 := obj
  ; F1 := @map
  ; fct_fmap_proper X Y := fct_map_proper (IsFct := H)
  ; fct_id X := fct_map_id (IsFct := H) X
  ; fct_comp X Y Z g f := fct_map_comp (IsFct := H) g f
  |}.

(** An existing functor supplies the fixed-map view transparently. *)

(** 已有函子透明地给出固定映射视图。 *)

Program Definition Fct_IsFct {C D : Cat} (F : Fct C D)
  : IsFct F (@fmap F)
  :=
  {|fct_map_proper X Y := @fct_fmap_proper C D F X Y
  ; fct_map_id X := @fct_id C D F X
  ; fct_map_comp _ _ _ g f := fct_comp _ _ F g f
  |}.
