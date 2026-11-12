From Cats Require Export
  Cat.Terminal
  Cat.Product.Core
  Cat.Monoidal.Lifting
  Cat.Monoidal.Cartesian.
From Cats Require Import
  Cat.Product.Transport.

Local Open Scope monoidal_scope.

(** * Cartesian Binary Lifting

    Transport generic lax lifting laws along the comparison between the
    derived tensor action and the selected product map. No pure map,
    exponentials or strength are needed. *)

(** * 笛卡尔二元提升

    沿导出张量作用与选定积映射的比较运输一般 lax 提升定律。不要求纯值映射、
    指数或强度。 *)

Section Lifting.
Context {C D : Cat} `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{TD : !HasTerminal D} `{PD : !HasProduct D}
    (L : LaxMonoidalFunctor
      (@CartesianMonoidal C TC PC) (@CartesianMonoidal D TD PD)).

(** Naturality at the ordinary product maps of both categories. *)

(** 关于两个范畴中通常积映射的自然性。 *)

Lemma cartesian_lift2_pre {X Y X' Y' Z : @Ob C}
    (f : Hom (X' × Y') Z) (g : Hom X X') (h : Hom Y Y')
  : lift₂[L; f] ∘ (@cross D PD _ _ _ _ (fmap L g) (fmap L h)) ≈
      lift₂[L; f ∘ (@cross C PC _ _ _ _ g h)].
Proof.
  pose proof (lax_lift2_pre L f g h) as H.
  rewrite !cartesian_tensor_map in H. exact H.
Qed.

(** A product associativity diagram lifts through the same lax structure. *)

(** 积的结合图通过同一个 lax 结构提升。 *)

Lemma cartesian_lift2_assoc {X Y Z U V T : @Ob C}
    (f : Hom (X × Y) U) (g : Hom (U × Z) T)
    (h : Hom (Y × Z) V) (k : Hom (X × V) T)
    (H : g ∘ (@cross C PC _ _ _ _ f id) ≈
      k ∘ (@cross C PC _ _ _ _ id h) ∘ (@product_assoc C PC X Y Z).1)
  : lift₂[L; g] ∘ (@cross D PD _ _ _ _ lift₂[L; f] id) ≈
      lift₂[L; k] ∘ (@cross D PD _ _ _ _ id lift₂[L; h]) ∘
        (@product_assoc D PD (L X) (L Y) (L Z)).1.
Proof.
  assert (K : g ∘ (@tensor_map C (@CartesianMonoidal C TC PC)
    _ _ _ _ f id) ≈ k ∘ (@tensor_map C (@CartesianMonoidal C TC PC)
      _ _ _ _ id h) ∘ (@tensor_assoc C (@CartesianMonoidal C TC PC) X Y Z)).
  { rewrite !cartesian_tensor_map. exact H. }
  pose proof (lax_lift2_assoc L f g h k K) as E.
  rewrite !cartesian_tensor_map in E. exact E.
Qed.

End Lifting.
