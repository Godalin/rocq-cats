From Cats Require Export
  Cat.Profunctor.Core.
From Cats Require Import
  Cat.Core
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift.

Local Open Scope profunctor_scope.

(** * Hom Profunctors and Functorial Reindexing

    The existing Hom bifunctor is a profunctor. Explicit lifting raises
    its carrier and equality levels independently; the declared ambient
    bounds must actually contain the corresponding Hom levels. No object
    size bound or coend existence is required. *)

(** * Hom Profunctor 及函子重索引

    已有 Hom 双函子就是 profunctor。显式提升独立扩大其载体与相等层级；
    所声明环境界必须确实容纳对应 Hom 层级。不要求对象大小界或 coend 存在。 *)

(** Raise the existing Hom functor, without rebuilding its composition laws. *)

(** 提升已有 Hom 函子，不重新证明其复合定律。 *)

Definition HomProfunctor@{u p +} (C : Cat)
  : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})
  := LiftF ∘F (@HomF C).

(** Evaluate the same raised Hom on two independently supplied functors. *)

(** 在两个独立给定函子上求值同一个提升 Hom。 *)

Definition FunctorHomProfunctor@{u p +} {C D K : Cat}
    (F : Fct C K) (G : Fct D K)
  : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})
  := ProfunctorReindex F G (HomProfunctor K).

(** ** Hom Action in the Declared Bounds

    Fix a category and ambient bounds for its Hom carriers and equality
    witnesses. The three actions are ordinary pre/postcomposition of arrows;
    keep lifting explicit rather than asserting a resizing principle. *)

(** ** 声明大小界内的 Hom 作用

    固定范畴及容纳 Hom 载体／相等见证的环境界。三个作用就是通常的箭头预合成
    和后合成；保持显式提升，不宣称 resizing 原则。 *)

Section HomActions.
Universes u p.
Context (C : Cat).
Let H
  : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})
  := HomProfunctor C.

(** Two-sided action postcomposes and precomposes the represented arrow. *)

(** 双侧作用在所表示箭头之后及之前复合。 *)

Lemma hom_profunctor_dimap {X X' Y Y' : @Ob C}
    (f : Hom X' X) (g : Hom Y Y') (h : H (X,Y))
  : lower (dimap[H; f; g] h) ≈ g ∘ lower h ∘ f.
Proof. reflexivity. Defined.

(** The input action is precomposition. *)

(** 输入作用是预合成。 *)

Lemma hom_profunctor_lmap {X X' Y : @Ob C}
    (f : Hom X' X) (h : H (X,Y))
  : lower (lmap[H; f] h) ≈ lower h ∘ f.
Proof.
  change ((@Cat.Core.id C Y) ∘ lower h ∘ f ≈ lower h ∘ f).
  rewrite comp_id_l. reflexivity.
Defined.

(** The output action is postcomposition. *)

(** 输出作用是后合成。 *)

Lemma hom_profunctor_rmap {X Y Y' : @Ob C}
    (g : Hom Y Y') (h : H (X,Y))
  : lower (rmap[H; g] h) ≈ g ∘ lower h.
Proof.
  change (g ∘ lower h ∘ (@Cat.Core.id C X) ≈ g ∘ lower h).
  rewrite comp_id_r. reflexivity.
Defined.

End HomActions.

(** ** Hom between Two Functor Images

    Fix two functors with the same target, retaining independent source
    categories and the target's actual Hom bounds. Reindex the already
    constructed profunctor; its action maps both ordinary boundary arrows. *)

(** ** 两个函子像之间的 Hom

    固定两个同目标函子，保持来源范畴独立，并使用目标的真实 Hom 界。对已构造
    profunctor 重索引，其作用映射两条通常边界箭头。 *)

Section FunctorHomAction.
Universes u p.
Context {C D K : Cat} (F : Fct C K) (G : Fct D K).
Let H
  : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})
  := FunctorHomProfunctor F G.

(** Dimap on computation Hom values uses exactly the functor images of
    input/output maps, followed by the original composition in the target. *)

(** 计算 Hom 值上的 dimap 恰好使用输入／输出映射的函子像，再使用原目标复合。 *)

Lemma functor_hom_profunctor_dimap {X X' : @Ob C} {Y Y' : @Ob D}
    (f : Hom X' X) (g : Hom Y Y') (h : H (X,Y))
  : lower (dimap[H; f; g] h) ≈ fmap G g ∘ lower h ∘ fmap F f.
Proof. reflexivity. Defined.

End FunctorHomAction.
