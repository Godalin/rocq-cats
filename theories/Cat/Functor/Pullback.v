From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Pullback.

(** * Pointwise Pullbacks of Diagrams

    A cone of natural transformations is a pullback whenever each component
    is a pullback. Component uniqueness proves that the mediators are natural;
    no equality between chosen witnesses is required. This applies to
    presheaves by taking the indexing category opposite.

    The candidate theorem needs only the supplied component cones. A separate
    construction selects pullbacks from an explicitly supplied [HasPullback]
    in the target. No model choice is registered by importing this module. *)

(** * 图式的逐点拉回

    若自然变换锥的每个分量都是拉回，则该锥也是拉回。分量中介的唯一性给出
    自然性，无需比较选定见证本身的相等。将索引范畴取反即可应用于预层。

    候选定理仅需给定的分量锥；另一个构造从显式提供的目标 [HasPullback]
    选择拉回。导入本模块不会注册任何模型选择。 *)

(** ** Componentwise Universal Properties

    Fix a cospan of diagrams and a natural cone. Assume the pullback property
    only at its components, then assemble the original component mediators. *)

(** ** 逐分量的泛性质

    固定图式余跨度及自然锥，仅假设其各分量的拉回性质，再组织原分量中介。 *)

Section Candidate.
Context {J C : Cat} {F G H P : Fct J C}.
Context (α : F ⇒ H) (β : G ⇒ H) (p : P ⇒ F) (q : P ⇒ G).
Context (HP : ∀ i, is_pullback (α i) (β i) (P i) (p i) (q i)).

(** Lift a commuting natural cone using the given component mediators. *)

(** 使用给定分量中介提升交换的自然锥。 *)

Program Definition PointwisePullbackLiftN {Q : Fct J C}
    (u : Q ⇒ F) (v : Q ⇒ G) (Hu : (α ∘Nv u) ≈N (β ∘Nv v))
  : Q ⇒ P
  :=
  {|nt i := (snd (HP i) (Q i) (u i) (v i) (Hu i)).1
  |}.
Next Obligation.
  destruct (snd (HP X) (Q X) (u X) (v X) (Hu X)).2
    as [[HX1 HX2] HX_unique].
  destruct (snd (HP Y) (Q Y) (u Y) (v Y) (Hu Y)).2
    as [[HY1 HY2] HY_unique].
  apply (pullback_hom_ext (HP Y)).
  - rewrite <- comp_assoc, HY1, (nt_naturality u f).
    rewrite <- comp_assoc, (nt_naturality p f), comp_assoc,
      HX1.
    reflexivity.
  - rewrite <- comp_assoc, HY2, (nt_naturality v f).
    rewrite <- comp_assoc, (nt_naturality q f), comp_assoc,
      HX2.
    reflexivity.
Defined.

(** Componentwise pullback cones satisfy the full diagram pullback property. *)

(** 逐分量的拉回锥满足完整的图式拉回泛性质。 *)

Definition pointwise_pullback_universal
  : is_pullback (C := FctCat J C) α β P p q.
Proof.
  split.
  - intros i. exact (fst (HP i)).
  - intros Q u v Hu. exists (PointwisePullbackLiftN u v Hu).
    refine {|this := _
           ; that := _
           |}.
    + split; intros i;
        destruct (snd (HP i) (Q i) (u i) (v i) (Hu i)).2
          as [[H1 H2] H_unique]; assumption.
    + intros k [H1 H2] i.
      destruct (snd (HP i) (Q i) (u i) (v i) (Hu i)).2
        as [Hcone H_unique].
      apply H_unique.
      split; [exact (H1 i) | exact (H2 i)].
Defined.

End Candidate.

(** ** Choosing Component Pullbacks

    With chosen pullbacks in [C], map their vertices along indexing arrows
    using the original target mediators. Their uniqueness proves the functor
    laws. No product, terminal object or exponential is assumed. *)

(** ** 选择分量拉回

    给定 [C] 中选定的拉回，用原目标中介沿索引箭头映射顶点；中介唯一性证明
    函子律。不假设积、终对象或指数。 *)

Section Chosen.
Context {J C : Cat} `{HPb : !HasPullback C}.
Context {F G H : Fct J C} (α : F ⇒ H) (β : G ⇒ H).

(** The image cone commutes by naturality and the source pullback square. *)

(** 由自然性和源拉回方形，像锥交换。 *)

Lemma pointwise_pullback_map_square {i j : @Ob J} (f : Hom i j)
  : α j ∘ (fmap F f ∘ pb1 (α i) (β i)) ≈
      β j ∘ (fmap G f ∘ pb2 (α i) (β i)).
Proof.
  rewrite <- comp_assoc, (nt_naturality α f), comp_assoc,
    pullback_comm, <- comp_assoc, <- (nt_naturality β f), comp_assoc.
  reflexivity.
Defined.

(** The action uses the selected target pullback mediator, transparently. *)

(** 作用透明地使用目标选定的拉回中介。 *)

Definition pointwise_pullback_map {i j : @Ob J} (f : Hom i j)
  : Hom (Pb (α i) (β i)) (Pb (α j) (β j))
  := pb (fmap F f ∘ pb1 (α i) (β i))
      (fmap G f ∘ pb2 (α i) (β i))
      (pointwise_pullback_map_square f).

(** The first projection of the action is the original diagram action. *)

(** 作用的第一投影是原图式作用。 *)

Lemma pointwise_pullback_map_β1 {i j : @Ob J} (f : Hom i j)
  : pb1 (α j) (β j) ∘ pointwise_pullback_map f ≈
      fmap F f ∘ pb1 (α i) (β i).
Proof.
  exact (fst (@this _ _ _ _ _ (pullback_mediator_unique
    (pointwise_pullback_map_square f)))).
Qed.

(** The other projection retains the second diagram action. *)

(** 另一投影保留第二个图式的作用。 *)

Lemma pointwise_pullback_map_β2 {i j : @Ob J} (f : Hom i j)
  : pb2 (α j) (β j) ∘ pointwise_pullback_map f ≈
      fmap G f ∘ pb2 (α i) (β i).
Proof.
  exact (snd (@this _ _ _ _ _ (pullback_mediator_unique
    (pointwise_pullback_map_square f)))).
Qed.

(** Assemble vertices and actions into the pullback diagram. *)

(** 将顶点和作用组织为拉回图式。 *)

Program Definition PointwisePullbackF
  : Fct J C
  :=
  {|F0 i := Pb (α i) (β i)
  ; F1 i j f := pointwise_pullback_map f
  |}.
Next Obligation.
  intros f g Hfg. apply (pullback_hom_ext pullback_universal).
  - rewrite !pointwise_pullback_map_β1, Hfg. reflexivity.
  - rewrite !pointwise_pullback_map_β2, Hfg. reflexivity.
Defined.
Next Obligation.
  apply (pullback_hom_ext pullback_universal).
  - rewrite pointwise_pullback_map_β1, functor_id. carw.
  - rewrite pointwise_pullback_map_β2, functor_id. carw.
Defined.
Next Obligation.
  apply (pullback_hom_ext pullback_universal).
  - rewrite pointwise_pullback_map_β1, <- comp_assoc,
      pointwise_pullback_map_β1, comp_assoc,
      pointwise_pullback_map_β1, functor_comp, comp_assoc. reflexivity.
  - rewrite pointwise_pullback_map_β2, <- comp_assoc,
      pointwise_pullback_map_β2, comp_assoc,
      pointwise_pullback_map_β2, functor_comp, comp_assoc. reflexivity.
Defined.

(** The first component projections are natural by the mediator equation. *)

(** 由中介方程，第一分量投影自然。 *)

Program Definition PointwisePullbackFstN
  : PointwisePullbackF ⇒ F
  :=
  {|nt i := pb1 (α i) (β i)
  |}.
Next Obligation. apply pointwise_pullback_map_β1. Defined.

(** The second component projections form the other natural cone leg. *)

(** 第二分量投影组成另一条自然锥边。 *)

Program Definition PointwisePullbackSndN
  : PointwisePullbackF ⇒ G
  :=
  {|nt i := pb2 (α i) (β i)
  |}.
Next Obligation. apply pointwise_pullback_map_β2. Defined.

End Chosen.

(** Select the pointwise cone by reusing the candidate theorem. Importing
    this definition does not enable the choice as a global instance. *)

(** 复用候选定理选择逐点锥；导入此定义不会将选择启用为全局实例。 *)

Program Definition FctCat_HasPullback (J C : Cat) `{HPb : !HasPullback C}
  : HasPullback (FctCat J C)
  :=
  {|Pb F G H α β := PointwisePullbackF α β
  ; pb1 F G H α β := PointwisePullbackFstN α β
  ; pb2 F G H α β := PointwisePullbackSndN α β
  |}.
Next Obligation.
  apply pointwise_pullback_universal. intros i. apply pullback_universal.
Defined.
