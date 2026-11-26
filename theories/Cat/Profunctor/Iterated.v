From Cats Require Export
  Cat.Profunctor.Parameter.
From Cats Require Import
  Cat.Core
  Instance.Set.Core
  Instance.Set.Product.

Local Open Scope prof_scope.

(** * Balanced Three-Stage Operations

    Three composable profunctors have two intermediate indices. Balance
    at each index separately; parameterized coend descent then extends the
    same operation through either parenthesization. No coend indexed by a
    product category, resizing or uniform composition choice is assumed. *)

(** * 平衡的三段操作

    三个可复合 profunctor 具有两个中间指标。分别在每个指标处平衡，带参数
    coend 下降便将同一个操作延拓过任一种括号方式。不假定积范畴指标的 coend、
    大小重设或统一的复合选择。 *)

(** A respectful three-stage operation with the two ordinary balance laws.
    The laws keep their Type-valued witnesses independently of value sizes. *)

(** 带两个通常平衡律的尊重三段操作；定律保留独立于值大小的 Type 值见证。 *)

Minks.Mixin ProfunctorTripleCowedge@{u p +} {C D E B : Cat}
    (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _}))
    (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _}))
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
    (X : @Ob C) (W : @Ob B) (V : SetC@{u p})
  :=
  { triple_cowedge_leg :> ∀ (Y : @Ob D) (Z : @Ob E),
      ((P (X,Y) ×S Q (Y,Z)) ×S R (Z,W)) →r V

  (** Move the first intermediate arrow between the first two factors. *)

  (** 将第一个中间箭头在前两个因子之间移动。 *)

  ; triple_cowedge_gluing_l : ∀ (Y Y' : @Ob D) (Z : @Ob E)
      (h : Hom Y Y') (x : P (X,Y)) (y : Q (Y',Z)) (z : R (Z,W)),
      triple_cowedge_leg Y Z ((x,lmap[Q; h] y),z) ≈S
      triple_cowedge_leg Y' Z ((rmap[P; h] x,y),z)

  (** Move the second intermediate arrow between the last two factors. *)

  (** 将第二个中间箭头在后两个因子之间移动。 *)

  ; triple_cowedge_gluing_r : ∀ (Y : @Ob D) (Z Z' : @Ob E)
      (h : Hom Z Z') (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z',W)),
      triple_cowedge_leg Y Z ((x,y),lmap[R; h] z) ≈S
      triple_cowedge_leg Y Z' ((x,rmap[Q; h] y),z)
  }.

Arguments triple_cowedge_leg {_ _ _ _ _ _ _ _ _ _} _ _ _.
Arguments triple_cowedge_gluing_l {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ _.
Arguments triple_cowedge_gluing_r {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ _.

(** ** Single-Sided Actions on Composite Generators

    Given a composition family, specialize its original dimap equation to
    one boundary at a time. Only the untouched factor's identity is removed. *)

(** ** 复合生成元上的单侧作用

    给定复合族，将原 dimap 方程分别用于一侧边界，只消去未改变因子的恒等作用。 *)

Section SingleActions.
Universes u p.
Context {C D E : Cat}.
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HC : !HasProfComp C D E Q P}.

(** Input preprocessing acts only on the first generating value. *)

(** 输入预处理只作用于第一个生成值。 *)

Lemma profunctor_comp_lmap_inject {X X' : @Ob C} {Z : @Ob E}
    (f : Hom X' X) (Y : @Ob D) (x : P (X,Y)) (y : Q (Y,Z))
  : lmap[Q ∘Pr P; f] (ιPr[Q; P; Y] (x,y)) ≈S
      ιPr[Q; P; Y] (lmap[P; f] x,y).
Proof.
  transitivity (ιPr[Q; P; Y] (lmap[P; f] x,rmap[Q; id[Z]] y)).
  - exact (prof_comp_dimap_inject Q P f (id[Z]) Y x y).
  - apply func_proper. split; [reflexivity |].
    exact (prof_rmap_id Q Y Z y).
Defined.

(** Output postprocessing acts only on the last generating value. *)

(** 输出后处理只作用于最后一个生成值。 *)

Lemma profunctor_comp_rmap_inject {X : @Ob C} {Z Z' : @Ob E}
    (g : Hom Z Z') (Y : @Ob D) (x : P (X,Y)) (y : Q (Y,Z))
  : rmap[Q ∘Pr P; g] (ιPr[Q; P; Y] (x,y)) ≈S
      ιPr[Q; P; Y] (x,rmap[Q; g] y).
Proof.
  transitivity (ιPr[Q; P; Y] (lmap[P; id[X]] x,rmap[Q; g] y)).
  - exact (prof_comp_dimap_inject Q P (id[X]) g Y x y).
  - apply func_proper. split; [| reflexivity].
    exact (prof_lmap_id P X Y x).
Defined.

End SingleActions.

(** ** Descending the First Two Stages

    Fix the outer objects and a balanced three-stage operation. A chosen
    first composition family suffices to descend the first two factors;
    the remaining factor stays an external parameter. *)

(** ** 下降前两段

    固定外部对象及平衡三段操作。选定第一个复合族即可下降前两个因子，
    剩余因子保持为外部参数。 *)

Section LeftInner.
Universes u p.
Context {C D E B : Cat}.
Context (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})).
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context {X : @Ob C} {W : @Ob B} {V : SetC@{u p}}.
Context (κ : ProfunctorTripleCowedge R Q P X W V).

(** Fixing the last value gives a cowedge of the first composition kernel. *)

(** 固定最后一个值，得到第一个复合核的余楔。 *)

Program Definition ProfunctorTripleLeftSlice (Z : @Ob E) (z : R (Z,W))
  : Cowedge (ProfCompKernel Q P X Z) V
  := ProfCompCowedge Q P
      (λ Y, {|func xy := κ Y Z (xy,z)|}) _.
Next Obligation.
  intros xy xy' H. exact (@func_proper _ _ (κ Y Z)
    (xy,z) (xy',z) (H,reflexivity z)).
Defined.
Next Obligation.
  exact (triple_cowedge_gluing_l κ Y Y' Z h x y z).
Defined.

(** These slices respect equality of the external last value. *)

(** 这些切片保持外部最后一个值的相等。 *)

Global Instance profunctor_triple_left_slice_proper (Z : @Ob E)
  : Proper ([≈S] ==> CowedgeEq) (ProfunctorTripleLeftSlice Z).
Proof.
  intros z z' H Y xy.
  exact (@func_proper _ _ (κ Y Z) (xy,z) (xy,z') (reflexivity xy,H)).
Defined.

Context `{HI : !HasProfComp C D E Q P}.

(** Descend the slices beside their unchanged last value. *)

(** 在不变的最后一个值旁下降这些切片。 *)

Definition profunctor_triple_left_leg (Z : @Ob E)
  : ((Q ∘Pr P) (X,Z) ×S R (Z,W)) →r V
  := prof_comp_parameter_desc Q P (ProfunctorTripleLeftSlice Z)
      (profunctor_triple_left_slice_proper Z).

(** The parameter boundary square transports the second balance law
    through the first descent, even for a noninvertible intermediate arrow. *)

(** 参数边界方块将第二个平衡律运输过第一次下降，即使中间箭头不可逆也成立。 *)

Lemma profunctor_triple_left_balance (Z Z' : @Ob E) (h : Hom Z Z')
    (t : (Q ∘Pr P) (X,Z)) (z : R (Z',W))
  : profunctor_triple_left_leg Z (t,lmap[R; h] z) ≈S
      profunctor_triple_left_leg Z' (rmap[Q ∘Pr P; h] t,z).
Proof.
  pose (μ := λ v : R (Z',W), ProfunctorTripleLeftSlice Z (lmap[R; h] v)).
  assert (Hμ : Proper ([≈S] ==> CowedgeEq) μ).
  { intros v v' Hv. apply profunctor_triple_left_slice_proper.
    exact (@func_proper _ _ (lmap[R; h]) v v' Hv). }
  symmetry.
  refine (prof_comp_parameter_boundary Q P μ
    (ProfunctorTripleLeftSlice Z') Hμ
    (profunctor_triple_left_slice_proper Z') (id[X]) h
    id_resp id_resp _ t z).
  intros Y x y v.
  transitivity (κ Y Z' ((x,rmap[Q; h] y),v)).
  - exact (@func_proper _ _ (κ Y Z')
      ((lmap[P; id[X]] x,rmap[Q; h] y),v)
      ((x,rmap[Q; h] y),v)
      ((prof_lmap_id P X Y x,reflexivity _),reflexivity v)).
  - symmetry. exact (triple_cowedge_gluing_r κ Y Z Z' h x y v).
Defined.

(** The descended legs form the original outer composition cowedge. *)

(** 下降后的腿组成原外层复合余楔。 *)

Definition ProfunctorTripleLeftCowedge
  : Cowedge (ProfCompKernel R (Q ∘Pr P) X W) V
  := ProfCompCowedge R (Q ∘Pr P)
      profunctor_triple_left_leg profunctor_triple_left_balance.

(** Keep the same derived cowedge for descent and its computation laws. *)

(** 下降及其计算律使用同一个派生余楔。 *)

Let μ := ProfunctorTripleLeftCowedge.

Context `{HO : !HasCoend SetCat
    (ProfCompKernel R (Q ∘Pr P) X W)}.

(** Descend once more using just the single indicated outer coend. *)

(** 仅用所指单个外层 coend 再下降一次。 *)

Definition profunctor_triple_left_desc
  : coend[ProfCompKernel R (Q ∘Pr P) X W] →r V
  := coend⟨μ⟩.

(** Expose outer computation at an abstract inner value before applying it
    to a nested injection. This keeps the selected computations shared. *)

(** 先对抽象内层值暴露外层计算，再应用于嵌套注入，以保持选定计算的共享。 *)

Lemma profunctor_triple_left_outer_β (Z : @Ob E)
    (t : (Q ∘Pr P) (X,Z)) (z : R (Z,W))
  : profunctor_triple_left_desc
      (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z (t,z)) ≈S
      μ Z (t,z).
Proof. exact (coend_β μ Z (t,z)). Defined.

(** Both original injections evaluate to the original three-stage operation. *)

(** 两个原注入的求值为原三段操作。 *)

Lemma profunctor_triple_left_β (Y : @Ob D) (Z : @Ob E)
    (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W))
  : profunctor_triple_left_desc
      (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
        (ιPr[Q; P; Y] (x,y),z)) ≈S κ Y Z ((x,y),z).
Proof.
  transitivity (μ Z (ιPr[Q; P; Y] (x,y),z)).
  - exact (profunctor_triple_left_outer_β Z (ιPr[Q; P; Y] (x,y)) z).
  - exact (@prof_comp_parameter_β C D E Q P X Z
      (@hasProfCompCoend C D E Q P HI X Z) (R (Z,W)) V
      (ProfunctorTripleLeftSlice Z) (profunctor_triple_left_slice_proper Z)
      Y (x,y) z).
Defined.

End LeftInner.

(** ** Double Generators on the Left

    Choose the first composition family and only one outer coend.
    Two successive original distinction laws suffice on the entire coend,
    without assuming every value is natively an injected representative. *)

(** ** 左侧双重生成元

    选择第一个复合族和单个外层 coend。连续使用两次原区分律便覆盖整个 coend，
    不假定每个值在原生表示上均为注入代表。 *)

Section LeftDistinction.
Universes u p.
Context {C D E B : Cat}.
Context (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})).
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HI : !HasProfComp C D E Q P}.
Context {X : @Ob C} {W : @Ob B}.
Context `{HO : !HasCoend SetCat
    (ProfCompKernel R (Q ∘Pr P) X W)}.

(** Doubly injected triples jointly distinguish all outgoing maps. *)

(** 双重注入的三元组联合区分全部出射映射。 *)

Lemma profunctor_triple_left_hom_ext {V : SetC@{u p}}
    (f g : coend[ProfCompKernel R (Q ∘Pr P) X W] →r V)
    (H : ∀ Y Z (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W)),
      f (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z (ιPr[Q; P; Y] (x,y),z)) ≈S
      g (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z (ιPr[Q; P; Y] (x,y),z)))
  : f ≈f g.
Proof.
  apply (@prof_comp_hom_ext C E B R (Q ∘Pr P) X W HO V f g).
  intros Z.
  apply (prof_comp_parameter_hom_ext Q P
    (f ∘r ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z)
    (g ∘r ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z)).
  intros Y [x y] z. exact (H Y Z x y z).
Defined.

End LeftDistinction.

(** ** Descending the Last Two Stages

    Use the same three-stage operation, now fixing its first value and
    descending the last two factors. The left-parameter presentation only
    exchanges coordinates in the original parameterized mediator. *)

(** ** 下降后两段

    使用同一个三段操作，这次固定其第一个值并下降后两个因子。左参数表示只在
    原带参数中介中交换坐标。 *)

Section RightInner.
Universes u p.
Context {C D E B : Cat}.
Context (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})).
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context {X : @Ob C} {W : @Ob B} {V : SetC@{u p}}.
Context (κ : ProfunctorTripleCowedge R Q P X W V).

(** Fixing the first value gives a cowedge of the last composition kernel. *)

(** 固定第一个值，得到最后一个复合核的余楔。 *)

Program Definition ProfunctorTripleRightSlice (Y : @Ob D) (x : P (X,Y))
  : Cowedge (ProfCompKernel R Q Y W) V
  := ProfCompCowedge R Q
      (λ Z, {|func yz := κ Y Z ((x,fst yz),snd yz)|}) _.
Next Obligation.
  intros [y z] [y' z'] [Hy Hz].
  exact (@func_proper _ _ (κ Y Z) ((x,y),z) ((x,y'),z')
    ((reflexivity x,Hy),Hz)).
Defined.
Next Obligation.
  exact (triple_cowedge_gluing_r κ Y Y0 Y' h x x0 y).
Defined.

(** The first value remains a respectful external parameter. *)

(** 第一个值保持为保相等的外部参数。 *)

Global Instance profunctor_triple_right_slice_proper (Y : @Ob D)
  : Proper ([≈S] ==> CowedgeEq) (ProfunctorTripleRightSlice Y).
Proof.
  intros x x' H Z [y z].
  exact (@func_proper _ _ (κ Y Z) ((x,y),z) ((x',y),z)
    ((H,reflexivity y),reflexivity z)).
Defined.

Context `{HI : !HasProfComp D E B R Q}.

(** Descend beside the unchanged first value, with its parameter on the left. *)

(** 在不变的第一个值旁下降，参数位于左侧。 *)

Definition profunctor_triple_right_leg (Y : @Ob D)
  : (P (X,Y) ×S (R ∘Pr Q) (Y,W)) →r V
  := prof_comp_left_parameter_desc R Q (ProfunctorTripleRightSlice Y)
      (profunctor_triple_right_slice_proper Y).

(** The same parameter boundary square transports the first balance law
    through this descent; no intermediate arrow is inverted. *)

(** 同一个参数边界方块将第一个平衡律运输过此次下降，不反转任何中间箭头。 *)

Lemma profunctor_triple_right_balance (Y Y' : @Ob D) (h : Hom Y Y')
    (x : P (X,Y)) (t : (R ∘Pr Q) (Y',W))
  : profunctor_triple_right_leg Y (x,lmap[R ∘Pr Q; h] t) ≈S
      profunctor_triple_right_leg Y' (rmap[P; h] x,t).
Proof.
  pose (μ := λ v : P (X,Y), ProfunctorTripleRightSlice Y' (rmap[P; h] v)).
  assert (Hμ : Proper ([≈S] ==> CowedgeEq) μ).
  { intros v v' Hv. apply profunctor_triple_right_slice_proper.
    exact (@func_proper _ _ (rmap[P; h]) v v' Hv). }
  refine (prof_comp_parameter_boundary R Q μ
    (ProfunctorTripleRightSlice Y) Hμ
    (profunctor_triple_right_slice_proper Y) h (id[W])
    id_resp id_resp _ t x).
  intros Z y z v.
  transitivity (κ Y Z ((v,lmap[Q; h] y),z)).
  - exact (@func_proper _ _ (κ Y Z)
      ((v,lmap[Q; h] y),rmap[R; id[W]] z)
      ((v,lmap[Q; h] y),z)
      (reflexivity _,prof_rmap_id R Z W z)).
  - exact (triple_cowedge_gluing_l κ Y Y' Z h v y z).
Defined.

(** These legs form the outer cowedge for the other parenthesization. *)

(** 这些腿组成另一种括号方式的外层余楔。 *)

Definition ProfunctorTripleRightCowedge
  : Cowedge (ProfCompKernel (R ∘Pr Q) P X W) V
  := ProfCompCowedge (R ∘Pr Q) P
      profunctor_triple_right_leg profunctor_triple_right_balance.

Context `{HO : !HasCoend SetCat
    (ProfCompKernel (R ∘Pr Q) P X W)}.

(** Only the indicated outer coend is needed for the second descent. *)

(** 第二次下降只需要所指的外层 coend。 *)

Definition profunctor_triple_right_desc
  : coend[ProfCompKernel (R ∘Pr Q) P X W] →r V
  := coend⟨ProfunctorTripleRightCowedge⟩.

(** First expose the outer equation with an abstract inner value. *)

(** 先以内层抽象值暴露外层方程。 *)

Lemma profunctor_triple_right_outer_β (Y : @Ob D)
    (x : P (X,Y)) (t : (R ∘Pr Q) (Y,W))
  : profunctor_triple_right_desc
      (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y (x,t)) ≈S
      profunctor_triple_right_leg Y (x,t).
Proof. exact (coend_β ProfunctorTripleRightCowedge Y (x,t)). Defined.

(** Two injections compute to the same original three-stage operation. *)

(** 两次注入计算为同一个原三段操作。 *)

Lemma profunctor_triple_right_β (Y : @Ob D) (Z : @Ob E)
    (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W))
  : profunctor_triple_right_desc
      (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
        (x,ιPr[R; Q; Z] (y,z))) ≈S κ Y Z ((x,y),z).
Proof.
  transitivity (profunctor_triple_right_leg Y (x,ιPr[R; Q; Z] (y,z))).
  - exact (profunctor_triple_right_outer_β Y x (ιPr[R; Q; Z] (y,z))).
  - exact (@prof_comp_left_parameter_β D E B R Q Y W
      (@hasProfCompCoend D E B R Q HI Y W) (P (X,Y)) V
      (ProfunctorTripleRightSlice Y) (profunctor_triple_right_slice_proper Y)
      Z (y,z) x).
Defined.

End RightInner.

(** ** Double Generators on the Right

    Choose the last composition family and one outer coend. The same
    original distinction laws, with the parameter on the left, distinguish
    maps on this whole nested coend. *)

(** ** 右侧双重生成元

    选择最后一个复合族和单个外层 coend。使用左参数的同一原区分律，区分
    整个嵌套 coend 上的映射。 *)

Section RightDistinction.
Universes u p.
Context {C D E B : Cat}.
Context (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})).
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HI : !HasProfComp D E B R Q}.
Context {X : @Ob C} {W : @Ob B}.
Context `{HO : !HasCoend SetCat
    (ProfCompKernel (R ∘Pr Q) P X W)}.

(** Right-associated double generators distinguish outgoing maps. *)

(** 右结合的双重生成元区分出射映射。 *)

Lemma profunctor_triple_right_hom_ext {V : SetC@{u p}}
    (f g : coend[ProfCompKernel (R ∘Pr Q) P X W] →r V)
    (H : ∀ Y Z (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W)),
      f (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y (x,ιPr[R; Q; Z] (y,z))) ≈S
      g (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y (x,ιPr[R; Q; Z] (y,z))))
  : f ≈f g.
Proof.
  apply (@prof_comp_hom_ext C D B (R ∘Pr Q) P X W HO V f g).
  intros Y.
  apply (prof_comp_left_parameter_hom_ext R Q
    (f ∘r ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y)
    (g ∘r ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y)).
  intros Z [y z] x. exact (H Y Z x y z).
Defined.

End RightDistinction.
