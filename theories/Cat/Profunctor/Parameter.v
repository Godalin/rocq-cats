From Cats Require Export
  Cat.Profunctor.ComposeUniversal.
From Cats Require Import
  Cat.Core
  Cat.Profunctor.ComposeMap
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.CoendProduct.

Local Open Scope prof_scope.

(** * Balanced Composition with an External Parameter

    Ordinary balanced operations give cowedges of the composition kernel.
    A fixed setoid parameter remains external during descent. All mediators
    and uniqueness laws below reuse the chosen coend/product theory; no
    function object, global composition choice or value-bound order is needed. *)

(** * 带外部参数的平衡复合

    通常的平衡操作给出复合核的余楔。固定广集参数在下降时保持外部形式。
    以下中介与唯一性律均复用选定 coend／积理论，不要求函数对象、全局复合选择
    或值界之间的大小次序。 *)

(** ** Balanced Legs and Cowedges

    Fix the two profunctors and outer objects. An intermediate arrow may
    act on either factor. This ordinary balance equation is equivalent to
    the original kernel cowedge equation, without a chosen coend. *)

(** ** 平衡腿与余楔

    固定两个 profunctor 及外部对象，中间箭头可作用于任一因子。通常的平衡方程
    与原核的余楔方程等价，不需要选定 coend。 *)

Section BalancedLegs.
Universes u p.
Context {C D E : Cat}.
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context {X : @Ob C} {Z : @Ob E} {W : SetC@{u p}}.

(** Every kernel cowedge balances the two one-sided intermediate actions. *)

(** 每个核余楔平衡中间指标的两个单侧作用。 *)

Lemma prof_comp_cowedge_gluing
    (κ : Cowedge (ProfCompKernel Q P X Z) W)
    {Y Y' : @Ob D} (h : Hom Y Y')
    (x : P (X,Y)) (y : Q (Y',Z))
  : κ Y (x,lmap[Q; h] y) ≈S κ Y' (rmap[P; h] x,y).
Proof.
  transitivity (κ Y (dimap[P; id[X]; id[Y]] x,lmap[Q; h] y)).
  - apply func_proper. split; [| reflexivity].
    symmetry. exact (prof_dimap_id P X Y x).
  - transitivity (κ Y' (rmap[P; h] x,dimap[Q; id[Y']; id[Z]] y)).
    + exact (cowedge_comm κ h (x,y)).
    + apply func_proper. split; [reflexivity |].
      exact (prof_dimap_id Q Y' Z y).
Defined.

(** Balanced respectful legs form a cowedge with those same legs. The
    identity actions are removed using the original profunctor laws. *)

(** 平衡的尊重腿组成具有原腿的余楔，恒等作用由原 profunctor 定律消去。 *)

Program Definition ProfCompCowedge
    (κ : ∀ Y : @Ob D, (P (X,Y) ×S Q (Y,Z)) →r W)
    (Hκ : ∀ (Y Y' : @Ob D) (h : Hom Y Y')
      (x : P (X,Y)) (y : Q (Y',Z)),
      κ Y (x,lmap[Q; h] y) ≈S κ Y' (rmap[P; h] x,y))
  : Cowedge (ProfCompKernel Q P X Z) W
  := CowedgeOf (D := SetCat) (F := ProfCompKernel Q P X Z)
      (W := W) κ _.
Next Obligation.
  intros [x y].
  transitivity (κ X0 (x,lmap[Q; f] y)).
  - apply func_proper. split; [| reflexivity].
    exact (prof_dimap_id P X X0 x).
  - transitivity (κ Y (rmap[P; f] x,y)).
    + exact (Hκ X0 Y f x y).
    + apply func_proper. split; [reflexivity |].
      symmetry. exact (prof_dimap_id Q Y Z y).
Defined.

(** Reconstructing a cowedge keeps its original components; no equality
    of the law witnesses is required. *)

(** 重构余楔保留原分量，不要求定律见证相等。 *)

Lemma prof_comp_cowedge_η
    (κ : Cowedge (ProfCompKernel Q P X Z) W)
  : ProfCompCowedge κ
      (λ Y Y' h x y, prof_comp_cowedge_gluing κ h x y) ≈CW κ.
Proof. intros Y xy. reflexivity. Defined.

End BalancedLegs.

(** ** Descent Beside a Fixed Setoid

    Choose only the single composition coend at the specified outer ends.
    A respectful family of its cowedges descends while keeping its parameter
    on the right; exchange coordinates to obtain the left presentation. *)

(** ** 在固定广集旁下降

    只选择指定外端处的单个复合 coend。保持相等的余楔族下降时保留右侧参数；
    交换坐标便得到左侧表示。 *)

Section ParameterDescent.
Universes u p.
Context {C D E : Cat}.
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context {X : @Ob C} {Z : @Ob E}.
Context `{HC : !HasCoend SetCat (ProfCompKernel Q P X Z)}.
Context {V W : SetC@{u p}}.

(** Parameterized descent is the existing coend mediator at each parameter. *)

(** 带参数下降就是每个参数处已有的 coend 中介。 *)

Definition prof_comp_parameter_desc
    (κ : V → Cowedge (ProfCompKernel Q P X Z) W)
    (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
  : (coend[ProfCompKernel Q P X Z] ×S V) →r W
  := coend_parameter_desc κ Hκ.

(** Each original generating pair is evaluated at the unchanged parameter. *)

(** 每个原生成对在不变参数处求值。 *)

Lemma prof_comp_parameter_β
    (κ : V → Cowedge (ProfCompKernel Q P X Z) W)
    (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
    (Y : @Ob D) (xy : P (X,Y) ×S Q (Y,Z)) (v : V)
  : prof_comp_parameter_desc κ Hκ (ιPr[Q; P; Y] xy,v)
    ≈S κ v Y xy.
Proof. exact (coend_parameter_β κ Hκ Y xy v). Defined.

(** Paired generators distinguish all respectful parameterized maps. *)

(** 配对生成元区分全部保持参数相等的映射。 *)

Lemma prof_comp_parameter_hom_ext
    (f g : (coend[ProfCompKernel Q P X Z] ×S V) →r W)
    (H : ∀ Y (xy : P (X,Y) ×S Q (Y,Z)) (v : V),
      f (ιPr[Q; P; Y] xy,v) ≈S g (ιPr[Q; P; Y] xy,v))
  : f ≈f g.
Proof. exact (coend_parameter_hom_ext f g H). Defined.

(** The generator equation uniquely determines descent. *)

(** 生成元方程唯一决定下降。 *)

Lemma prof_comp_parameter_unique
    (κ : V → Cowedge (ProfCompKernel Q P X Z) W)
    (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
    (f : (coend[ProfCompKernel Q P X Z] ×S V) →r W)
    (H : ∀ Y (xy : P (X,Y) ×S Q (Y,Z)) (v : V),
      f (ιPr[Q; P; Y] xy,v) ≈S κ v Y xy)
  : f ≈f prof_comp_parameter_desc κ Hκ.
Proof. exact (coend_parameter_unique κ Hκ f H). Defined.

(** Pointwise equal cowedge families give equal descents, independently
    of their respectfulness witnesses. *)

(** 逐点相等的余楔族给出相等下降，不依赖各自的保相等见证。 *)

Lemma prof_comp_parameter_proper
    (κ μ : V → Cowedge (ProfCompKernel Q P X Z) W)
    (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
    (Hμ : Proper ([≈S] ==> CowedgeEq) μ)
    (H : ∀ v, κ v ≈CW μ v)
  : prof_comp_parameter_desc κ Hκ ≈f
      prof_comp_parameter_desc μ Hμ.
Proof. exact (coend_parameter_desc_proper κ μ Hκ Hμ H). Defined.

(** Exchange coordinates without another mediator or universal proof. *)

(** 交换坐标，不引入另一中介或泛证明。 *)

Program Definition prof_comp_left_parameter_desc
    (κ : V → Cowedge (ProfCompKernel Q P X Z) W)
    (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
  : (V ×S coend[ProfCompKernel Q P X Z]) →r W
  :=
  {|func vz := prof_comp_parameter_desc κ Hκ (snd vz,fst vz)
  |}.
Next Obligation.
  intros [v z] [v' z'] [Hv Hz].
  exact (@func_proper _ _ (prof_comp_parameter_desc κ Hκ)
    (z,v) (z',v') (Hz,Hv)).
Defined.

(** Left-parameter descent has the same original injection equation. *)

(** 左参数下降满足同一个原注入方程。 *)

Lemma prof_comp_left_parameter_β
    (κ : V → Cowedge (ProfCompKernel Q P X Z) W)
    (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
    (Y : @Ob D) (xy : P (X,Y) ×S Q (Y,Z)) (v : V)
  : prof_comp_left_parameter_desc κ Hκ (v,ιPr[Q; P; Y] xy)
    ≈S κ v Y xy.
Proof. exact (prof_comp_parameter_β κ Hκ Y xy v). Defined.

(** Left-paired generators distinguish maps by the original right-side law. *)

(** 由原右侧定律可知左配对生成元区分映射。 *)

Lemma prof_comp_left_parameter_hom_ext
    (f g : (V ×S coend[ProfCompKernel Q P X Z]) →r W)
    (H : ∀ Y (xy : P (X,Y) ×S Q (Y,Z)) (v : V),
      f (v,ιPr[Q; P; Y] xy) ≈S g (v,ιPr[Q; P; Y] xy))
  : f ≈f g.
Proof.
  unshelve epose (f' := ({|func zv := f (snd zv,fst zv)|}
    : (coend[ProfCompKernel Q P X Z] ×S V) →r W)).
  { intros [z v] [z' v'] [Hz Hv]. apply func_proper. exact (Hv,Hz). }
  unshelve epose (g' := ({|func zv := g (snd zv,fst zv)|}
    : (coend[ProfCompKernel Q P X Z] ×S V) →r W)).
  { intros [z v] [z' v'] [Hz Hv]. apply func_proper. exact (Hv,Hz). }
  intros [v z]. exact (prof_comp_parameter_hom_ext f' g' H (z,v)).
Defined.

(** Left descent is likewise uniquely determined on paired generators. *)

(** 左下降同样由配对生成元上的值唯一决定。 *)

Lemma prof_comp_left_parameter_unique
    (κ : V → Cowedge (ProfCompKernel Q P X Z) W)
    (Hκ : Proper ([≈S] ==> CowedgeEq) κ)
    (f : (V ×S coend[ProfCompKernel Q P X Z]) →r W)
    (H : ∀ Y (xy : P (X,Y) ×S Q (Y,Z)) (v : V),
      f (v,ιPr[Q; P; Y] xy) ≈S κ v Y xy)
  : f ≈f prof_comp_left_parameter_desc κ Hκ.
Proof.
  apply prof_comp_left_parameter_hom_ext. intros Y xy v.
  transitivity (κ v Y xy); [apply H |].
  symmetry. apply prof_comp_left_parameter_β.
Defined.

End ParameterDescent.

(** ** Transporting a Parameterized Operation Square

    Only two individual endpoint coends are supplied. Change both input
    profunctors, the external parameter and the output. A commuting square
    on original pairs extends to all coend values, including non-generators. *)

(** ** 运输带参数操作方块

    只给出两个端点处的单独 coend，同时改变两个输入 profunctor、外部参数与输出。
    原对上的交换方块延拓到全部 coend 值，包括非生成形式的值。 *)

Section ParameterChange.
Universes u p.
Context {C D E : Cat}.
Context {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}.
Context {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}.
Context {X X' : @Ob C} {Z Z' : @Ob E}.
Context `{HF : !HasCoend SetCat (ProfCompKernel Q P X Z)}.
Context `{HG : !HasCoend SetCat (ProfCompKernel Q' P' X' Z')}.
Context {V V' W W' : SetC@{u p}}.
Context (κ : V → Cowedge (ProfCompKernel Q P X Z) W).
Context (μ : V' → Cowedge (ProfCompKernel Q' P' X' Z') W').
Context (Hκ : Proper ([≈S] ==> CowedgeEq) κ).
Context (Hμ : Proper ([≈S] ==> CowedgeEq) μ).
Context (δ : ProfCompKernel Q P X Z ⇒
    ProfCompKernel Q' P' X' Z') (k : V →r V') (ψ : W →r W').

(** One generator square suffices; the coend map and parameterized
    distinction law supply its unique extension. *)

(** 一个生成元方块已充分，coend 映射与带参数区分律给出其唯一延拓。 *)

Lemma prof_comp_parameter_map
    (H : ∀ Y (xy : P (X,Y) ×S Q (Y,Z)) (v : V),
      μ (k v) Y (δ (Y,Y) xy) ≈S ψ (κ v Y xy))
    (z : coend[ProfCompKernel Q P X Z]) (v : V)
  : prof_comp_parameter_desc Q' P' μ Hμ
      (coend_map δ z,k v) ≈S
      ψ (prof_comp_parameter_desc Q P κ Hκ (z,v)).
Proof.
  pose (m := @coend_map D SetCat _ _ HF HG δ).
  unshelve epose (f := ({|func zv :=
    prof_comp_parameter_desc Q' P' μ Hμ (m (fst zv),k (snd zv))|}
    : (coend[ProfCompKernel Q P X Z] ×S V) →r W')).
  { intros [a b] [a' b'] [Ha Hb].
    exact (@func_proper _ _
      (prof_comp_parameter_desc Q' P' μ Hμ)
      (m a,k b) (m a',k b')
      (@func_proper _ _ m a a' Ha,@func_proper _ _ k b b' Hb)). }
  pose (g := ψ ∘r prof_comp_parameter_desc Q P κ Hκ).
  assert (HE : f ≈f g).
  { apply (prof_comp_parameter_hom_ext Q P). intros Y xy w.
    transitivity (prof_comp_parameter_desc Q' P' μ Hμ
      (ιPr[Q'; P'; Y] (δ (Y,Y) xy),k w)).
    - exact (@func_proper _ _
        (prof_comp_parameter_desc Q' P' μ Hμ)
        (m (ιPr[Q; P; Y] xy),k w)
        (ιPr[Q'; P'; Y] (δ (Y,Y) xy),k w)
        (coend_map_β δ Y xy,reflexivity (k w))).
    - transitivity (μ (k w) Y (δ (Y,Y) xy)).
      + apply prof_comp_parameter_β.
      + transitivity (ψ (κ w Y xy)); [apply H |].
        exact (@func_proper _ _ ψ _ _
          (symmetry (prof_comp_parameter_β Q P κ Hκ Y xy w))). }
  exact (HE (z,v)).
Defined.

(** The same square in the left-parameter presentation has no new proof. *)

(** 左参数表示中的同一个方块不需要新证明。 *)

Lemma prof_comp_left_parameter_map
    (H : ∀ Y (xy : P (X,Y) ×S Q (Y,Z)) (v : V),
      μ (k v) Y (δ (Y,Y) xy) ≈S ψ (κ v Y xy))
    (v : V) (z : coend[ProfCompKernel Q P X Z])
  : prof_comp_left_parameter_desc Q' P' μ Hμ
      (k v,coend_map δ z) ≈S
      ψ (prof_comp_left_parameter_desc Q P κ Hκ (v,z)).
Proof. exact (prof_comp_parameter_map H z v). Defined.

End ParameterChange.

(** ** Input and Boundary Squares

    Specialize the same kernel-map square to transformations of the input
    profunctors or to changes of the outer objects. Neither specialization
    requires choices away from the two indicated endpoint coends. *)

(** ** 输入与边界方块

    将同一个核映射方块分别用于输入 profunctor 的变换和外部对象的改变。
    两种特化均不要求在所指两端点 coend 以外作选择。 *)

Section InputChange.
Universes u p.
Context {C D E : Cat}.
Context {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}.
Context {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}.
Context {X : @Ob C} {Z : @Ob E}.
Context `{HF : !HasCoend SetCat (ProfCompKernel Q P X Z)}.
Context `{HG : !HasCoend SetCat (ProfCompKernel Q' P' X Z)}.
Context {V V' W W' : SetC@{u p}}.
Context (κ : V → Cowedge (ProfCompKernel Q P X Z) W).
Context (μ : V' → Cowedge (ProfCompKernel Q' P' X Z) W').
Context (Hκ : Proper ([≈S] ==> CowedgeEq) κ).
Context (Hμ : Proper ([≈S] ==> CowedgeEq) μ).
Context (α : P ⇒ P') (β : Q ⇒ Q') (k : V →r V') (ψ : W →r W').

(** Input transformations act on each value in execution order. *)

(** 输入变换按执行顺序分别作用于各值。 *)

Lemma prof_comp_parameter_change
    (H : ∀ Y (x : P (X,Y)) (y : Q (Y,Z)) (v : V),
      μ (k v) Y (α (X,Y) x,β (Y,Z) y) ≈S ψ (κ v Y (x,y)))
    (z : coend[ProfCompKernel Q P X Z]) (v : V)
  : prof_comp_parameter_desc Q' P' μ Hμ
      (coend_map (ProfCompInputN β α X Z) z,k v) ≈S
      ψ (prof_comp_parameter_desc Q P κ Hκ (z,v)).
Proof.
  refine (prof_comp_parameter_map κ μ Hκ Hμ
    (ProfCompInputN β α X Z) k ψ _ z v).
  intros Y [x y] w. exact (H Y x y w).
Defined.

End InputChange.

(** ** Changing the Outer Ends

    Keep the two profunctors and change only their outer objects, together
    with the external parameter and output. In particular, an operation's
    context naturality can be checked before descent. *)

(** ** 改变外端

    固定两个 profunctor，只改变其外部对象以及外部参数与输出。
    特别地，操作的上下文自然性可以在下降前检查。 *)

Section BoundaryChange.
Universes u p.
Context {C D E : Cat}.
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context {X X' : @Ob C} {Z Z' : @Ob E}.
Context `{HF : !HasCoend SetCat (ProfCompKernel Q P X Z)}.
Context `{HG : !HasCoend SetCat (ProfCompKernel Q P X' Z')}.
Context {V V' W W' : SetC@{u p}}.
Context (κ : V → Cowedge (ProfCompKernel Q P X Z) W).
Context (μ : V' → Cowedge (ProfCompKernel Q P X' Z') W').
Context (Hκ : Proper ([≈S] ==> CowedgeEq) κ).
Context (Hμ : Proper ([≈S] ==> CowedgeEq) μ).
Context (f : Hom X' X) (g : Hom Z Z') (k : V →r V') (ψ : W →r W').

(** The original outer actions and the parameter change commute with
    descent whenever they commute on each original pair. *)

(** 原外端作用与参数改变只要在每个原对上与操作交换，便与下降交换。 *)

Lemma prof_comp_parameter_boundary
    (H : ∀ Y (x : P (X,Y)) (y : Q (Y,Z)) (v : V),
      μ (k v) Y (lmap[P; f] x,rmap[Q; g] y) ≈S ψ (κ v Y (x,y)))
    (z : coend[ProfCompKernel Q P X Z]) (v : V)
  : prof_comp_parameter_desc Q P μ Hμ
      (coend_map (ProfCompBoundaryN Q P f g) z,k v) ≈S
      ψ (prof_comp_parameter_desc Q P κ Hκ (z,v)).
Proof.
  refine (prof_comp_parameter_map κ μ Hκ Hμ
    (ProfCompBoundaryN Q P f g) k ψ _ z v).
  intros Y [x y] w. exact (H Y x y w).
Defined.

End BoundaryChange.
