From Cats.Set Require Export
  Pi.
From Cats Require Import
  Cat.Core
  Instance.Set.Core.

(** * Dependent Sets and Coherent Families *)

(** * 依赖集合与相干族 *)

(** ** Coherent Families over Setoids

    Transport is a respectful map. The laws compare its action on elements,
    never equality witnesses themselves. Quantifying over any witnesses of the
    same base equivalences expresses coherence over a setoid: the composite
    law accepts any witness r, and witness independence follows from it. *)

(** ** 广集上的相干族

    运输是保相等映射，定律只比较其在元素上的作用，不比较相等见证本身。对同一基
    底相等的任意见证量化表达相干性：复合律接受任意见证 r，见证独立性由此导出。 *)

Record FamS (X : SetC)
  :=
  { fam :> X → SetC
  ; transpS {x y : X} : x ≈S y → fam x →r fam y
  ; transpS_id {x} (p : x ≈S x) (v : fam x)
    : transpS p v ≈S v
  ; transpS_comp {x y z} (p : x ≈S y) (q : y ≈S z) (r : x ≈S z)
      (v : fam x)
    : transpS r v ≈S transpS q (transpS p v)
  }.

Arguments transpS {_} _ {_ _} _.
Arguments transpS_id {_} _ {_} _ _.
Arguments transpS_comp {_} _ {_ _ _} _ _ _ _.

(** The chosen reflexive equality witness of a setoid element. *)

(** 广集元素的选定自反相等见证。 *)

Theorem reflS {X : SetC} {x : X}
  : x ≈S x.
Proof. reflexivity. Qed.

(** Different witnesses induce equivalent maps; no proof irrelevance is used. *)

(** 不同见证诱导等价映射，不使用证明无关性。 *)

Theorem transpS_witness_independent {X} (Y : FamS X) {x y} (p q : x ≈S y)
  : transpS Y p ≈f transpS Y q.
Proof.
  intros v. assert (e : x ≈S x) by reflexivity.
  transitivity (transpS Y q (transpS Y e v)).
  - exact (transpS_comp Y e q p v).
  - apply func_proper. apply transpS_id.
Qed.

(** Transport along opposite base equalities cancels on elements. *)

(** 沿反向基底相等的运输在元素上抵消。 *)

Theorem transpS_inv {X} (Y : FamS X) {x y}
    (p : x ≈S y) (q : y ≈S x) (v : Y x)
  : transpS Y q (transpS Y p v) ≈S v.
Proof.
  assert (e : x ≈S x) by reflexivity.
  transitivity (transpS Y e v).
  - symmetry. exact (transpS_comp Y p q e v).
  - apply transpS_id.
Qed.

(** Fiber isomorphisms are consequences of coherent transport. *)

(** 纤维同构由相干运输导出。 *)

Definition transpS_iso {X} (Y : FamS X) {x y} (p : x ≈S y)
  : Y x ≅[SetCat] Y y.
Proof.
  assert (q : y ≈S x) by (symmetry; exact p).
  exists (transpS Y p), (transpS Y q); split; intros v;
    apply transpS_inv.
Defined.

(** The constant coherent family with identity transport. *)

(** 运输为恒等的常相干族。 *)

Program Definition ConstFamS (X A : SetC)
  : FamS X
  :=
  {|fam _ := A
  ; transpS _ _ _ := id_resp (X := A)
  |}.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Reindexing keeps the fiber over the image and transports along the image
    of the base equivalence. Coherence follows from the original family. *)

(** 重索引保留像处的纤维，并沿基底相等的像运输；相干性来自原族。 *)

Program Definition ReindexFamS {X Y : SetC} (A : FamS Y) (f : X →r Y)
  : FamS X
  :=
  {|fam x := A (f x)
  ; transpS x y p := transpS A (@func_proper _ _ f x y p)
  |}.
Next Obligation. apply transpS_id. Defined.
Next Obligation. apply transpS_comp. Defined.

Notation "A '[' f ']S'" := (ReindexFamS A f)
  (at level 8, left associativity, format "A [ f ]S") : cat_scope.



(** ** Dependent Sums

    Both coordinates are compared by setoid equivalence. The first witness
    supplies the transport needed to compare the second coordinates. *)

(** ** 依赖和

    两个坐标均按广集相等比较，第一个见证提供比较第二个坐标所需的运输。 *)

Definition SigEq {X : SetC} {Y : FamS X} (a b : ∃ x : X, Y x)
  := ∃ p : a.1 ≈S b.1, transpS Y p a.2 ≈S b.2.

Infix "≈ΣS" := SigEq (at level 50).

(** [SigEq] is an equivalence relation. *)

(** [SigEq] 是等价关系。 *)

Global Instance SigEq_Equivalence {X Y}
  : Equivalence (@SigEq X Y).
Proof.
  split.
  - intros [x v]. assert (p : x ≈S x) by reflexivity.
    exists p. apply transpS_id.
  - intros [x v] [y w] [p Hp].
    assert (q : y ≈S x) by (symmetry; exact p).
    exists q. transitivity (transpS Y q (transpS Y p v)).
    + apply func_proper. symmetry. exact Hp.
    + apply transpS_inv.
  - intros [x v] [y w] [z u] [p Hp] [q Hq].
    assert (r : x ≈S z) by (transitivity y; assumption).
    exists r. transitivity (transpS Y q (transpS Y p v)).
    + exact (transpS_comp Y p q r v).
    + transitivity (transpS Y q w).
      * apply func_proper. exact Hp.
      * exact Hq.
Qed.

(** The dependent-sum setoid, comparing second coordinates after transport. *)

(** 在运输后比较第二坐标的依赖和广集。 *)

Program Canonical SigS (X : SetC) (Y : FamS X)
  :=
  {|carrier := ∃ x : X, Y x
  ; carrier_equiv := SigEq
  |}.

(** The respectful first projection from a dependent-sum setoid. *)

(** 依赖和广集的保相等第一投影。 *)

Program Definition sig_base_resp {X} (Y : FamS X)
  : SigS X Y →r X
  :=
  {|func a := a.1
  |}.
Next Obligation.
  intros a b [p Hp]. exact p.
Defined.

(** ** Fibers of Setoid Maps

    Every respectful map of setoids gives a coherent family of fibers.
    Membership witnesses are retained as data; fiber equality compares only
    their underlying elements. *)

(** ** 广集映射的纤维

    每个保相等映射给出相干纤维族。成员见证作为数据保留，纤维相等只比较底层元素。 *)

Program Definition FiberS {E X : SetC} (f : E →r X) (x : X)
  : SetC
  :=
  {|carrier := ∃ u : E, f u ≈S x
  ; carrier_equiv a b := a.1 ≈S b.1
  |}.
Next Obligation.
  split.
  - intros a. reflexivity.
  - intros a b H. symmetry. exact H.
  - intros a b c H1 H2. transitivity b.1; assumption.
Defined.

(** Transport fiber membership along equality of target elements. *)

(** 沿目标元素相等运输纤维成员资格。 *)

Program Definition fiber_transp_resp {E X : SetC} (f : E →r X)
    {x y : X} (p : x ≈S y)
  : FiberS f x →r FiberS f y
  :=
  {|func a := (a.1; _)
  |}.
Next Obligation. transitivity x; [exact a.2 | exact p]. Defined.
Next Obligation. intros a b H. exact H. Defined.

(** The coherent family of fibers of a respectful setoid map. *)

(** 保相等广集映射的相干纤维族。 *)

Program Definition FiberFamS {E X : SetC} (f : E →r X)
  : FamS X
  :=
  {|fam := FiberS f
  ; transpS x y p := fiber_transp_resp f p
  |}.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** The total space recovers the domain of the original map, up to setoid
    isomorphism. This also shows that transport-based sum equality identifies
    equivalent representatives without identifying their witness data. *)

(** 全空间在广集同构意义下恢复原映射的定义域；基于运输的和相等识别等价代表而不
    识别其见证数据。 *)

Program Definition fiber_total_proj_resp {E X : SetC} (f : E →r X)
  : SigS X (FiberFamS f) →r E
  :=
  {|func a := a.2.1
  |}.
Next Obligation.
  intros a b [p Hp]. exact Hp.
Defined.

(** Send an element to its image together with its reflexive fiber witness. *)

(** 将元素送到其像及自反纤维见证。 *)

Program Definition fiber_total_intro_resp {E X : SetC} (f : E →r X)
  : E →r SigS X (FiberFamS f)
  :=
  {|func e := (f e; (e; reflS (x := f e)))
  |}.
Next Obligation.
  intros e e' H.
  assert (p : f e ≈S f e') by (apply func_proper; exact H).
  exists p. exact H.
Defined.

(** The total space of a map's fiber family is isomorphic to its domain. *)

(** 映射的纤维族全空间同构于该映射的定义域。 *)

Theorem fiber_total_iso {E X : SetC} (f : E →r X)
  : SigS X (FiberFamS f) ≅[SetCat] E.
Proof.
  exists (fiber_total_proj_resp f), (fiber_total_intro_resp f); split.
  - intros [x [e q]]. exists q. change (e ≈S e). reflexivity.
  - intros e. change (e ≈S e). reflexivity.
Defined.
