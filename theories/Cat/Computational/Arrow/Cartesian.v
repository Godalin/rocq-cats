From Cats Require Export
  Cat.Computational.Arrow.Core
  Cat.Terminal
  Cat.Monoidal.Cartesian
  Cat.Product.Transport.

Local Open Scope computation_scope.

(** * Cartesian Operations for Computational Arrows

    The monoidal action remains the only chosen computation structure.
    Finite products supply exchange, projection and duplication, from which
    the familiar Haskell operations and laws are derived. *)

(** * 计算 Arrow 的笛卡尔运算

    幺半作用仍是唯一选定的计算结构。有限积提供交换、投影及复制，从中导出
    熟悉的 Haskell 运算及定律。 *)

(** Expose the chosen left-context action at ordinary product endpoints. *)

(** 在通常积端点上暴露选定左上下文作用。 *)

Definition arrow_second {C K : Cat}
    `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP))
    {X Y : @Ob C} (Z : @Ob C) (f : Hom (A X) (A Y))
  : Hom (A (Z × X)%ob) (A (Z × Y)%ob)
  := context[A; Z; f].

Notation "'second[' A ';' f ';' Z ']'" := (arrow_second A Z f)
  : computation_scope.

(** Exchange the ordinary factors before and after the left-context action. *)

(** 在左上下文作用前后交换通常因子。 *)

Definition arrow_first {C K : Cat}
    `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP))
    {X Y : @Ob C} (Z : @Ob C) (f : Hom (A X) (A Y))
  : Hom (A (X × Z)%ob) (A (Y × Z)%ob)
  := arr[A; ⟨π2, π1⟩] ∘ second[A; f; Z] ∘ arr[A; ⟨π2, π1⟩].

Notation "'first[' A ';' f ';' Z ']'" := (arrow_first A Z f)
  : computation_scope.

Section Cartesian.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** The derived operations respect computation equality. *)

(** 导出运算保持计算相等。 *)

Global Instance arrow_second_proper {X Y : @Ob C} (Z : @Ob C)
  : Proper (HomEq ==> HomEq) (@arrow_second C K HT HP A X Y Z).
Proof. exact (arrow_context_proper A Z). Qed.

(** Right-context action also respects computation equality. *)

(** 右上下文作用也保持计算相等。 *)

Global Instance arrow_first_proper {X Y : @Ob C} (Z : @Ob C)
  : Proper (HomEq ==> HomEq) (@arrow_first C K HT HP A X Y Z).
Proof. intros f g H. unfold arrow_first. rewrite H. reflexivity. Qed.

(** Pure exchange is involutive by the product equations. *)

(** 由积方程，纯交换为对合。 *)

Lemma arrow_exchange_inv (X Y : @Ob C)
  : arr[A; (⟨π2, π1⟩ : Hom (Y × X) (X × Y))] ∘
      arr[A; (⟨π2, π1⟩ : Hom (X × Y) (Y × X))] ≈ id.
Proof.
  rewrite <- functor_comp, product_comp_r, product_β1, product_β2,
    product_pair_η, functor_id. reflexivity.
Qed.

(** Left-context action on pure arrows is the ordinary product map. *)

(** 纯箭头上的左上下文作用就是通常积映射。 *)

Lemma arrow_second_arr {X Y : @Ob C} (f : Hom X Y) (Z : @Ob C)
  : second[A; arr[A; f]; Z] ≈ arr[A; @id Z × f].
Proof.
  pose proof (arrow_context_arr A Z f) as H.
  rewrite cartesian_tensor_map in H. exact H.
Qed.

(** Left-context action preserves sequencing. *)

(** 左上下文作用保持顺序组合。 *)

Lemma arrow_second_comp {X Y W : @Ob C}
    (g : Hom (A Y) (A W)) (f : Hom (A X) (A Y)) (Z : @Ob C)
  : second[A; g ∘ f; Z] ≈ second[A; g; Z] ∘ second[A; f; Z].
Proof. exact (arrow_context_comp A Z g f). Qed.

(** Ordinary context maps commute with left-context action. *)

(** 通常上下文映射与左上下文作用交换。 *)

Lemma arrow_second_natural {X Y Z W : @Ob C}
    (f : Hom (A X) (A Y)) (h : Hom Z W)
  : arr[A; h × @id Y] ∘ second[A; f; Z] ≈
      second[A; f; W] ∘ arr[A; h × @id X].
Proof.
  pose proof (arrow_context_natural A f h) as H.
  rewrite !cartesian_tensor_map in H. exact H.
Qed.

(** Pure right-context extension is an ordinary product map. *)

(** 纯右上下文扩展就是通常积映射。 *)

Lemma arrow_first_arr {X Y : @Ob C} (f : Hom X Y) (Z : @Ob C)
  : first[A; arr[A; f]; Z] ≈ arr[A; f × @id Z].
Proof.
  unfold arrow_first. rewrite arrow_second_arr, <- !functor_comp.
  apply functor_fmap_proper.
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

(** Right-context extension preserves sequence order. *)

(** 右上下文扩展保持顺序。 *)

Lemma arrow_first_comp {X Y W : @Ob C}
    (g : Hom (A Y) (A W)) (f : Hom (A X) (A Y)) (Z : @Ob C)
  : first[A; g ∘ f; Z] ≈ first[A; g; Z] ∘ first[A; f; Z].
Proof.
  unfold arrow_first. rewrite arrow_second_comp, !comp_assoc.
  rewrite <- (comp_assoc
    arr[A; (⟨π2, π1⟩ : Hom (Y × Z) (Z × Y))]),
    (arrow_exchange_inv Z Y), comp_id_l.
  reflexivity.
Qed.

(** Discarding an ordinary left context follows from its naturality into
    the terminal context and the monoidal unit law. *)

(** 丢弃通常左上下文，来自到终上下文的自然性及幺半单位律。 *)

Lemma arrow_second_projection {X Y : @Ob C}
    (f : Hom (A X) (A Y)) (Z : @Ob C)
  : arr[A; (π2 : Hom (Z × Y) Y)] ∘ second[A; f; Z] ≈
      f ∘ arr[A; (π2 : Hom (Z × X) X)].
Proof.
  pose proof (arrow_context_unit A f) as Hu.
  change (arr[A; (π2 : Hom (1 × Y) Y)] ∘ second[A; f; 1] ≈
    f ∘ arr[A; (π2 : Hom (1 × X) X)]) in Hu.
  pose proof (arrow_second_natural f (! : Hom Z 1)) as Hn.
  transitivity ((arr[A; (π2 : Hom (1 × Y) Y)] ∘
    arr[A; (! : Hom Z 1) × @id Y]) ∘ second[A; f; Z]).
  - rewrite <- functor_comp, cross_η, product_β2, comp_id_l. reflexivity.
  - rewrite comp_assoc, Hn, <- comp_assoc, Hu,
      comp_assoc, <- functor_comp, cross_η, product_β2, comp_id_l.
    reflexivity.
Qed.

(** Discarding the right context recovers the original computation. *)

(** 丢弃右上下文，恢复原计算。 *)

Lemma arrow_first_projection {X Y : @Ob C}
    (f : Hom (A X) (A Y)) (Z : @Ob C)
  : arr[A; (π1 : Hom (Y × Z) Y)] ∘ first[A; f; Z] ≈
      f ∘ arr[A; (π1 : Hom (X × Z) X)].
Proof.
  unfold arrow_first. rewrite <- !comp_assoc, <- functor_comp, product_β1.
  rewrite arrow_second_projection,
    comp_assoc, <- functor_comp, product_β2. reflexivity.
Qed.

(** Ordinary maps of the right context commute with the computation. *)

(** 右上下文的通常映射与计算交换。 *)

Lemma arrow_first_natural {X Y Z W : @Ob C}
    (f : Hom (A X) (A Y)) (h : Hom Z W)
  : arr[A; @id Y × h] ∘ first[A; f; Z] ≈
      first[A; f; W] ∘ arr[A; @id X × h].
Proof.
  assert (Ho : arr[A; @id Y × h] ∘
    arr[A; (⟨π2, π1⟩ : Hom (Z × Y) (Y × Z))] ≈
    arr[A; (⟨π2, π1⟩ : Hom (W × Y) (Y × W))] ∘
    arr[A; h × @id Y]).
  { rewrite <- !functor_comp. apply functor_fmap_proper.
    repeat first [rewrite cross_η | rewrite product_comp_r |
      rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
      rewrite comp_id_l | rewrite comp_id_r]. reflexivity. }
  assert (Hi : arr[A; h × @id X] ∘
    arr[A; (⟨π2, π1⟩ : Hom (X × Z) (Z × X))] ≈
    arr[A; (⟨π2, π1⟩ : Hom (X × W) (W × X))] ∘
    arr[A; @id X × h]).
  { rewrite <- !functor_comp. apply functor_fmap_proper.
    repeat first [rewrite cross_η | rewrite product_comp_r |
      rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
      rewrite comp_id_l | rewrite comp_id_r]. reflexivity. }
  unfold arrow_first. rewrite <- !comp_assoc, Ho, !comp_assoc.
  rewrite <- (comp_assoc arr[A; h × @id Y] (second[A; f; Z])
    arr[A; (⟨π2, π1⟩ : Hom (X × Z) (Z × X))]),
    arrow_second_natural, !comp_assoc, Hi. reflexivity.
Qed.

(** Expand two left contexts using the selected associator and its inverse. *)

(** 用选定结合子及其逆展开两个左上下文。 *)

Lemma arrow_second_nested {X Y : @Ob C}
    (f : Hom (A X) (A Y)) (Z W : @Ob C)
  : second[A; second[A; f; W]; Z] ≈
      arr[A; (@product_assoc C HP Z W Y).1] ∘
      second[A; f; (Z × W)%ob] ∘
      arr[A; (@product_assoc C HP Z W X).2.1].
Proof.
  pose proof (arrow_context_assoc A (Z := Z) (W := W) f) as H.
  change (arr[A; (@product_assoc C HP Z W Y).1] ∘
    second[A; f; (Z × W)%ob] ≈ second[A; second[A; f; W]; Z] ∘
      arr[A; (@product_assoc C HP Z W X).1]) in H.
  transitivity ((second[A; second[A; f; W]; Z] ∘
    arr[A; (@product_assoc C HP Z W X).1]) ∘
    arr[A; (@product_assoc C HP Z W X).2.1]).
  - rewrite comp_assoc, <- functor_comp,
      (snd (@product_assoc C HP Z W X).2.2), functor_id, comp_id_r.
    reflexivity.
  - rewrite <- H. reflexivity.
Qed.

(** Fuse pure maps before any fixed computation. *)

(** 在任意固定计算前合并纯映射。 *)

Local Lemma arr_comp_post {U : @Ob K} {X Y Z : @Ob C}
    (p : Hom Y Z) (q : Hom X Y) (k : Hom U (A X))
  : arr[A; p] ∘ (arr[A; q] ∘ k) ≈ arr[A; p ∘ q] ∘ k.
Proof. rewrite <- comp_assoc, <- functor_comp. reflexivity. Qed.

(** Reassociate computations and fuse adjacent pure maps, leaving all
    effectful computations abstract. *)

(** 重排计算括号并合并相邻纯映射，保持全部带效应计算抽象。 *)

Local Ltac normalize_arr :=
  repeat first [rewrite comp_assoc | rewrite arr_comp_post |
    rewrite <- functor_comp].

(** Nested right contexts agree with one extension by their product. *)

(** 嵌套右上下文与按其积做一次扩展一致。 *)

Lemma arrow_first_assoc {X Y Z W : @Ob C}
    (f : Hom (A X) (A Y))
  : arr[A; (@product_assoc C HP Y Z W).1] ∘
      first[A; first[A; f; Z]; W] ≈
      first[A; f; (Z × W)%ob] ∘
        arr[A; (@product_assoc C HP X Z W).1].
Proof.
  unfold arrow_first.
  rewrite !arrow_second_comp, !arrow_second_arr, arrow_second_nested.
  normalize_arr.
  assert (Ho : (@product_assoc C HP Y Z W).1 ∘
    ((⟨π2, π1⟩ : Hom (W × (Y × Z)) ((Y × Z) × W)) ∘
      ((@id W × (⟨π2, π1⟩ : Hom (Z × Y) (Y × Z))) ∘
        (@product_assoc C HP W Z Y).1)) ≈
    (⟨π2, π1⟩ : Hom ((Z × W) × Y) (Y × (Z × W))) ∘
      ((⟨π2, π1⟩ : Hom (W × Z) (Z × W)) × @id Y)).
  { unfold product_assoc. cbn.
    repeat first [rewrite cross_η | rewrite product_comp_r |
      rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
      rewrite comp_id_l | rewrite comp_id_r]. reflexivity. }
  assert (Hi : ((⟨π2, π1⟩ : Hom (W × Z) (Z × W)) × @id X) ∘
    ((@product_assoc C HP W Z X).2.1 ∘
      ((@id W × (⟨π2, π1⟩ : Hom (X × Z) (Z × X))) ∘
        (⟨π2, π1⟩ : Hom ((X × Z) × W) (W × (X × Z))))) ≈
    (⟨π2, π1⟩ : Hom (X × (Z × W)) ((Z × W) × X)) ∘
      (@product_assoc C HP X Z W).1).
  { unfold product_assoc. cbn.
    repeat first [rewrite cross_η | rewrite product_comp_r |
      rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
      rewrite comp_id_l | rewrite comp_id_r]. reflexivity. }
  rewrite Ho, functor_comp. repeat rewrite comp_assoc.
  rewrite <- (comp_assoc
    arr[A; ((⟨π2, π1⟩ : Hom (W × Z) (Z × W)) × @id Y)]
    (second[A; f; (W × Z)%ob])
    arr[A; (@product_assoc C HP W Z X).2.1 ∘
      ((@id W × (⟨π2, π1⟩ : Hom (X × Z) (Z × X))) ∘
        (⟨π2, π1⟩ : Hom ((X × Z) × W) (W × (X × Z))))]),
    arrow_second_natural.
  normalize_arr. rewrite Hi. reflexivity.
Qed.

(** Reassociation is natural in the middle computation. The proof uses
    ordinary context exchange, never interchange of two effects. *)

(** 括号重排在中间计算上自然。仅使用通常上下文的交换，不交换两个带效应
    计算。 *)

Lemma arrow_middle_assoc {X Y Y' Z : @Ob C}
    (f : Hom (A Y) (A Y'))
  : arr[A; (@product_assoc C HP X Y' Z).1] ∘
      first[A; second[A; f; X]; Z] ≈
      second[A; first[A; f; Z]; X] ∘
        arr[A; (@product_assoc C HP X Y Z).1].
Proof.
  unfold arrow_first.
  rewrite !arrow_second_comp, !arrow_second_arr, !arrow_second_nested.
  normalize_arr.
  assert (Ho : (@product_assoc C HP X Y' Z).1 ∘
    ((⟨π2, π1⟩ : Hom (Z × (X × Y')) ((X × Y') × Z)) ∘
      (@product_assoc C HP Z X Y').1) ≈
    ((@id X × (⟨π2, π1⟩ : Hom (Z × Y') (Y' × Z))) ∘
      (@product_assoc C HP X Z Y').1) ∘
        ((⟨π2, π1⟩ : Hom (Z × X) (X × Z)) × @id Y')).
  { unfold product_assoc. cbn.
    repeat first [rewrite cross_η | rewrite product_comp_r |
      rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
      rewrite comp_id_l | rewrite comp_id_r]. reflexivity. }
  assert (Hi : ((⟨π2, π1⟩ : Hom (Z × X) (X × Z)) × @id Y) ∘
    ((@product_assoc C HP Z X Y).2.1 ∘
      (⟨π2, π1⟩ : Hom ((X × Y) × Z) (Z × (X × Y)))) ≈
    (@product_assoc C HP X Z Y).2.1 ∘
      ((@id X × (⟨π2, π1⟩ : Hom (Y × Z) (Z × Y))) ∘
        (@product_assoc C HP X Y Z).1)).
  { unfold product_assoc. cbn.
    repeat first [rewrite cross_η | rewrite product_comp_r |
      rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
      rewrite comp_id_l | rewrite comp_id_r]. reflexivity. }
  rewrite Ho, functor_comp. repeat rewrite comp_assoc.
  rewrite <- (comp_assoc
    arr[A; ((⟨π2, π1⟩ : Hom (Z × X) (X × Z)) × @id Y')]
    (second[A; f; (Z × X)%ob])
    arr[A; (@product_assoc C HP Z X Y).2.1 ∘
      (⟨π2, π1⟩ : Hom ((X × Y) × Z) (Z × (X × Y)))]),
    arrow_second_natural.
  normalize_arr. rewrite Hi. reflexivity.
Qed.

End Cartesian.

(** Run the left computation before the right on separate inputs.
    This operation is not assumed jointly functorial. *)

(** 在分开的输入上先运行左计算，再运行右计算；不假定此运算联合具有函子性。 *)

Definition arrow_split {C K : Cat}
    `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP))
    {X Y X' Y' : @Ob C}
    (f : Hom (A X) (A Y)) (g : Hom (A X') (A Y'))
  : Hom (A (X × X')%ob) (A (Y × Y')%ob)
  := second[A; g; Y] ∘ first[A; f; X'].

Notation "f '***[' A ']' g" := (arrow_split A f g)
  (at level 41, right associativity) : computation_scope.

(** Copy an ordinary input, then perform ordered splitting. *)

(** 复制通常输入，再执行有序分开组合。 *)

Definition arrow_fanout {C K : Cat}
    `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP)) {X Y Z : @Ob C}
    (f : Hom (A X) (A Y)) (g : Hom (A X) (A Z))
  : Hom (A X) (A (Y × Z)%ob)
  := (f ***[A] g) ∘ arr[A; ⟨id, id⟩].

Notation "f '&&&[' A ']' g" := (arrow_fanout A f g)
  (at level 41, right associativity) : computation_scope.

(** Ordered splitting preserves both specified computation equalities. *)

(** 有序分开组合保持两个指定计算相等。 *)

Global Instance arrow_split_proper {C K : Cat}
    `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP))
    {X Y X' Y' : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq) (@arrow_split C K HT HP A X Y X' Y').
Proof.
  intros f f' Hf g g' Hg. unfold arrow_split. rewrite Hf, Hg. reflexivity.
Qed.

(** Ordered fanout preserves both specified computation equalities. *)

(** 有序扇出组合保持两个指定计算相等。 *)

Global Instance arrow_fanout_proper {C K : Cat}
    `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP)) {X Y Z : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq) (@arrow_fanout C K HT HP A X Y Z).
Proof.
  intros f f' Hf g g' Hg. unfold arrow_fanout. rewrite Hf, Hg. reflexivity.
Qed.
