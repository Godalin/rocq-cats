From Cats.Set.Relation Require Export Closure.
From Cats.Set Require Import Generated.

(** * Equivalence Closure by Composition

    Finite paths of oriented edges form the equivalence relation generated
    by the edges. Symmetry moves past path closure in the direction needed
    by [CompositeClosure]. The closure laws and least simultaneous extension
    then follow from that general theorem, rather than a second independent
    equivalence-generation construction.

    The original [EquivClosure] interface is preserved. Its derivation trees
    and the path presentation have the same relation, by transparent maps;
    no equality or inverse laws between their witness types are imposed. *)

(** * 由复合得到等价闭包

    带正反方向的有限路径形成由边生成的等价关系。对称操作可按
    [CompositeClosure] 所需的方向移过路径闭包。因此闭包律及同时闭合的最小
    扩张来自一般定理，无须再独立构造一套等价生成理论。

    原有 [EquivClosure] 接口保持不变。其推导树与路径呈现通过透明映射表示
    相同关系，不为两种见证类型施加相等或互逆律。 *)

Local Open Scope relation_scope.
Local Open Scope set_scope.

(** A forward path maps its edges into forward alternatives. A backward
    path first maps the edges, then reverses the whole path. This is a
    one-sided comparison, not commutation of the two closure operators. *)

(** 正向路径将边映入正向分支；反向路径先映射边，再反转整条路径。这是单向
    比较，不是两个闭包算子可交换。 *)

Definition sym_rtc_interchange {A : Type} (R : crelation A)
  : (R^*)^± ⊆R (R^±)^*.
Proof.
  intros x y [p | p].
  - exact (rtc_map (S := R^±) (λ x y h, inl h) x y p).
  - exact (@ReflTransClosure_Symmetric A (R^±)
      (SymClosure_Symmetric R) y x
      (rtc_map (S := R^±) (λ x y h, inl h) y x p)).
Defined.

(** Symmetric closure followed by path closure is the chosen equivalence
    closure. Its common witness bound contains the carrier, as required for
    intermediate path elements. The inclusion preorder is supplied explicitly
    so composition and flattening do not depend on an opaque instance. *)

(** 先对称闭包再路径闭包，得到选定等价闭包。其共同见证界容纳路径中间元素
    所需的载体。显式提供包含预序，使复合与压平不依赖不透明实例。 *)

Definition EquivalenceClosure@{a r +} (A : Type@{a})
  : Closure (@subrelation@{a r r} A)
  := @CompositeClosure (A → A → Type@{r})
      (@subrelation@{a r r} A) (RelationInclusionPreorder A)
      (SymmetricClosure A) (ReflexiveTransitiveClosure A)
      (@sym_rtc_interchange A).

Notation "R '^±*'" := (EquivalenceClosure _ R)
  (at level 1) : relation_scope.

(** The generated paths are a preorder and are symmetric because their
    edges are symmetric. This property does not identify different paths. *)

(** 生成路径构成预序，且因边对称而对称；这个性质不识别不同路径。 *)

Global Program Instance EquivalenceClosure_Equivalence@{a r +}
    {A : Type@{a}} (R : A → A → Type@{r})
  : Equivalence (EquivalenceClosure@{a r _} A R)
  :=
  {|Equivalence_Reflexive := rtc_refl
  ; Equivalence_Symmetric := ReflTransClosure_Symmetric (R^±)
  ; Equivalence_Transitive x y z := rtc_trans
  |}.

(** Closed relations for the composite are exactly equivalence relations.
    Reuse the generic simultaneous-closedness theorem, then interpret the
    two component predicates as symmetry and preorder structure. *)

(** 复合的闭关系恰好是等价关系。复用一般的同时闭性定理，再将两个分量谓词
    分别解释为对称性与预序结构。 *)

Definition equivalence_closure_closed@{a r +}
    {A : Type@{a}} (R : A → A → Type@{r})
  : is_closed (EquivalenceClosure@{a r _} A) R ↔ Equivalence R.
Proof.
  pose (hc := @composite_closure_closed _ _ (RelationInclusionPreorder A)
    (SymmetricClosure A) (ReflexiveTransitiveClosure A)
    (@sym_rtc_interchange A) R).
  split.
  - intros h.
    pose (s := fst (sym_closure_closed R) (fst (fst hc h))).
    pose (p := fst (rtc_closed R) (snd (fst hc h))).
    refine {|Equivalence_Reflexive := @PreOrder_Reflexive _ R p
           ; Equivalence_Symmetric := s
           ; Equivalence_Transitive := @PreOrder_Transitive _ R p
           |}.
  - intros hs. apply (snd hc). split.
    + exact (snd (sym_closure_closed R) (@Equivalence_Symmetric _ R hs)).
    + apply (snd (rtc_closed R)).
      refine {|PreOrder_Reflexive := @Equivalence_Reflexive _ R hs
             ; PreOrder_Transitive := @Equivalence_Transitive _ R hs
             |}.
Defined.

(** An equivalence target is closed under the composite, so leastness is
    exactly the generic closure universal property. Its two maps do not
    identify derivations or claim inverse equations on their witnesses. *)

(** 等价目标对复合闭合，因此最小性恰好来自一般闭包泛性质。两个映射不识别
    推导，也不为其见证断言互逆方程。 *)

Definition equivalence_closure_universal {A : Type} (R S : crelation A)
    `{HS : !Equivalence S}
  : R^±* ⊆R S ↔ R ⊆R S
  := @closure_universal _ _ (RelationInclusionPreorder A)
      (EquivalenceClosure A) R S (snd (equivalence_closure_closed S) HS).

(** Map generated paths along a function into an equivalence target.
    The source and target carriers and witness levels can differ. *)

(** 沿函数将生成路径映入等价目标，源、目标的载体与见证层级可以不同。 *)

Definition equivalence_closure_preserves@{a b r s +}
    {A : Type@{a}} {B : Type@{b}}
    {R : A → A → Type@{r}} {S : B → B → Type@{s}}
    `{HS : !Equivalence S}
    (f : A → B) (h : ∀ x y, R x y → S (f x) (f y))
    {x y : A} (p : EquivalenceClosure@{a r _} A R x y)
  : S (f x) (f y).
Proof.
  refine (@rtc_preserves@{a b r r s} A B (R^±) S
    {|PreOrder_Reflexive := @Equivalence_Reflexive _ S HS
    ; PreOrder_Transitive := @Equivalence_Transitive _ S HS
    |} f _ x y p).
  intros u v q.
  exact (@sym_closure_preserves A B R S
    (@Equivalence_Symmetric _ S HS) f h u v q).
Defined.

(** Equivalence closure is monotone by its generic closure structure. *)

(** 等价闭包的单调性来自其一般闭包结构。 *)

Definition equivalence_closure_map {A : Type} {R S : crelation A}
    (h : R ⊆R S)
  : R^±* ⊆R S^±*
  := closure_monotone (EquivalenceClosure A) h.

(** It consequently respects pointwise equivalence of generators. *)

(** 因而它保持生成关系的逐点等价。 *)

Global Instance EquivalenceClosure_proper {A : Type}
  : Proper (relation_equivalence ==> relation_equivalence)
      (EquivalenceClosure A).
Proof.
  intros R S h. apply relation_equiv_of_inclusions.
  - exact (equivalence_closure_map (relation_equiv_forward h)).
  - exact (equivalence_closure_map (relation_equiv_backward h)).
Defined.

(** The path and the existing tree presentations generate the same relation.
    Each direction follows by the other presentation's leastness; no rewrite
    of the existing definition or its exported clients is necessary. *)

(** 路径呈现与既有树呈现生成相同关系。两个方向分别由另一呈现的最小性导出，
    无须改写原定义或其导出客户端。 *)

Definition equivalence_closure_legacy {A : Type} (R : crelation A)
  : R^±* ≈R R^≈.
Proof.
  apply relation_equiv_of_inclusions.
  - apply (snd (equivalence_closure_universal R (R^≈))).
    intros x y p. exact (closure_step p).
  - intros x y p. exact (equiv_closure_preserves (λ x, x)
      (λ x y q, closure_inflate (EquivalenceClosure A) R x y q) p).
Defined.
