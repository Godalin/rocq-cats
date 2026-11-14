From Cats Require Export
  Cat.Comma.Core
  Cat.Terminal.
From Cats Require Import
  Cat.Preorder
  Cat.Diagram.Core.

(** * Structured Arrows and Universal Arrows

    Fixing the left endpoint gives the comma category of arrows from [X]
    into images of [U]. Its initiality is equivalent to unique factorization.
    All mediators remain computational data. *)

(** * 结构箭头与泛箭头

    固定左端点得到从 [X] 指向 [U] 的像的逗号范畴；其始性等价于唯一分解
    泛性质，所有中介均保留为可计算数据。 *)

Definition StructuredArrow {C D : Cat} (U : Fct D C) (X : @Ob C)
  : Cat
  := ConstF (CodiscreteCat unit) X ↓C U.

Notation "X '↓[' U ']'" := (StructuredArrow U X)
  (at level 40, no associativity) : cat_scope.

(** Package a candidate arrow with the unique left object. *)

(** 将候选箭头与唯一左对象打包。 *)

Program Definition StructuredOb {C D : Cat} (U : Fct D C)
    {X : @Ob C} {A : @Ob D} (η : Hom X (U A))
  : @Ob (X ↓[U])
  :=
  {|comma_left_ob := tt
  ; comma_right_ob := A
  ; comma_arrow := η
  |}.

(** A commuting triangle determines a structured-arrow morphism. The left
    side is the canonical singleton arrow; the right side remains unchanged. *)

(** 交换三角形确定结构箭头态射；左侧取典范单元素箭头，右侧保持原映射。 *)

Program Definition StructuredMap {C D : Cat} (U : Fct D C)
    {X : @Ob C} (Z W : @Ob (X ↓[U]))
    (g : Hom (comma_right_ob Z) (comma_right_ob W))
    (H : fmap U g ∘ comma_arrow Z ≈ comma_arrow W)
  : (@Hom (X ↓[U])) Z W
  :=
  {|comma_left := tt
  ; comma_right := g
  |}.
Next Obligation.
  change (fmap U g ∘ comma_arrow Z ≈ comma_arrow W ∘ id).
  rewrite comp_id_r. exact H.
Defined.

(** Every arrow into a [U]-image factors uniquely through the candidate,
    using specified hom equality. *)

(** 每条指向 [U] 的像的箭头均通过候选唯一分解，使用指定 Hom 相等。 *)

Definition is_universal_arrow {C D : Cat} (U : Fct D C)
    {X : @Ob C} {A : @Ob D} (η : Hom X (U A))
  : Type
  := ∀ B (f : Hom X (U B)), ∃ g : Hom A B,
      is_unique (λ g, fmap U g ∘ η ≈ f) g.

Notation "η '⦂' 'UnivArr(' U ')'" := (is_universal_arrow U η)
  (at level 50, no associativity) : cat_scope.

(** Initiality of any structured-arrow object supplies the direct property;
    the representative of the singleton left object is immaterial. *)

(** 任意结构箭头对象的始性给出直接泛性质，单元素左对象的代表不影响结果。 *)

Definition structured_initial_universal {C D : Cat} (U : Fct D C)
    {X : @Ob C} (Z : @Ob (X ↓[U]))
    (HZ : @is_initial (X ↓[U]) Z)
  : comma_arrow Z ⦂ UnivArr(U).
Proof.
  intros B f. destruct (HZ (StructuredOb U f)) as [h Hh].
  exists (comma_right h). refine {|this := _
                                ; that := _
                                |}.
  - pose proof (comma_comm h) as E.
    change (fmap U (comma_right h) ∘ comma_arrow Z ≈ f ∘ id) in E.
    rewrite comp_id_r in E. exact E.
  - intros g Hg.
    pose (K := StructuredMap U Z (StructuredOb U f) g Hg).
    exact (snd (@that _ _ _ _ _ Hh K I)).
Defined.

(** A direct universal arrow is initial in its comma category. *)

(** 直接泛箭头是其逗号范畴的始对象。 *)

Definition universal_arrow_is_initial {C D : Cat} (U : Fct D C)
    {X : @Ob C} {A : @Ob D} {η : Hom X (U A)}
    (Hη : η ⦂ UnivArr(U))
  : @is_initial (X ↓[U]) (StructuredOb U η).
Proof.
  intros Z. destruct (Hη (comma_right_ob Z) (comma_arrow Z)) as [g Hg].
  pose (h := StructuredMap U (StructuredOb U η) Z g (@this _ _ _ _ _ Hg)).
  exists h. refine {|this := I
                   ; that := _
                   |}.
  intros k _. split; [exact tt |].
  apply (@that _ _ _ _ _ Hg).
  pose proof (comma_comm k) as E.
  change (fmap U (comma_right k) ∘ η ≈ comma_arrow Z ∘ id) in E.
  rewrite comp_id_r in E. exact E.
Defined.

(** Initiality and direct universality are constructively equivalent for
    the same candidate arrow. *)

(** 同一候选箭头的始性与直接泛性质构造性等价。 *)

Theorem universal_arrow_initial {C D : Cat} (U : Fct D C)
    {X : @Ob C} {A : @Ob D} (η : Hom X (U A))
  : (η ⦂ UnivArr(U)) ↔ @is_initial (X ↓[U]) (StructuredOb U η).
Proof.
  split.
  - apply universal_arrow_is_initial.
  - apply structured_initial_universal.
Defined.

(** Two universal arrows from the same object determine an isomorphism
    preserving those arrows, obtained from initial-object uniqueness. *)

(** 从同一对象出发的两个泛箭头确定保持它们的同构，由始对象唯一性得到。 *)

Definition universal_arrow_iso {C D : Cat} (U : Fct D C)
    {X : @Ob C} {A B : @Ob D} {η : Hom X (U A)} {θ : Hom X (U B)}
    (Hη : η ⦂ UnivArr(U)) (Hθ : θ ⦂ UnivArr(U))
  : ∃ i : A ≅[D] B, fmap U i.1 ∘ η ≈ θ.
Proof.
  pose (i := initial_unique (universal_arrow_is_initial U Hη)
    (universal_arrow_is_initial U Hθ)).
  exists (comma_right i.1; functor_is_iso (CommaRightF _ U) i.1 i.2).
  pose proof (comma_comm i.1) as E.
  change (fmap U (comma_right i.1) ∘ η ≈ θ ∘ id) in E.
  rewrite comp_id_r in E. exact E.
Defined.

(** Compatibility with the universal arrow determines any mediator uniquely,
    hence also the preceding comparison isomorphism. *)

(** 与泛箭头相容便唯一确定中介，因而也唯一确定前面的比较同构。 *)

Lemma universal_arrow_hom_unique {C D : Cat} (U : Fct D C)
    {X : @Ob C} {A B : @Ob D} {η : Hom X (U A)}
    (Hη : η ⦂ UnivArr(U)) (f g : Hom A B)
    (E : fmap U f ∘ η ≈ fmap U g ∘ η)
  : f ≈ g.
Proof.
  destruct (Hη B (fmap U g ∘ η)) as [h Hh].
  transitivity h.
  - apply (@that _ _ _ _ _ Hh). exact E.
  - symmetry. apply (@that _ _ _ _ _ Hh). reflexivity.
Qed.

(** The comparison is unique among arrows preserving the two units. *)

(** 比较在保持两个单位的箭头中唯一。 *)

Lemma universal_arrow_iso_unique {C D : Cat} (U : Fct D C)
    {X : @Ob C} {A B : @Ob D} {η : Hom X (U A)} {θ : Hom X (U B)}
    (Hη : η ⦂ UnivArr(U)) (Hθ : θ ⦂ UnivArr(U))
    (f : Hom A B) (Hf : fmap U f ∘ η ≈ θ)
  : f ≈ (universal_arrow_iso U Hη Hθ).1.1.
Proof.
  apply (universal_arrow_hom_unique U Hη).
  rewrite Hf, (universal_arrow_iso U Hη Hθ).2. reflexivity.
Qed.
