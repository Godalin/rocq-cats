From Cats Require Export
  Cat.Core
  Cat.Functor.Laws.

(** * Separately Functorial Tensor Contexts

    A binoidal category has one tensor on objects and two actions on
    arrows, each functorial with the other object fixed. Their two
    execution orders need not agree. Units, associators and symmetry
    belong to stronger interfaces. *)

(** * 分别具有函子性的张量上下文

    双侧张量范畴在对象上具有一个张量，在态射上具有两种作用；固定另一对象时，
    每种作用分别具有函子性。两种执行次序不必相等。单位元、结合子及对称性
    属于更强的接口。 *)

(** Reserve tensor and action syntax for the field-local interpretations. *)

(** 为字段内的局部解释预留张量与作用语法。 *)

Declare Scope binoidal_scope.
Delimit Scope binoidal_scope with binoidal.
Reserved Infix "⊗" (at level 41, right associativity).
Reserved Infix "⊲" (at level 40, left associativity).
Reserved Notation "f '⊳' Z"
  (at level 40, left associativity).
Local Open Scope binoidal_scope.

(** Choose one object tensor and its two separately functorial actions on
    the named category. Both law groups refer to these exact maps. *)

(** 在具名范畴上选择唯一对象张量及其分别具有函子性的两种作用；两组定律均
    引用恰好这些映射。 *)

Class HasBinoidal (C : Cat)
  :=
  { binoidal_tensor : C → C → C
    where "X '⊗' Y" := (binoidal_tensor X Y)
      : binoidal_scope

  (** Each action uses the same chosen tensor on objects. *)

  (** 每种作用使用同一选定对象张量。 *)

  ; binoidal_l {X Y : C} (Z : C) (f : Hom X Y)
    : Hom (Z ⊗ X) (Z ⊗ Y)
    where "Z '⊲' f" := (binoidal_l Z f)
      : binoidal_scope
  ; binoidal_r {X Y : C} (Z : C) (f : Hom X Y)
    : Hom (X ⊗ Z) (Y ⊗ Z)
    where "f '⊳' Z" := (binoidal_r Z f)
      : binoidal_scope

  (** Fixed left and right contexts use the reusable functor-law interface. *)

  (** 固定的左右上下文使用可复用的函子律接口。 *)

  ; isBinoidalL (Z : C)
    :: IsFct (binoidal_tensor Z) (λ X Y, @binoidal_l X Y Z)
  ; isBinoidalR (Z : C)
    :: IsFct (λ X, X ⊗ Z) (λ X Y, @binoidal_r X Y Z)
  }.

Arguments binoidal_tensor {_ _} _ _.
Arguments binoidal_l {_ _ _ _} _ _.
Arguments binoidal_r {_ _ _ _} _ _.

Infix "⊗" := binoidal_tensor : binoidal_scope.
Infix "⊲" := binoidal_l : binoidal_scope.
Notation "f '⊳' Z" := (binoidal_r Z f) : binoidal_scope.

(** A complete binoidal category stores its category once and selects one
    extension. Its inherited instance reads that same stored choice. *)

(** 完整双侧张量范畴只保存一次底层范畴，并选择一份扩展；继承实例读取同一
    保存的选择。 *)

Record BinoidalCat
  := BinoidalCatOfCat
  { BinoidalCatToCat :> Cat
  ; hasBinoidal :: HasBinoidal BinoidalCatToCat
  }.

Arguments BinoidalCatOfCat _ _ : clear implicits.

(** ** Laws of the Chosen Actions

    Fix the named category and its chosen tensor actions. Expose the
    subject-specific laws from the two supplied functor-law groups. *)

(** ** 选定作用的定律

    固定具名范畴及其选定张量作用，从两份给定函子律组提供按数学主题命名的定律。 *)

Section ActionLaws.
Context {C : Cat} `{BC : !HasBinoidal C}.

(** Each context action respects hom equality. *)

(** 每种上下文作用均保持 Hom 相等。 *)

Global Instance binoidal_l_proper {X Y : C} (Z : C)
  : Proper (HomEq ==> HomEq) (@binoidal_l C BC X Y Z).
Proof.
  exact (fct_map_proper (IsFct := isBinoidalL Z)).
Qed.

(** The right-context action has the same respectfulness interface. *)

(** 右上下文作用具有同样的保相等接口。 *)

Global Instance binoidal_r_proper {X Y : C} (Z : C)
  : Proper (HomEq ==> HomEq) (@binoidal_r C BC X Y Z).
Proof.
  exact (fct_map_proper (IsFct := isBinoidalR Z)).
Qed.

(** Left context preserves identities. *)

(** 左上下文保持恒等。 *)

Lemma binoidal_l_id (Z X : C)
  : Z ⊲ @id X ≈ id.
Proof.
  exact (fct_map_id (IsFct := isBinoidalL Z) X).
Qed.

(** Right context preserves identities. *)

(** 右上下文保持恒等。 *)

Lemma binoidal_r_id (Z X : C)
  : @id X ⊳ Z ≈ id.
Proof.
  exact (fct_map_id (IsFct := isBinoidalR Z) X).
Qed.

(** Left context preserves composition. *)

(** 左上下文保持复合。 *)

Lemma binoidal_l_comp {X Y W : C} (Z : C)
    (g : Hom Y W) (f : Hom X Y)
  : Z ⊲ (g ∘ f) ≈ (Z ⊲ g) ∘ (Z ⊲ f).
Proof.
  exact (fct_map_comp (IsFct := isBinoidalL Z) g f).
Qed.

(** Right context preserves composition. *)

(** 右上下文保持复合。 *)

Lemma binoidal_r_comp {X Y W : C} (Z : C)
    (g : Hom Y W) (f : Hom X Y)
  : (g ∘ f) ⊳ Z ≈ (g ⊳ Z) ∘ (f ⊳ Z).
Proof.
  exact (fct_map_comp (IsFct := isBinoidalR Z) g f).
Qed.

End ActionLaws.

(** ** Fixed-Context Functors

    Fix a binoidal structure on the named category. Bundle left and right
    context actions as functors and derive their identity and composition laws. *)

(** ** 固定上下文函子

    固定具名范畴上的双侧张量结构，将左右上下文作用打包为函子，并导出恒等与复合定律。 *)

Section ContextFunctors.
Context {C : Cat} `{BC : !HasBinoidal C}.

(** Tensor with a fixed object on the left. Its object map is derived
    from the same selected tensor, not stored as another choice. *)

(** 在左侧张量一个固定对象。对象映射从同一选定张量导出，不另作选择。 *)

Definition BinoidalLF (Z : @Ob C)
  : Fct C C
  := FctOfMaps (binoidal_tensor Z)
    (λ X Y, @binoidal_l C BC X Y Z) (isBinoidalL Z).

(** Tensor with a fixed object on the right. *)

(** 在右侧张量一个固定对象。 *)

Definition BinoidalRF (Z : @Ob C)
  : Fct C C
  := FctOfMaps (λ X, X ⊗ Z)
    (λ X Y, @binoidal_r C BC X Y Z) (isBinoidalR Z).

(** Run the left factor before the right factor on separate inputs. *)

(** 在分开的输入上先运行左因子，再运行右因子。 *)

Definition binoidal_sequence {X Y Z W : @Ob C}
    (f : Hom X Y) (g : Hom Z W)
  : Hom (X ⊗ Z) (Y ⊗ W)
  := (Y ⊲ g) ∘ (f ⊳ Z).

(** Ordered sequencing respects both computation equalities. *)

(** 有序组合保持两个计算相等。 *)

Global Instance binoidal_sequence_proper {X Y Z W : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq) (@binoidal_sequence X Y Z W).
Proof.
  intros f f' Hf g g' Hg. unfold binoidal_sequence.
  rewrite Hf, Hg. reflexivity.
Qed.

End ContextFunctors.
