From Cats Require Export
  Cat.Core
  Cat.Functor.Core.

(** * Separately Functorial Tensor Contexts

    A binoidal category has one tensor on objects and two actions on
    arrows, each functorial with the other object fixed. Their two
    execution orders need not agree. Units, associators and symmetry
    belong to stronger interfaces. *)

(** * 分别具有函子性的张量上下文

    双侧张量范畴在对象上具有一个张量，在态射上具有两种作用；固定另一对象时，
    每种作用分别具有函子性。两种执行次序不必相等。单位元、结合子及对称性
    属于更强的接口。 *)

Class BinoidalCat (C : Cat)
  :=
  (** Compute the unique category view from the named parameter. *)

  (** 从具名参数计算唯一底层范畴视图。 *)

  { BinoidalC :> Cat := C

  (** Both arrow actions use this same tensor on objects. *)

  (** 两种态射作用使用对象上的同一张量。 *)

  ; binoidal_tensor : @Ob C → @Ob C → @Ob C
  ; binoidal_left {X Y : @Ob C} (Z : @Ob C) (f : Hom X Y)
    : Hom (binoidal_tensor Z X) (binoidal_tensor Z Y)
  ; binoidal_right {X Y : @Ob C} (Z : @Ob C) (f : Hom X Y)
    : Hom (binoidal_tensor X Z) (binoidal_tensor Y Z)

  (** Both actions preserve specified hom equality. *)

  (** 两种作用均保持指定 Hom 相等。 *)

  ; binoidal_left_proper {X Y : @Ob C} (Z : @Ob C)
    :: Proper (HomEq ==> HomEq) (@binoidal_left X Y Z)
  ; binoidal_right_proper {X Y : @Ob C} (Z : @Ob C)
    :: Proper (HomEq ==> HomEq) (@binoidal_right X Y Z)

  (** Each fixed-context action preserves identities and sequencing. *)

  (** 每种固定上下文作用保持恒等及顺序组合。 *)

  ; binoidal_left_id (Z X : @Ob C)
    : binoidal_left Z (@id X) ≈ id
  ; binoidal_right_id (Z X : @Ob C)
    : binoidal_right Z (@id X) ≈ id
  ; binoidal_left_comp {X Y W : @Ob C} (Z : @Ob C)
      (g : Hom Y W) (f : Hom X Y)
    : binoidal_left Z (g ∘ f) ≈ binoidal_left Z g ∘ binoidal_left Z f
  ; binoidal_right_comp {X Y W : @Ob C} (Z : @Ob C)
      (g : Hom Y W) (f : Hom X Y)
    : binoidal_right Z (g ∘ f) ≈ binoidal_right Z g ∘ binoidal_right Z f
  }.

Arguments BinoidalC {_} _.
Arguments binoidal_tensor {_ _} _ _.
Arguments binoidal_left {_ _ _ _} _ _.
Arguments binoidal_right {_ _ _ _} _ _.

Declare Scope binoidal_scope.
Delimit Scope binoidal_scope with binoidal.
Infix "⊗" := binoidal_tensor
  (at level 41, right associativity) : binoidal_scope.
Infix "⊲" := binoidal_left
  (at level 40, left associativity) : binoidal_scope.
Notation "f '⊳' Z" := (binoidal_right Z f)
  (at level 40, left associativity) : binoidal_scope.
Local Open Scope binoidal_scope.

(** ** Fixed-Context Functors

    Fix a binoidal structure on the named category. Bundle left and right
    context actions as functors and derive their identity and composition laws. *)

(** ** 固定上下文函子

    固定具名范畴上的双侧张量结构，将左右上下文作用打包为函子，并导出恒等与复合定律。 *)

Section ContextFunctors.
Context {C : Cat} `{BC : !BinoidalCat C}.

(** Tensor with a fixed object on the left. Its object map is derived
    from the same selected tensor, not stored as another choice. *)

(** 在左侧张量一个固定对象。对象映射从同一选定张量导出，不另作选择。 *)

Program Definition BinoidalLeftF (Z : @Ob C)
  : Functor C C
  :=
  {|F0 X := Z ⊗ X
  ; F1 X Y f := Z ⊲ f
  ; functor_fmap_proper X Y := binoidal_left_proper Z
  ; functor_id X := binoidal_left_id Z X
  ; functor_comp X Y W g f := binoidal_left_comp Z g f
  |}.

(** Tensor with a fixed object on the right. *)

(** 在右侧张量一个固定对象。 *)

Program Definition BinoidalRightF (Z : @Ob C)
  : Functor C C
  :=
  {|F0 X := X ⊗ Z
  ; F1 X Y f := f ⊳ Z
  ; functor_fmap_proper X Y := binoidal_right_proper Z
  ; functor_id X := binoidal_right_id Z X
  ; functor_comp X Y W g f := binoidal_right_comp Z g f
  |}.

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
