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

(** Reserve tensor and action syntax for the field-local interpretations. *)

(** 为字段内的局部解释预留张量与作用语法。 *)

Declare Scope monoidal_scope.
Delimit Scope monoidal_scope with monoidal.
Reserved Infix "⊗"
  (at level 41, right associativity).
Reserved Infix "⊲"
  (at level 40, left associativity).
Reserved Notation "f '⊳' Z"
  (at level 40, left associativity).
Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** Choose one object tensor and its two separately functorial actions on
    the named category. Both law groups refer to these exact maps. *)

(** 在具名范畴上选择唯一对象张量及其分别具有函子性的两种作用；两组定律均
    引用恰好这些映射。 *)

Minks.Mixin HasBinoidal (C : Cat)
  :=
  { tensor : C → C → C
    where "X '⊗' Y" := (tensor X Y)
      : ob_scope

  (** Each action uses the same chosen tensor on objects. *)

  (** 每种作用使用同一选定对象张量。 *)

  ; tensor_l {X Y : C} (Z : C) (f : Hom X Y)
    : Hom (Z ⊗ X) (Z ⊗ Y)
    where "Z '⊲' f" := (tensor_l Z f)
      : monoidal_scope

  ; tensor_r {X Y : C} (Z : C) (f : Hom X Y)
    : Hom (X ⊗ Z) (Y ⊗ Z)
    where "f '⊳' Z" := (tensor_r Z f)
      : monoidal_scope

  (** Fixed left and right contexts use the reusable functor-law interface. *)

  (** 固定的左右上下文使用可复用的函子律接口。 *)

  ; isBinoidalL (Z : C)
    :: IsFct (tensor Z) (λ X Y, @tensor_l X Y Z)

  ; isBinoidalR (Z : C)
    :: IsFct (λ X, X ⊗ Z) (λ X Y, @tensor_r X Y Z)
  }.

Arguments tensor {_ _} _ _.
Arguments tensor_l {_ _ _ _} _ _.
Arguments tensor_r {_ _ _ _} _ _.

Infix "⊗" := tensor
  (at level 41, right associativity)
  : ob_scope.
Infix "⊲" := tensor_l
  (at level 40, left associativity)
  : monoidal_scope.
Notation "f '⊳' Z" := (tensor_r Z f)
  (at level 40, left associativity)
  : monoidal_scope.

(** A complete binoidal category stores its category once and selects one
    extension. Its inherited instance reads that same stored choice. *)

(** 完整双侧张量范畴只保存一次底层范畴，并选择一份扩展；继承实例读取同一
    保存的选择。 *)

Minks.Struct BinoidalCat
  extends Cat
  with  hasBinoidal as hasBinoidal : HasBinoidal.

(** ** Laws of the Chosen Actions

    Fix the named category and its chosen tensor actions. Expose the
    subject-specific laws from the two supplied functor-law groups. *)

(** ** 选定作用的定律

    固定具名范畴及其选定张量作用，从两份给定函子律组提供按数学主题命名的定律。 *)

Section ActionLaws.
Context {C : Cat} `{BC : !HasBinoidal C}.

(** Each context action respects hom equality. *)

(** 每种上下文作用均保持 Hom 相等。 *)

Global Instance tensor_l_proper {X Y : C} (Z : C)
  : Proper (HomEq ==> HomEq) (@tensor_l C BC X Y Z).
Proof.
  exact (fmap_proper (IsFct := isBinoidalL Z)).
Qed.

(** The right-context action has the same respectfulness interface. *)

(** 右上下文作用具有同样的保相等接口。 *)

Global Instance tensor_r_proper {X Y : C} (Z : C)
  : Proper (HomEq ==> HomEq) (@tensor_r C BC X Y Z).
Proof.
  exact (fmap_proper (IsFct := isBinoidalR Z)).
Qed.

(** Left context preserves identities. *)

(** 左上下文保持恒等。 *)

Lemma tensor_l_id (Z X : C)
  : Z ⊲ id[X] ≈ id.
Proof.
  exact (fmap_id (IsFct := isBinoidalL Z) (X := X)).
Qed.

(** Right context preserves identities. *)

(** 右上下文保持恒等。 *)

Lemma tensor_r_id (Z X : C)
  : id[X] ⊳ Z ≈ id.
Proof.
  exact (fmap_id (IsFct := isBinoidalR Z) (X := X)).
Qed.

(** Left context preserves composition. *)

(** 左上下文保持复合。 *)

Lemma tensor_l_comp {X Y W : C} (Z : C)
    (g : Hom Y W) (f : Hom X Y)
  : Z ⊲ (g ∘ f) ≈ (Z ⊲ g) ∘ (Z ⊲ f).
Proof.
  exact (fmap_comp (IsFct := isBinoidalL Z) g f).
Qed.

(** Right context preserves composition. *)

(** 右上下文保持复合。 *)

Lemma tensor_r_comp {X Y W : C} (Z : C)
    (g : Hom Y W) (f : Hom X Y)
  : (g ∘ f) ⊳ Z ≈ (g ⊳ Z) ∘ (f ⊳ Z).
Proof.
  exact (fmap_comp (IsFct := isBinoidalR Z) g f).
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

Definition TensorAtLF (Z : C)
  : Fct C C
  := MakeFct (tensor Z)
    (λ X Y, @tensor_l C BC X Y Z) (isBinoidalL Z).

(** Tensor with a fixed object on the right. *)

(** 在右侧张量一个固定对象。 *)

Definition TensorAtRF (Z : @Ob C)
  : Fct C C
  := MakeFct (λ X, X ⊗ Z)
    (λ X Y, @tensor_r C BC X Y Z) (isBinoidalR Z).

(** Run the left factor before the right factor on separate inputs. *)

(** 在分开的输入上先运行左因子，再运行右因子。 *)

Definition tensor_sequence {X Y Z W : @Ob C}
    (f : Hom X Y) (g : Hom Z W)
  : Hom (X ⊗ Z) (Y ⊗ W)
  := (Y ⊲ g) ∘ (f ⊳ Z).

(** Ordered sequencing respects both computation equalities. *)

(** 有序组合保持两个计算相等。 *)

Global Instance tensor_sequence_proper {X Y Z W : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq) (@tensor_sequence X Y Z W).
Proof.
  intros f f' Hf g g' Hg. unfold tensor_sequence.
  rewrite Hf, Hg. reflexivity.
Qed.

End ContextFunctors.

Notation "'(' Z '⊗-)'" := (TensorAtLF Z)
  (at level 0, format "( Z  ⊗-)")
  : monoidal_scope.
Notation "'(-⊗' Z ')'" := (TensorAtRF Z)
  (at level 0, format "(-⊗  Z )")
  : monoidal_scope.

(** ** Sequencing with Identities

    For fixed separate actions, tensoring with an identity recovers an
    action. Tensoring two identities gives an identity. *)

(** ** 与恒等态射的组合

    固定分别作用后，与恒等态射张量得到相应的作用。两个恒等态射的张量
    仍为恒等态射。 *)

Section SequenceIdentities.
Context {C : Cat} `{BC : !HasBinoidal C}.

(** Tensoring identities uses only the two separate functor laws. *)

(** 张量两个恒等态射只需两条分别函子律。 *)

Lemma tensor_sequence_id (X Y : C)
  : tensor_sequence id[X] id[Y] ≈ id[X ⊗ Y].
Proof.
  unfold tensor_sequence.
  rewrite tensor_l_id, tensor_r_id. apply comp_id_l.
Qed.

(** Tensoring with a left identity recovers the left context action. *)

(** 在左侧张量恒等态射恢复左上下文作用。 *)

Lemma tensor_sequence_left {X Y : C} (Z : C)
    (f : Hom X Y)
  : tensor_sequence id[Z] f ≈ Z ⊲ f.
Proof.
  unfold tensor_sequence. rewrite tensor_r_id.
  apply comp_id_r.
Qed.

(** Tensoring with a right identity recovers the right context action. *)

(** 在右侧张量恒等态射恢复右上下文作用。 *)

Lemma tensor_sequence_right {X Y : C} (Z : C)
    (f : Hom X Y)
  : tensor_sequence f id[Z] ≈ f ⊳ Z.
Proof.
  unfold tensor_sequence. rewrite tensor_l_id.
  apply comp_id_l.
Qed.

End SequenceIdentities.
