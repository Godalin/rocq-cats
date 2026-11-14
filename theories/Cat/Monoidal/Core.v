From Cats Require Export
  Cat.Binoidal.Bifunctor
  Cat.Premonoidal.Laws.

Local Open Scope binoidal_scope.

(** * Monoidal Categories

    A monoidal category is a premonoidal category with interchange.
    Its tensor bifunctor and joint naturality are derived from the shared
    context actions. Units, structure maps, inverses and coherence are
    inherited once; all equations use specified hom equality. *)

(** * 幺半范畴

    幺半范畴是具有交换律的预幺半范畴。张量双函子及联合自然性从共享上下文
    作用导出。单位对象、结构映射、逆与相干性只继承一次；全部方程使用指定
    Hom 相等。 *)

Class MonoidalCat (C : Cat)
  :=
  (** The only parent stores the tensor actions and structural choices. *)

  (** 唯一父结构保存张量作用及结构选择。 *)

  { MonoidalP :> PremonoidalCat C

  (** The two orders agree for arbitrary arrows. The other centrality
      square follows by exchanging the roles of the two arrows. *)

  (** 任意态射的两种次序相等。交换两条态射的角色即可导出另一中心性方块。 *)

  ; monoidal_interchange {X X' Y Y' : @Ob C}
      (f : Hom X X') (g : Hom Y Y')
    : (f ⊳ Y') ∘ (X ⊲ g) ≈ (X' ⊲ g) ∘ (f ⊳ Y)
  }.

Arguments MonoidalP {_} _.

(** Register the same immediate parent for inherited instance search. *)

(** 为继承实例搜索注册同一个直接父结构。 *)

#[export] Existing Instance MonoidalP.

(** ** Tensor Operations and Interchange

    Fix a monoidal structure on the named category. Derive the tensor map
    from separate actions and prove its joint functoriality using interchange. *)

(** ** 张量运算与交换律

    固定具名范畴上的幺半结构，从分别作用导出张量映射，并利用交换律证明联合函子性。 *)

Section TensorOperations.
Context {C : Cat} `{MC : !MonoidalCat C}.

(** The object tensor is exactly the inherited tensor. *)

(** 对象张量恰好是继承的张量。 *)

Definition tensor (X Y : @Ob C)
  : @Ob C
  := X ⊗ Y.

(** Tensor arrows by the inherited left-then-right ordered actions. *)

(** 通过继承的先左后右有序作用张量态射。 *)

Definition tensor_map {X X' Y Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y')
  : Hom (tensor X Y) (tensor X' Y')
  := binoidal_sequence f g.

(** Every arrow is central; only one interchange equation was stored. *)

(** 每条态射都是中心态射；结构只保存了一种交换方程。 *)

Definition monoidal_arrow_central {X Y : @Ob C} (f : Hom X Y)
  : is_central f.
Proof.
  intros Z W g. split.
  - apply monoidal_interchange.
  - symmetry. apply monoidal_interchange.
Defined.

(** The associator is the parent's chosen forward map. *)

(** 结合子是父结构的选定正向映射。 *)

Definition tensor_assoc (X Y Z : @Ob C)
  : Hom (tensor (tensor X Y) Z) (tensor X (tensor Y Z))
  := (premonoidal_associator X Y Z).1.

(** The left unit map retains the parent's selected component. *)

(** 左单位映射保留父结构的选定分量。 *)

Definition tensor_unit_l (X : @Ob C)
  : Hom (binoidal_tensor (PremonoidalUnit MC) X) X
  := (premonoidal_left_unitor X).1.

(** The right unitor uses the same inherited unit. *)

(** 右单位子使用同一继承单位对象。 *)

Definition tensor_unit_r (X : @Ob C)
  : Hom (binoidal_tensor X (PremonoidalUnit MC)) X
  := (premonoidal_right_unitor X).1.

End TensorOperations.

(** Expose the inherited unit with an explicit structure argument. *)

(** 通过显式结构参数提供继承的单位对象。 *)

Definition TensorUnit {C : Cat} (MC : MonoidalCat C)
  : @Ob C
  := PremonoidalUnit MC.

Declare Scope monoidal_scope.
Delimit Scope monoidal_scope with monoidal.
Infix "⊗" := tensor (at level 41, right associativity) : monoidal_scope.
Infix "⊗m" := tensor_map (at level 41, right associativity) : monoidal_scope.
Notation "'I⊗[' M ']'" := (TensorUnit M) : monoidal_scope.
Notation "'α⊗[' X ';' Y ';' Z ']'" := (tensor_assoc X Y Z)
  : monoidal_scope.
Notation "'λ⊗[' X ']'" := (tensor_unit_l X) : monoidal_scope.
Notation "'ρ⊗[' X ']'" := (tensor_unit_r X) : monoidal_scope.
Local Open Scope monoidal_scope.

(** ** Derived Tensor Laws

    Fix a monoidal category structure on [C]. Derive the tensor's
    respectfulness and functor laws, together with naturality and
    invertibility of its associator and unitors. *)

(** ** 张量的导出定律

    固定 [C] 上的幺半范畴结构，导出张量的保相等性及函子律，以及结合子和单位子的自然性与可逆性。 *)

Section TensorLaws.
Context {C : Cat} `{MC : !MonoidalCat C}.

(** Tensoring arrows preserves specified hom equality. *)

(** 态射张量保持指定 Hom 相等。 *)

Global Instance tensor_map_proper {X X' Y Y' : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq)
      (@tensor_map C MC X X' Y Y').
Proof. apply binoidal_sequence_proper. Qed.

(** Tensor preserves identities using only the separate action laws. *)

(** 仅通过分别作用的定律，张量保持恒等。 *)

Lemma tensor_map_id (X Y : @Ob C)
  : (@id X ⊗m @id Y) ≈ @id (X ⊗ Y).
Proof.
  unfold tensor_map, binoidal_sequence.
  rewrite binoidal_left_id, binoidal_right_id, comp_id_l. reflexivity.
Qed.

(** A fixed identity on the left recovers left context action. *)

(** 左侧固定恒等时，恢复左上下文作用。 *)

Lemma tensor_map_left {X Y : @Ob C} (Z : @Ob C) (f : Hom X Y)
  : (@id Z ⊗m f) ≈ Z ⊲ f.
Proof.
  unfold tensor_map, binoidal_sequence.
  rewrite binoidal_right_id, comp_id_r. reflexivity.
Qed.

(** A fixed identity on the right recovers right context action. *)

(** 右侧固定恒等时，恢复右上下文作用。 *)

Lemma tensor_map_right {X Y : @Ob C} (Z : @Ob C) (f : Hom X Y)
  : (f ⊗m @id Z) ≈ f ⊳ Z.
Proof.
  unfold tensor_map, binoidal_sequence.
  rewrite binoidal_left_id, comp_id_l. reflexivity.
Qed.

(** Interchange makes ordered tensoring jointly functorial. *)

(** 交换律使有序张量联合具有函子性。 *)

Lemma tensor_map_comp {X X' X'' Y Y' Y'' : @Ob C}
    (f' : Hom X' X'') (f : Hom X X')
    (g' : Hom Y' Y'') (g : Hom Y Y')
  : ((f' ∘ f) ⊗m (g' ∘ g)) ≈ (f' ⊗m g') ∘ (f ⊗m g).
Proof.
  exact (central_sequence_comp f' f g' g (monoidal_arrow_central f')).
Qed.

(** The associator is jointly natural by three separate naturality squares. *)

(** 结合子的联合自然性由三个分别自然性方块得到。 *)

Lemma tensor_assoc_natural {X X' Y Y' Z Z' : @Ob C}
    (f : Hom X X') (g : Hom Y Y') (h : Hom Z Z')
  : α⊗[X'; Y'; Z'] ∘ ((f ⊗m g) ⊗m h) ≈
      (f ⊗m (g ⊗m h)) ∘ α⊗[X; Y; Z].
Proof.
  exact (premonoidal_assoc_sequence_natural f g h).
Qed.

(** Left-unitor naturality uses the inherited equation. *)

(** 左单位子自然性使用继承的方程。 *)

Lemma tensor_unit_l_natural {X Y : @Ob C} (f : Hom X Y)
  : λ⊗[Y] ∘ (@id (I⊗[MC]) ⊗m f) ≈ f ∘ λ⊗[X].
Proof. rewrite tensor_map_left. apply premonoidal_unit_l_natural. Qed.

(** Right-unitor naturality uses the inherited equation. *)

(** 右单位子自然性使用继承的方程。 *)

Lemma tensor_unit_r_natural {X Y : @Ob C} (f : Hom X Y)
  : ρ⊗[Y] ∘ (f ⊗m @id (I⊗[MC])) ≈ f ∘ ρ⊗[X].
Proof. rewrite tensor_map_right. apply premonoidal_unit_r_natural. Qed.

(** The original computational inverse of the associator. *)

(** 结合子的原可计算逆。 *)

Definition tensor_assoc_iso (X Y Z : @Ob C)
  : is_iso α⊗[X; Y; Z]
  := (premonoidal_associator X Y Z).2.

(** The original computational inverse of the left unitor. *)

(** 左单位子的原可计算逆。 *)

Definition tensor_unit_l_iso (X : @Ob C)
  : is_iso λ⊗[X]
  := (premonoidal_left_unitor X).2.

(** The original computational inverse of the right unitor. *)

(** 右单位子的原可计算逆。 *)

Definition tensor_unit_r_iso (X : @Ob C)
  : is_iso ρ⊗[X]
  := (premonoidal_right_unitor X).2.

(** The inherited pentagon expressed with the derived bimap. *)

(** 用导出的二元映射表述继承的五边形。 *)

Lemma monoidal_pentagon (W X Y Z : @Ob C)
  : α⊗[W; X; Y ⊗ Z] ∘ α⊗[W ⊗ X; Y; Z] ≈
      (id ⊗m α⊗[X; Y; Z]) ∘
        (α⊗[W; X ⊗ Y; Z] ∘ (α⊗[W; X; Y] ⊗m id)).
Proof.
  rewrite tensor_map_left, tensor_map_right. apply premonoidal_pentagon.
Qed.

(** The inherited triangle expressed with the derived bimap. *)

(** 用导出的二元映射表述继承的三角形。 *)

Lemma monoidal_triangle (X Y : @Ob C)
  : (id ⊗m λ⊗[Y]) ∘ α⊗[X; I⊗[MC]; Y] ≈ ρ⊗[X] ⊗m id.
Proof.
  rewrite tensor_map_left, tensor_map_right. apply premonoidal_triangle.
Qed.

End TensorLaws.

(** The tensor bifunctor is computed, not stored as another choice.
    Pair projections preserve reduction on an undestructed input pair. *)

(** 张量双函子通过计算得到，不另作选择。对投影保留未拆解输入对上的归约。 *)

Program Definition tensorF {C : Cat} (MC : MonoidalCat C)
  : Fct (C ×C C) C
  :=
  {|F0 p := @tensor C MC (fst p) (snd p)
  ; F1 p q f := @tensor_map C MC _ _ _ _ (fst f) (snd f)
  |}.
Next Obligation.
  intros [f1 f2] [g1 g2] [H1 H2].
  apply tensor_map_proper; assumption.
Defined.
Next Obligation. apply tensor_map_id. Defined.
Next Obligation. apply tensor_map_comp. Defined.

(** ** Joint Structural Natural Isomorphisms

    Keep the same monoidal structure. Assemble joint natural associator and
    unitor isomorphisms from the inherited premonoidal coherence. *)

(** ** 联合结构自然同构

    保持同一幺半结构，从继承的预幺半相干性组装联合自然的结合子与单位子同构。 *)

Section NaturalIsomorphisms.
Context {C : Cat} `{MC : !MonoidalCat C}.

(** Package derived joint naturality with the inherited associator. *)

(** 将导出的联合自然性与继承结合子打包。 *)

Program Definition MonoidalAssociatorN
  : TensorLeftF (tensorF MC) ⇒ TensorRightF (tensorF MC)
  :=
  {|nt p := α⊗[fst (fst p); snd (fst p); snd p]
  |}.
Next Obligation.
  destruct X as [[x y] z], Y as [[x' y'] z'], f as [[f g] h].
  apply tensor_assoc_natural.
Defined.

(** The natural isomorphism retains the same component inverses. *)

(** 自然同构保留相同的分量逆。 *)

Definition monoidal_associator
  : TensorLeftF (tensorF MC) ≅N TensorRightF (tensorF MC)
  := (MonoidalAssociatorN;
      λ p, tensor_assoc_iso (fst (fst p)) (snd (fst p)) (snd p)).

(** Package the inherited left unitor as a natural transformation. *)

(** 将继承左单位子打包为自然变换。 *)

Program Definition MonoidalLeftUnitorN
  : π2F (tensorF MC) (I⊗[MC]) ⇒ IdF
  :=
  {|nt X := λ⊗[X]
  |}.
Next Obligation. apply tensor_unit_l_natural. Defined.

(** Package the inherited right unitor as a natural transformation. *)

(** 将继承右单位子打包为自然变换。 *)

Program Definition MonoidalRightUnitorN
  : π1F (tensorF MC) (I⊗[MC]) ⇒ IdF
  :=
  {|nt X := ρ⊗[X]
  |}.
Next Obligation. apply tensor_unit_r_natural. Defined.

(** The natural left-unitor isomorphism keeps its selected inverse. *)

(** 左单位自然同构保留其选定逆。 *)

Definition monoidal_left_unitor
  : π2F (tensorF MC) (I⊗[MC]) ≅N IdF
  := (MonoidalLeftUnitorN; tensor_unit_l_iso).

(** The natural right-unitor isomorphism keeps its selected inverse. *)

(** 右单位自然同构保留其选定逆。 *)

Definition monoidal_right_unitor
  : π1F (tensorF MC) (I⊗[MC]) ≅N IdF
  := (MonoidalRightUnitorN; tensor_unit_r_iso).

End NaturalIsomorphisms.
