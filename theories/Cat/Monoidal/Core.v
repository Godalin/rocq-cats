From Cats Require Export
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Monoidal Categories

    A tensor is a bifunctor, not necessarily a categorical product. Its
    associator and unitors are chosen natural isomorphisms; coherence uses
    the specified hom equality. No equality of functor records is needed. *)

(** * 幺半范畴

    张量是双函子，不必是范畴积。结合子与单位子是选定自然同构，相干性使用
    指定 Hom 相等，不要求函子记录相等。 *)

(** The left bracketing of a tensor on triples. *)

(** 三个对象上的左括号张量函子。 *)

Definition TensorLeftF {C : Cat} (T : Functor (C ×C C) C)
  : Functor ((C ×C C) ×C C) C
  := T ∘F (T ×F IdF).

(** The right bracketing, on the same triple-product source. *)

(** 在同一个三重乘积来源上的右括号张量函子。 *)

Program Definition TensorRightF {C : Cat} (T : Functor (C ×C C) C)
  : Functor ((C ×C C) ×C C) C
  :=
  {|F0 p := T (fst (fst p), T (snd (fst p), snd p))
  ; F1 p q f := fmap T
      (X := (fst (fst p), T (snd (fst p), snd p)))
      (Y := (fst (fst q), T (snd (fst q), snd q)))
      (fst (fst f), fmap T
        (X := (snd (fst p), snd p)) (Y := (snd (fst q), snd q))
        (snd (fst f), snd f))
  |}.
Next Obligation.
  intros [[f g] h] [[f' g'] h'] [[Hf Hg] Hh]. cbn.
  apply functor_fmap_proper. split; [exact Hf |].
  exact (@functor_fmap_proper _ _ T
    (snd (fst X), snd X) (snd (fst Y), snd Y)
    (g, h) (g', h') (Hg, Hh)).
Defined.
Next Obligation.
  transitivity (fmap T
    (X := (fst (fst X), T (snd (fst X), snd X)))
    (Y := (fst (fst X), T (snd (fst X), snd X))) (id, id)).
  - apply functor_fmap_proper. split; [reflexivity |].
    exact (@functor_id _ _ T (snd (fst X), snd X)).
  - apply functor_id.
Defined.
Next Obligation.
  etransitivity; [| apply functor_comp].
  apply functor_fmap_proper. split; [reflexivity |].
  exact (@functor_comp _ _ T
    (snd (fst X), snd X) (snd (fst Y), snd Y) (snd (fst Z), snd Z)
    (snd (fst f), snd f) (snd (fst g), snd g)).
Defined.

(** A monoidal structure on the named category [C]. The natural
    isomorphisms retain their inverse components. The intermediate tensor
    and coherence components are computed fields, not additional choices.

    Pentagon and triangle are equations of arrows with fixed endpoints.
    Neither the tensor unit nor the tensor is required to be terminal or
    a product, respectively. Carrier, equality and law sizes are inferred
    independently from the underlying category and natural isomorphisms. *)

(** 指定范畴 [C] 上的幺半结构。自然同构保留各分量的逆，中间张量运算及相干
    分量都是计算字段，不是额外选取。

    五边形与三角形是固定端点的态射方程，不要求张量单位为终对象，也不要求
    张量为积。载体、相等及定律的大小由底层范畴和自然同构分别推导。 *)

Class MonoidalCategory (C : Cat)
  :=
  { tensorF : Functor (C ×C C) C
  ; TensorUnit : @Ob C
  ; monoidal_associator : TensorLeftF tensorF ≅N TensorRightF tensorF
  ; monoidal_left_unitor : π2F tensorF TensorUnit ≅N IdF
  ; monoidal_right_unitor : π1F tensorF TensorUnit ≅N IdF
  ; tensor (X Y : @Ob C) := tensorF (X, Y)
  ; tensor_map {X X' Y Y' : @Ob C}
      (f : Hom X X') (g : Hom Y Y')
      : Hom (tensor X Y) (tensor X' Y')
    := fmap tensorF (X := (X, Y)) (Y := (X', Y')) (f, g)
  ; tensor_assoc (X Y Z : @Ob C)
      : Hom (tensor (tensor X Y) Z) (tensor X (tensor Y Z))
    := monoidal_associator.1 ((X, Y), Z)
  ; tensor_unit_l (X : @Ob C) : Hom (tensor TensorUnit X) X
    := monoidal_left_unitor.1 X
  ; tensor_unit_r (X : @Ob C) : Hom (tensor X TensorUnit) X
    := monoidal_right_unitor.1 X
  ; monoidal_pentagon (W X Y Z : @Ob C)
    : tensor_assoc W X (tensor Y Z) ∘ tensor_assoc (tensor W X) Y Z ≈
        tensor_map id (tensor_assoc X Y Z) ∘
          (tensor_assoc W (tensor X Y) Z ∘
            tensor_map (tensor_assoc W X Y) id)
  ; monoidal_triangle (X Y : @Ob C)
    : tensor_map id (tensor_unit_l Y) ∘ tensor_assoc X TensorUnit Y ≈
        tensor_map (tensor_unit_r X) id
  }.

Arguments tensorF {_} _.
Arguments TensorUnit {_} _.
Arguments tensor {_ _} _ _.
Arguments tensor_map {_ _ _ _ _ _} _ _.
Arguments tensor_assoc {_ _} _ _ _.
Arguments tensor_unit_l {_ _} _.
Arguments tensor_unit_r {_ _} _.

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

Section TensorLaws.
Context {C : Cat} `{MC : !MonoidalCategory C}.

(** Tensoring arrows preserves the specified equality in both variables. *)

(** 态射张量在两个变量上保持指定相等。 *)

Global Instance tensor_map_proper {X X' Y Y' : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq)
      (@tensor_map C MC X X' Y Y').
Proof.
  intros f f' Hf g g' Hg.
  exact (@functor_fmap_proper _ _ (tensorF MC) (X, Y) (X', Y')
    (f, g) (f', g') (Hf, Hg)).
Qed.

(** Tensor preserves a pair of identities. *)

(** 张量保持一对恒等态射。 *)

Lemma tensor_map_id (X Y : @Ob C)
  : (@id X ⊗m @id Y) ≈ @id (X ⊗ Y).
Proof. exact (@functor_id _ _ (tensorF MC) (X, Y)). Qed.

(** Bifunctoriality is the interchange equation for tensor and composition. *)

(** 双函子性就是张量与复合的交换方程。 *)

Lemma tensor_map_comp {X X' X'' Y Y' Y'' : @Ob C}
    (f' : Hom X' X'') (f : Hom X X')
    (g' : Hom Y' Y'') (g : Hom Y Y')
  : ((f' ∘ f) ⊗m (g' ∘ g)) ≈ (f' ⊗m g') ∘ (f ⊗m g).
Proof.
  exact (@functor_comp _ _ (tensorF MC)
    (X, Y) (X', Y') (X'', Y'') (f', g') (f, g)).
Qed.

(** The associator is natural in all three tensor arguments. *)

(** 结合子在三个张量变量上自然。 *)

Lemma tensor_assoc_natural {X X' Y Y' Z Z' : @Ob C}
    (f : Hom X X') (g : Hom Y Y') (h : Hom Z Z')
  : α⊗[X'; Y'; Z'] ∘ ((f ⊗m g) ⊗m h) ≈
      (f ⊗m (g ⊗m h)) ∘ α⊗[X; Y; Z].
Proof.
  exact (nt_naturality (monoidal_associator.1)
    (X := ((X, Y), Z)) (Y := ((X', Y'), Z')) ((f, g), h)).
Qed.

(** The left unitor is natural. *)

(** 左单位子自然。 *)

Lemma tensor_unit_l_natural {X Y : @Ob C} (f : Hom X Y)
  : λ⊗[Y] ∘ (@id (I⊗[MC]) ⊗m f) ≈ f ∘ λ⊗[X].
Proof. exact (nt_naturality (monoidal_left_unitor.1) f). Qed.

(** The right unitor is natural. *)

(** 右单位子自然。 *)

Lemma tensor_unit_r_natural {X Y : @Ob C} (f : Hom X Y)
  : ρ⊗[Y] ∘ (f ⊗m @id (I⊗[MC])) ≈ f ∘ ρ⊗[X].
Proof. exact (nt_naturality (monoidal_right_unitor.1) f). Qed.

(** The associator component comes with a computational inverse. *)

(** 结合子分量具有可计算的逆。 *)

Definition tensor_assoc_iso (X Y Z : @Ob C)
  : is_iso α⊗[X; Y; Z]
  := monoidal_associator.2 ((X, Y), Z).

(** The left unitor component comes with a computational inverse. *)

(** 左单位子分量具有可计算的逆。 *)

Definition tensor_unit_l_iso (X : @Ob C)
  : is_iso λ⊗[X]
  := monoidal_left_unitor.2 X.

(** The right unitor component comes with a computational inverse. *)

(** 右单位子分量具有可计算的逆。 *)

Definition tensor_unit_r_iso (X : @Ob C)
  : is_iso ρ⊗[X]
  := monoidal_right_unitor.2 X.

End TensorLaws.
