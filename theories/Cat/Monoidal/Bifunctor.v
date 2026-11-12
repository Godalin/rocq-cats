From Cats Require Export
  Cat.Monoidal.Core.

Local Open Scope binoidal_scope.

(** * Assembly from a Tensor Bifunctor

    Existing models may supply one bifunctor and natural structural
    isomorphisms. This constructor extracts their premonoidal parent and
    proves interchange once, without storing a second tensor. *)

(** * 从张量双函子装配

    已有模型可以提供一个双函子及自然结构同构。本构造提取其预幺半父结构，
    统一证明交换律，不另存第二个张量。 *)

Section Assembly.
Context {C : Cat} (T : Functor (C ×C C) C) (I : @Ob C)
    (A : TensorLeftF T ≅N TensorRightF T)
    (L : π2F T I ≅N IdF) (R : π1F T I ≅N IdF).

Let BC
  : BinoidalCat C
  := BifunctorBinoidal T.
Local Existing Instance BC.

Context
    (Hp : ∀ W X Y Z : @Ob C,
      A.1 ((W, X), Y ⊗ Z) ∘ A.1 ((W ⊗ X, Y), Z) ≈
        (W ⊲ A.1 ((X, Y), Z)) ∘
          (A.1 ((W, X ⊗ Y), Z) ∘ (A.1 ((W, X), Y) ⊳ Z)))
    (Ht : ∀ X Y : @Ob C,
      (X ⊲ L.1 Y) ∘ A.1 ((X, I), Y) ≈ (R.1 X) ⊳ Y).

(** Retain every supplied object and structural inverse. Only derived
    action laws, centrality and separate naturality are reconstructed. *)

(** 保留给定的全部对象与结构逆；仅重建导出的作用定律、中心性及分别自然性。 *)

Program Definition BifunctorMonoidal
  : MonoidalCat C
  :=
  {|MonoidalP :=
      {|PremonoidalB := BC
      ; PremonoidalUnit := I
      ; premonoidal_associator X Y Z := (A.1 ((X, Y), Z); A.2 ((X, Y), Z))
      ; premonoidal_left_unitor X := (L.1 X; L.2 X)
      ; premonoidal_right_unitor X := (R.1 X; R.2 X)
      ; premonoidal_assoc_central X Y Z := bifunctor_arrow_central T _
      ; premonoidal_unit_l_central X := bifunctor_arrow_central T _
      ; premonoidal_unit_r_central X := bifunctor_arrow_central T _
      ; premonoidal_unit_l_natural X Y f := nt_naturality L.1 f
      ; premonoidal_unit_r_natural X Y f := nt_naturality R.1 f
      ; premonoidal_pentagon := Hp
      ; premonoidal_triangle := Ht
      |}
  ; monoidal_interchange X X' Y Y' f g :=
      fst (bifunctor_arrow_central T f Y Y' g)
  |}.
Next Obligation.
  pose proof (nt_naturality A.1
    (X := ((X, Y), Z)) (Y := ((X', Y), Z)) ((f, id), id)) as H.
  cbn in H. etransitivity; [exact H |].
  apply comp_proper; [| reflexivity].
  apply functor_fmap_proper. split; [reflexivity | apply functor_id].
Defined.
Next Obligation.
  exact (nt_naturality A.1
    (X := ((X, Y), Z)) (Y := ((X, Y'), Z)) ((id, g), id)).
Defined.
Next Obligation.
  pose proof (nt_naturality A.1
    (X := ((X, Y), Z)) (Y := ((X, Y), Z')) ((id, id), h)) as H.
  cbn in H. etransitivity; [| exact H].
  apply comp_proper; [reflexivity |].
  apply functor_fmap_proper. split;
    [symmetry; apply functor_id | reflexivity].
Defined.

(** The reconstructed bimap agrees with the original functor action.
    No equality of functor records or proof witnesses is required. *)

(** 重建的二元映射与原函子作用相等，不要求函子记录或证明见证相等。 *)

Lemma bifunctor_monoidal_map {X X' Y Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y')
  : @tensor_map C BifunctorMonoidal X X' Y Y' f g ≈
      fmap T (X := (X, Y)) (Y := (X', Y')) (f, g).
Proof. apply bifunctor_sequence. Qed.

(** Compare the reconstructed tensor functor with the supplied one by
    identity components, rather than equality of their records. *)

(** 用恒等分量比较重建张量函子与给定函子，不要求其记录相等。 *)

Program Definition BifunctorTensorN
  : tensorF BifunctorMonoidal ⇒ T
  :=
  {|nt p := _
  |}.
Next Obligation. destruct p as [X Y]. exact id. Defined.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g].
  rewrite comp_id_l, comp_id_r. exact (bifunctor_monoidal_map f g).
Defined.

(** Both comparison directions compute to identities on each object pair. *)

(** 对每个对象对，两个比较方向都计算为恒等。 *)

Definition bifunctor_monoidal_iso
  : tensorF BifunctorMonoidal ≅N T.
Proof.
  exists BifunctorTensorN. intros [X Y].
  exists id. split; apply comp_id_l.
Defined.

End Assembly.
