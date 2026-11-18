From Cats Require Export
  Cat.Binoidal.Bifunctor
  Cat.Premonoidal.Core.

Local Open Scope binoidal_scope.

(** * Structural Choices from a Tensor Bifunctor

    Restrict joint natural isomorphisms to the separate tensor actions.
    Associativity and unitors can be constructed independently. Their
    combination uses only the triangle connecting the supplied choices. *)

(** * 从张量双函子得到结构选择

    将联合自然同构限制到分别张量作用上。结合性与单位子可独立构造；组合时
    只使用连接给定选择的三角形。 *)

Section Assembly.
Context {C : Cat} (T : Fct (C ×C C) C).

Let BC
  : HasBinoidal C
  := BifunctorHasBinoidal T.
Local Existing Instance BC.

(** ** Associativity without a Unit

    Fix a joint associator and its pentagon. Naturality in each position
    follows by holding the other two arrows at their identities. *)

(** ** 不带单位的结合性

    固定联合结合子及其五边形。将另两条态射固定为恒等，即得各位置的自然性。 *)

Section Associativity.
Context (A : TensorLF T ≅N TensorRF T)
    (Hp : ∀ W X Y Z : C,
      A.1 ((W, X), Y ⊗ Z) ∘ A.1 ((W ⊗ X, Y), Z) ≈
        (W ⊲ A.1 ((X, Y), Z)) ∘
          (A.1 ((W, X ⊗ Y), Z) ∘ (A.1 ((W, X), Y) ⊳ Z))).

(** The last-variable family stores the original maps and inverses.
    The remaining directions constrain these same components. *)

(** 最后变量族保存原映射及逆，其他方向约束同一组分量。 *)

Program Definition BifunctorHasAssociator
  : HasAssociator C BC
  :=
  {|PremonoidalAssocRIso X Y :=
      ({|nt Z := A.1 ((X, Y), Z)|}; λ Z, A.2 ((X, Y), Z))
  ; isAssociator :=
      {|assoc_natural_l Y Z := {|nat_iso_naturality X X' f := _|}
      ; assoc_natural_m X Z := {|nat_iso_naturality Y Y' g := _|}
      ; assoc_central X Y Z := bifunctor_arrow_central T _
      ; assoc_pentagon := Hp
      |}
  |}.
Next Obligation.
  pose proof (nat_naturality A.1
    (X := ((X, Y), X0)) (Y := ((X, Y), Y0)) ((id, id), f)) as H.
  cbn in H. etransitivity; [| exact H].
  apply comp_proper; [reflexivity |].
  apply fct_fmap_proper. split;
    [symmetry; exact (@fct_id _ _ T (X, Y)) | reflexivity].
Defined.
Next Obligation.
  pose proof (nat_naturality A.1
    (X := ((X, Y), Z)) (Y := ((X', Y), Z)) ((f, id), id)) as H.
  cbn in H. etransitivity; [exact H |].
  apply comp_proper; [| reflexivity].
  apply fct_fmap_proper. split;
    [reflexivity | exact (@fct_id _ _ T (Y, Z))].
Defined.
Next Obligation.
  exact (nat_naturality A.1
    (X := ((X, Y), Z)) (Y := ((X, Y'), Z)) ((id, g), id)).
Defined.

End Associativity.

(** ** Unit Choices without an Associator

    Fix one unit and two joint unitors. Repackage their components at the
    derived action functors, retaining the supplied inverse witnesses. *)

(** ** 不带结合子的单位选择

    固定唯一单位及两个联合单位子。按导出的作用函子重新打包分量，保留给定
    的逆见证。 *)

Section Unit.
Context (I : C) (L : π2F T I ≅N IdF) (R : π1F T I ≅N IdF).

(** No associativity or coherence with an associator is needed here. *)

(** 此处无需结合性或与结合子的相干性。 *)

Program Definition BifunctorHasUnitors
  : HasUnitors C BC
  :=
  {|PremonoidalUnit := I
  ; PremonoidalUnitorLIso :=
      ({|nt X := L.1 X|}; L.2)
  ; PremonoidalUnitorRIso :=
      ({|nt X := R.1 X|}; R.2)
  ; isUnitors :=
      {|unitor_l_central X := bifunctor_arrow_central T _
      ; unitor_r_central X := bifunctor_arrow_central T _
      |}
  |}.
Next Obligation. exact (nat_naturality L.1 f). Defined.
Next Obligation. exact (nat_naturality R.1 f). Defined.

End Unit.

(** ** Compatible Choices

    The independently built choices share exactly [BC]. Only their
    triangle remains when constructing the premonoidal extension. *)

(** ** 相容选择

    独立构造的选择共享恰好同一 [BC]；构造预幺半扩展时只剩三角形条件。 *)

Section Compatibility.
Context (I : C) (A : TensorLF T ≅N TensorRF T)
    (L : π2F T I ≅N IdF) (R : π1F T I ≅N IdF)
    (Hp : ∀ W X Y Z : C,
      A.1 ((W, X), Y ⊗ Z) ∘ A.1 ((W ⊗ X, Y), Z) ≈
        (W ⊲ A.1 ((X, Y), Z)) ∘
          (A.1 ((W, X ⊗ Y), Z) ∘ (A.1 ((W, X), Y) ⊳ Z)))
    (Ht : ∀ X Y : C,
      (X ⊲ L.1 Y) ∘ A.1 ((X, I), Y) ≈ (R.1 X) ⊳ Y).

(** Combine the two choices without selecting any additional operation. *)

(** 组合两份选择，不另选运算。 *)

Program Definition BifunctorHasPremonoidal
  : HasPremonoidal C BC
  :=
  {|hasAssociator := BifunctorHasAssociator A Hp
  ; hasUnitors := BifunctorHasUnitors I L R
  ; isPremonoidal :=
      ({|premonoidal_compatible_triangle := _|}
        : IsPremonoidal (BifunctorHasAssociator A Hp)
            (BifunctorHasUnitors I L R))
  |}.

Next Obligation. exact (Ht X Y). Defined.

End Compatibility.
End Assembly.
