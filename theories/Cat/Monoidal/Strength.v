From Cats Require Export
  Cat.Monoidal.Monoidal.

Local Open Scope monoidal_scope.

(** * Tensorial Strength

    Strength carries an ordinary left context through an effectful right
    input. It is additional chosen data on an endofunctor, distinct from a
    lax tensorator and from invertibility of monoidal comparisons. *)

(** * 张量强度

    强度将左侧通常上下文穿过右侧带效应输入。它是自函子上额外选定的数据，
    不同于 lax tensorator，也不同于幺半比较的可逆性。 *)

Class HasStrength {C : Cat} (MC : HasMonoidal C) (F : Fct C C)
  :=
  (** The two-variable natural map retains an ordinary left context. *)

  (** 二变量自然映射保留左侧通常上下文。 *)

  { strengthN
    : (tensorF (HasMonoidal_interchange MC) ∘F (IdF ×F F)) ⇒
        (F ∘F tensorF (HasMonoidal_interchange MC))

  (** Removing a unit context agrees with mapping the left unitor. *)

  (** 移去单位上下文，等于映射左单位子。 *)

  ; strength_unit (Y : @Ob C)
    : fmap F (tensor_unitor_l (HasTensorUnitors := MC) Y).1 ∘
        strengthN (𝐈[MC], Y) ≈
        (tensor_unitor_l (HasTensorUnitors := MC) (F Y)).1

  (** Nested ordinary contexts are transported coherently with associators. *)

  (** 嵌套通常上下文按结合子相干地运输。 *)

  ; strength_assoc (X Y Z : @Ob C)
    : fmap F (tensor_assoc (HasTensorAssoc := MC) X Y Z).1 ∘
        strengthN (tensor (HasBinoidal := MC) X Y, Z) ≈
        strengthN (X, tensor (HasBinoidal := MC) Y Z) ∘
          (tensor_map (IM := HasMonoidal_interchange MC) id (strengthN (Y, Z))) ∘
          (tensor_assoc (HasTensorAssoc := MC) X Y (F Z)).1
  }.

Arguments strengthN {_ _ _} _.
Arguments strength_unit {_ _ _} _ _.
Arguments strength_assoc {_ _ _} _ _ _ _.

Notation "'st[' S ';' X ';' Y ']'" := (strengthN S (X, Y))
  : monoidal_scope.

(** Naturality substitutes ordinary maps in the context and effectful input. *)

(** 自然性在上下文及带效应输入中代入通常映射。 *)

Lemma strength_natural {C : Cat} {MC : HasMonoidal C}
    {F : Fct C C} (S : HasStrength MC F)
    {X X' Y Y' : @Ob C} (f : Hom X X') (g : Hom Y Y')
  : st[S; X'; Y'] ∘ (tensor_map (IM := HasMonoidal_interchange MC) f (fmap F g)) ≈
      fmap F (tensor_map (IM := HasMonoidal_interchange MC) f g) ∘ st[S; X; Y].
Proof.
  exact (nat_naturality (strengthN S) (X := (X, Y)) (Y := (X', Y'))
    (f, g)).
Qed.
