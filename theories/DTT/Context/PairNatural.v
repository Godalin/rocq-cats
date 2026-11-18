From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Isomorphism
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  DTT.CwF
  DTT.Context.Extension
  DTT.Context.Elements
  DTT.Context.PairComparison
  DTT.Context.LiftedRepresentation
  DTT.Display.Section
  DTT.Display.Representation.

(** * Natural Comparison of Canonical Context-Pair Representations

    Fix the original chosen extensions and their canonical recovery.
    Lift the accepted pair maps to independent common carrier and equality
    bounds. Compare the resulting presheaves and their pairing representations;
    derive the inverse representation square from the general isomorphism
    square theorem. No terminal context or equality of structures is used. *)

(** * 规范上下文配对表示的自然比较

    固定原选定扩张及其规范恢复，将已有配对映射提升至相互独立的共同载体与
    相等上界。比较所得预层及其配对表示，再由一般同构方块定理导出逆表示方块；
    不使用终上下文或结构相等。 *)

Section ContextElementsPairNatural.
Context {C : Cat} (T : Fct (C^op) FamCat)
  `{HC : !HasContextExtension T}.
Let P := FamBaseF ∘F T.
Let HD := @ContextElements_HasDisplay C T HC.
Let R := @DisplayTyTmF C P HD.
Let HR := @Display_HasContextExtension C P HD.

(** Leave this obligation unreduced: eager simplification would unfold
    the complete canonical recovery. Apply its accepted coherence directly. *)

(** 保留此义务而不预化简，避免急切展开整个规范恢复；直接应用已有相干律。 *)

Local Obligation Tactic := idtac.

(** The accepted reindexing square makes the lifted forward pair maps
    natural. The native base substitution is unchanged. *)

(** 已有重索引方块使提升的前向配对映射自然，原生基底替换保持不变。 *)

Program Definition ContextElementsPairN@{v q +} {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF R A)
  :=
  {|nt Δ := (@context_elements_pair_resp C T HC Γ A Δ)^↑S|}.
Next Obligation.
  intros Γ A X Y f [x]. constructor.
  exact (@context_elements_pair_sub C T HC Γ X Y A f x).
Defined.

Local Obligation Tactic := cats_obligation.

(** Pointwise inverse pair laws give the natural isomorphism. Only the
    explicit wrappers share ambient sizes, not the original term fibers. *)

(** 逐点配对互逆律给出自然同构，仅显式包装共享环境大小，原项纤维不必同层。 *)

Definition context_elements_pair_nat_iso@{v q +} {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A) ≅N
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF R A).
Proof.
  exists (ContextElementsPairN A). intros Δ.
  exists ((@context_elements_pair_inv_resp C T HC Γ A Δ)^↑S).
  split; intros [x]; constructor.
  - exact (@context_elements_pair_β C T HC Γ Δ A x).
  - exact (@context_elements_pair_η C T HC Γ Δ A x).
Defined.

(** Natural inversion keeps the accepted backward pair components. *)

(** 自然取逆保留已有逆向配对分量。 *)

Definition ContextElementsPairInvN@{v q +} {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF R A) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A)
  := InvN (ContextElementsPairN A) (context_elements_pair_nat_iso A).2.

(** The comparison preserves the chosen representing arrows, as an
    equation of natural transformations rather than of law records. *)

(** 比较保持选定表示态射，结论是自然变换的方程，不是律记录的相等。 *)

Theorem context_elements_pair_natural_square@{v q +} {Γ : @Ob C}
    (A : Ty T Γ)
  : (@ContextPairLiftN C R HR Γ A ∘Nv ContextElementsPairN A
      : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A) ⇒
          ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A)))
      ≈N ContextPairLiftN T A.
Proof.
  intros Δ [[σ t]]. constructor.
  exact (@context_elements_pair C T HC Γ Δ A σ t).
Defined.

(** Invert the two representation isomorphisms of the preceding square.
    This derives compatibility with unpairing without another universal
    property argument or equality of inverse witnesses. *)

(** 将前一方块的两个表示同构取逆，导出逆配对相容性，不重证泛性质，
    也不要求逆见证相等。 *)

Theorem context_elements_unpair_natural_square@{v q +} {Γ : @Ob C}
    (A : Ty T Γ)
  : (ContextElementsPairN A ∘Nv ContextUnpairLiftN T A
      : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A)) ⇒
          ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF R A))
      ≈N @ContextUnpairLiftN C R HR Γ A.
Proof.
  pose (i := (ContextPairLiftN T A;
    nat_iso_is_iso (ContextPairLiftN T A) (context_pair_lifted_nat_iso T A).2)).
  pose (j := (@ContextPairLiftN C R HR Γ A;
    nat_iso_is_iso (@ContextPairLiftN C R HR Γ A)
      (@context_pair_lifted_nat_iso C R HR Γ A).2)).
  assert (H : (j.1 ∘Nv ContextElementsPairN A) ≈N (IdN ∘Nv i.1)).
  { transitivity (ContextPairLiftN T A).
    - exact (context_elements_pair_natural_square A).
    - intros Δ x. reflexivity. }
  pose proof (@iso_square_inv (FctCat (C^op) SetCat) _ _ _ _
    i j (ContextElementsPairN A) IdN H) as K.
  intros Δ x. symmetry. exact (K Δ x).
Defined.

End ContextElementsPairNatural.
