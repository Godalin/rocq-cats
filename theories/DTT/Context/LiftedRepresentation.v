From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  DTT.CwF
  DTT.Context.Extension
  DTT.Context.Representation.

(** * Lifted Representations of Context Pairs

    Fix chosen context extensions. Raise substitution-term pairs and native
    hom-sets to independent common carrier and equality bounds. Pairing and
    its universal laws give a natural isomorphism; its natural inverse uses
    the existing unpairing map. No terminal context or native size equality
    is required. *)

(** * 上下文配对的提升表示

    固定选定上下文扩张，将替换—项配对及原生 Hom 广集提升至相互独立的共同
    载体与相等上界。配对及其泛性质给出自然同构，其自然逆使用已有逆配对映射。
    不要求终上下文或原生大小相等。 *)

Section LiftedContextRepresentation.
Context {C : Cat} (T : Fct (C^op) FamCat)
  `{HC : !HasContextExtension T}.

(** Lift universal pairing, using its existing substitution law for
    naturality. The native term and hom universes remain independent. *)

(** 提升泛配对，由已有替换律得到自然性，保留原生项与 Hom 宇宙的独立性。 *)

Program Definition ContextPairLiftN@{v q +} {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A))
  :=
  {|nt Δ := (context_pair_resp T A Δ)^↑S|}.
Next Obligation.
  intros [[σ t]]. constructor. symmetry.
  exact (@context_pair_comp C T HC Γ X Y A σ t f).
Defined.

(** The inverse laws are the context-pair universal property, expressed
    through the existing data criterion rather than a native SetCat
    representation. Only the explicit wrappers use common upper bounds. *)

(** 互逆律由上下文配对泛性质和已有数据准则给出，不借助原生 SetCat 表示；
    仅显式包装使用共同上界。 *)

Definition context_pair_lifted_nat_iso@{v q +} {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A) ≅N
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A)).
Proof.
  exists (ContextPairLiftN A). intros Δ.
  exists ((context_unpair_resp T A Δ)^↑S). split.
  - intros [[σ t]]. constructor.
    exact (snd (context_pair_data_iff T A (context_proj T A)
      (context_var T A) σ t ⟨σ; t⟩[T, A])
      (@this _ _ _ _ _ (context_pair_universal T A σ t))).
  - intros [h]. constructor. symmetry.
    exact (@context_pair_η C T HC Γ Δ A h).
Defined.

(** The general natural-inverse construction retains the lifted unpairing
    components; no second naturality argument is supplied. *)

(** 一般自然逆构造保留提升后的逆配对分量，无需另行提供自然性证明。 *)

Definition ContextUnpairLiftN@{v q +} {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A)) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A)
  := InvN (ContextPairLiftN A) (context_pair_lifted_nat_iso A).2.

End LiftedContextRepresentation.
