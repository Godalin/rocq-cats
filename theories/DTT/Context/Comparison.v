From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  Instance.Set.Fam.Fixed
  Instance.Set.Fam.Lift
  DTT.CwF
  DTT.Context.Elements
  DTT.Display.Section.

(** * Comparing Original and Recovered Type-and-Term Functors

    Fix chosen context extensions for a family-valued presheaf. Raise both
    term fibers to common carrier and equality bounds, retaining the type
    base. Assemble the accepted fiber maps and coherence laws through the
    category of fixed-base families. No terminal context is required. *)

(** * 比较原类型—项函子与恢复函子

    固定族值预层的选定上下文扩张，将两侧项纤维提升至共同载体及相等大小界，
    保留类型基底。通过固定基底族范畴组装已有纤维映射和相干律；无需终上下文。 *)

Section ContextElementsComparison.
Context {C : Cat} (T : Fct (C^op) FamCat)
    `{HC : !HasContextExtension T}.
Let P := FamBaseF ∘F T.
Let HD := @ContextElements_HasDisplay C T HC.

(** The lifted forward term map commutes with type transport. The type
    base itself is not lifted. *)

(** 提升后的前向项映射与类型运输交换，类型基底本身不作提升。 *)

Program Definition ContextElementsFiberMap@{v q +} (Γ : @Ob C)
  : (LiftFamS (Tm T Γ) : FamS@{_ _ _ v q} (Ty T Γ)) →Fam
      (LiftFamS (@DisplayTerms C P HD Γ)
        : FamS@{_ _ _ v q} (Ty T Γ))
  := {|fam_map A := (context_elements_term_resp T A)^↑S|}.
Next Obligation.
  destruct a as [t]. constructor. apply context_elements_term_conv.
Defined.

(** The lifted backward term map uses the accepted inverse transport
    coherence, without comparing law witnesses. *)

(** 提升后的逆向项映射使用已有逆运输相干律，不比较律见证。 *)

Program Definition ContextElementsFiberInvMap@{v q +} (Γ : @Ob C)
  : (LiftFamS (@DisplayTerms C P HD Γ)
        : FamS@{_ _ _ v q} (Ty T Γ)) →Fam
      (LiftFamS (Tm T Γ) : FamS@{_ _ _ v q} (Ty T Γ))
  := {|fam_map A := (context_elements_term_inv_resp T A)^↑S|}.
Next Obligation.
  destruct a as [s]. constructor. apply context_elements_term_inv_conv.
Defined.

(** Pointwise inverse laws give an inverse in the fixed-base family
    category. Both directions retain their computational data. *)

(** 逐点互逆律给出固定基底族范畴中的逆，两方向均保留计算数据。 *)

Definition context_elements_fiber_map_iso@{v q +} (Γ : @Ob C)
  : @is_iso (FamSCat (Ty T Γ))
      (LiftFamS (Tm T Γ) : FamS@{_ _ _ v q} (Ty T Γ))
      (LiftFamS (@DisplayTerms C P HD Γ)
        : FamS@{_ _ _ v q} (Ty T Γ))
      (ContextElementsFiberMap Γ).
Proof.
  exists (ContextElementsFiberInvMap Γ). split; intros A [t]; constructor.
  - apply context_elements_term_β.
  - apply context_elements_term_η.
Defined.

(** Substitution coherence makes the forward comparisons natural. The
    base components are identity maps; equality uses coherent transport. *)

(** 替换相干性使前向比较自然；基底分量为恒等映射，相等使用相干运输。 *)

Program Definition ContextElementsTyTmN@{v q +}
  : ((FamLiftF : Fct FamCat FamCat@{_ _ _ _ _ _ _ _ v q _ _ _ _ _ _})
      ∘F T) ⇒
    ((FamLiftF : Fct FamCat FamCat@{_ _ _ _ _ _ _ _ v q _ _ _ _ _ _})
      ∘F @DisplayTyTmF C P HD)
  := {|nt Γ := fam_map_to_fam (ContextElementsFiberMap Γ)|}.
Next Obligation.
  exists (λ A, reflS (x := (fmap P f A))). intros A [t].
  constructor. etransitivity.
  - apply transpS_id.
  - apply context_elements_term_sub.
Defined.

(** The fixed-base embedding preserves the explicit inverse. Thus the
    lifted type-and-term functors are naturally isomorphic; no equality
    of functor records or unlifted universe-sized categories is asserted. *)

(** 固定基底嵌入保持显式逆，因此提升后的类型—项函子自然同构；
    不宣称函子记录或未提升的不同大小范畴原生相等。 *)

Definition context_elements_ty_tm_iso@{v q +}
  : ((FamLiftF : Fct FamCat FamCat@{_ _ _ _ _ _ _ _ v q _ _ _ _ _ _})
      ∘F T) ≅N
    ((FamLiftF : Fct FamCat FamCat@{_ _ _ _ _ _ _ _ v q _ _ _ _ _ _})
      ∘F @DisplayTyTmF C P HD).
Proof.
  exists ContextElementsTyTmN. intros Γ.
  exact (fct_is_iso (FamFixedF (Ty T Γ))
    (ContextElementsFiberMap Γ) (context_elements_fiber_map_iso Γ)).
Defined.

(** The general natural-inverse construction supplies the reverse
    comparison with the same explicit backward fiber maps. *)

(** 一般自然逆构造提供逆向比较，并保留同一显式逆向纤维映射。 *)

Definition ContextElementsTyTmInvN@{v q +}
  : ((FamLiftF : Fct FamCat FamCat@{_ _ _ _ _ _ _ _ v q _ _ _ _ _ _})
      ∘F @DisplayTyTmF C P HD) ⇒
    ((FamLiftF : Fct FamCat FamCat@{_ _ _ _ _ _ _ _ v q _ _ _ _ _ _})
      ∘F T)
  := InvN ContextElementsTyTmN (context_elements_ty_tm_iso).2.

End ContextElementsComparison.
