From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.CatCat
  Cat.Equivalence.Adjunction
  Cat.Diagram.Core
  Cat.Limit.Core
  Cat.Limit.Preservation
  Cat.Limit.Transport.

(** * Limits along Specified Equivalences

    The general construction keeps the two categories' native size levels
    and the indexing category independent. Chosen limits are enabled only
    by an explicit constructor. *)

(** * 沿指定等价运输极限

    一般构造保持两侧范畴的原生大小层级及索引范畴独立；选定极限仅通过显式
    构造器启用。 *)

Local Open Scope cat_scope.
Local Open Scope hom_scope.

(** Full faithfulness reflects a candidate limiting cone. The target
    mediator is lifted by fullness and its equations by faithfulness. *)

(** 全忠实性反映候选极限锥；满性提升目标中介，忠实性反映其方程。 *)

Definition fully_faithful_reflects_limit {J C D : Cat}
    (F : Functor C D) (HF : is_fully_faithful F)
    {K : Functor J C} {L : @Ob C} {κ : L ⇒Δ K}
    (Hκ : is_limit (MapCone F κ))
  : is_limit κ.
Proof.
  intros X μ.
  destruct (Hκ (F X) (MapCone F μ)) as [h Hh].
  destruct (fst HF X L h) as [f Hf].
  exists f. refine {|this := _
                   ; that := _
                   |}.
  - intros j. apply (snd HF).
    change (fmap F (κ j ∘ f) ≈ fmap F (μ j)).
    rewrite functor_comp, Hf. exact (@this _ _ _ _ _ Hh j).
  - intros g Hg. apply (snd HF). transitivity h; [| symmetry; exact Hf].
    apply (@that _ _ _ _ _ Hh). intros j.
    change (fmap F (κ j) ∘ fmap F g ≈ fmap F (μ j)).
    rewrite <- functor_comp. apply functor_fmap_proper. exact (Hg j).
Defined.

Section QuasiInverseLimits.
Context {C D : Cat} (F : Functor C D) (G : Functor D C)
    (u : (G ∘F F) ≅N IdF) (v : (F ∘F G) ≅N IdF).

(** A quasi-inverse functor preserves every candidate limit, by its
    constructed right-adjoint structure. *)

(** 拟逆函子通过构造得到的右伴随结构保持任意候选极限。 *)

Definition quasi_inverse_preserves_limit {J : Cat} {K : Functor J C}
    {L : @Ob C} {κ : L ⇒Δ K} (Hκ : is_limit κ)
  : is_limit (MapCone F κ)
  := right_adjoint_preserves_limit (QuasiInverseAdjunction G F v u) Hκ.

(** Evaluate the target isomorphism on a diagram, without identifying
    the two parenthesizations of functor composition as records. *)

(** 在图式上求值目标同构，不将函子复合的两种括号视为记录原生相等。 *)

Program Definition QuasiInverseDiagramN {J : Cat} (K : Functor J D)
  : (F ∘F (G ∘F K)) ⇒ K
  :=
  {|nt j := v.1 (K j)
  |}.
Next Obligation. exact (nt_naturality v.1 (fmap K f)). Qed.

(** Each diagram comparison component keeps its supplied inverse. *)

(** 每个图式比较分量保留给定的逆。 *)

Definition quasi_inverse_diagram_iso {J : Cat} (K : Functor J D)
  : QuasiInverseDiagramN K ⦂ (F ∘F (G ∘F K)) ≅N K
  := λ j, v.2 (K j).

(** Choose a limit of a target diagram from a chosen limit of its inverse
    image. Preservation and diagram-isomorphism transport supply the proof. *)

(** 由目标图式逆像的选定极限选择其极限；证明复用保持性及图式同构运输。 *)

Program Definition QuasiInverseLimit {J : Cat} (K : Functor J D)
    `{HL : !HasLimit C (G ∘F K)}
  : HasLimit D K
  :=
  {|Lim := F (lim (G ∘F K))
  ; limit_cone := QuasiInverseDiagramN K ∘Nv
      MapCone F (πlim[G ∘F K])
  |}.
Next Obligation.
  exact (limit_transport (QuasiInverseDiagramN K)
    (quasi_inverse_diagram_iso K)
    (quasi_inverse_preserves_limit (limit_universal (G ∘F K)))).
Defined.

(** Transfer all selected limits of a shape, without choosing a global
    model or imposing a bound on that shape. *)

(** 运输某形状的全部选定极限，不全局选择模型，也不对形状施加大小界。 *)

Program Definition QuasiInverseLimits (J : Cat)
    `{HL : !HasLimitsOfShape C J}
  : HasLimitsOfShape D J
  :=
  {|hasLimit K := QuasiInverseLimit K
  |}.

End QuasiInverseLimits.

(** Transfer chosen limits along the ordinary category-equivalence view. *)

(** 沿通常的范畴等价视图运输选定极限。 *)

Definition EquivalenceLimits {C D : Cat} (e : C ≃C D) (J : Cat)
    `{HL : !HasLimitsOfShape C J}
  : HasLimitsOfShape D J
  := QuasiInverseLimits e.1 e.2.1 (fst e.2.2) (snd e.2.2) J.
