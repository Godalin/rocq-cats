From Cats.STLC Require Import NormalPresheaf.
From Cats Require Import
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Renaming World and Presheaf Interface Regressions *)

(** * 重命名世界与预层接口回归检查 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

Section LargerWorldEquality.
Universes b q r l.
Constraint b < q.
Constraint q < r.
Constraint r < l.
Context (B : Type@{b}) (A : Ty B).

(** World hom equality may be larger than syntax-value equality; laws live
    above both. Instantiation must not identify these levels. *)

(** 世界 Hom 相等可以高于语法值的相等，定律位于二者之上；实例化不能合并这些
    层级。 *)

Definition larger_world_NePsh
  : Functor ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{b q _ _ _ _ _}
  := NePsh A.

Definition larger_world_eta
  : @Nat ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{b q _ _ _ _ _} (NePsh A) (NfPsh A)
  := NeutralEtaN A.

Definition larger_world_triangle
  : @NatEq ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{b q _ _ _ _ _} (NePsh A) (TmRenamingPsh A)
      (NeEmbedN A) (NfEmbedN A ∘Nv NeutralEtaN A)
  := neutral_eta_triangle A.

End LargerWorldEquality.

Section LargerValueEquality.
Universes b r q l.
Constraint b < r.
Constraint r < q.
Constraint q < l.
Context (B : Type@{b}) (A : Ty B).

(** The opposite ordering is also supported, including beta/eta terms and
    the interpretation from world arrows to substitutions. *)

(** 相反的层级顺序同样受支持，包括 βη 项及从世界箭头到替换的解释。 *)

Definition larger_value_TmPsh
  : Functor ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{b q _ _ _ _ _}
  := TmRenamingPsh A.

Definition larger_value_triangle
  : @NatEq ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{b q _ _ _ _ _} (NePsh A) (TmRenamingPsh A)
      (NeEmbedN A) (NfEmbedN A ∘Nv NeutralEtaN A)
  := neutral_eta_triangle A.

Definition larger_value_context_interpretation
  : Functor (RenamingCat@{b r l _ _ _ _ _} B)
      (Category.CtxCat@{b q l} B)
  := RenamingToContextF B.

End LargerValueEquality.

Section SmallStructuralEquality.
Universes r b q l.
Constraint r < b.
Constraint b < q.
Constraint q < l.
Context (B : Type@{b}) (A : Ty B).

(** Pointwise variable equality can be smaller than the world carrier;
    beta/eta derivations still bound the signature universe. *)

(** 变量的逐点相等可以低于世界载体；βη 推导仍须容纳签名宇宙。 *)

Definition small_world_triangle
  : @NatEq ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{b q _ _ _ _ _} (NePsh A) (TmRenamingPsh A)
      (NeEmbedN A) (NfEmbedN A ∘Nv NeutralEtaN A)
  := neutral_eta_triangle A.

End SmallStructuralEquality.

Section Computations.
Context {B : Type} (Γ Δ : Ctx B) (p q : B).

(** Weakening acts backwards to the world arrow and computes through the
    presheaf's respectful-map wrapper. *)

(** 弱化作用方向与世界箭头相反，并穿过预层的保相等映射包装直接计算。 *)

Example neutral_presheaf_weakening
    (n : Ne Γ (ty_base p))
  : fmap (NePsh (ty_base p)) (@ren_weaken B Γ (ty_base q)) n =
      n⟨wkRen⟩ne.
Proof. reflexivity. Qed.

(** The natural eta component preserves the higher-order expansion
    computation; it does not introduce an opaque mediator. *)

(** η 自然变换分量保留高阶展开的计算，不引入不透明的中介。 *)

Example eta_component_computes
    (f : Ne Γ ((ty_base p ⇒ ty_base q) ⇒ ty_base q))
  : NeutralEtaN _ Γ f = nf_lam
      (nf_base (ne_app (f⟨wkRen⟩ne)
        (nf_lam (nf_base
          (ne_app (ne_var (var_succ var_zero))
            (nf_base (ne_var var_zero))))))).
Proof. reflexivity. Qed.

(** Invoke naturality through the generic interface rather than unfolding
    the syntactic renaming proof. *)

(** 通过一般接口调用自然性，而不是展开语法重命名证明。 *)

Example eta_naturality_interface (A : Ty B) (ρ : Ren Δ Γ) (n : Ne Γ A)
  : NeutralEtaN A Δ (fmap (NePsh A) ρ n) =
      fmap (NfPsh A) ρ (NeutralEtaN A Γ n).
Proof. exact (nt_naturality (NeutralEtaN A) ρ n). Qed.

End Computations.

(** Two parallel world arrows select different unit variables. They remain
    different in world hom equality, but unit eta identifies their images
    in the substitution category. This guards the equality-policy boundary. *)

(** 两条平行世界箭头选取不同的单位变量。它们在世界 Hom 相等下仍不同，但单位
    η 识别了它们在替换范畴中的像。这检查两种相等约定之间的边界。 *)

Definition OneUnitWorld
  : Ctx Empty_set
  := ∅ ▻ ⊤.

Definition older_unit_ren
  : Ren (OneUnitWorld ▻ ⊤) OneUnitWorld
  := wkRen.

Definition newest_unit_ren
  : Ren (OneUnitWorld ▻ ⊤) OneUnitWorld
  := λ A x, match x with
     | inl x => match x with end
     | inr x => inr x
     end.

Definition parallel_unit_world_arrows_distinct
  : older_unit_ren ≈Ren newest_unit_ren → Empty_set.
Proof.
  intros h. specialize (h ⊤ var_zero). discriminate h.
Defined.

Example parallel_unit_world_images_agree
  : fmap (RenamingToContextF Empty_set) older_unit_ren ≈
      fmap (RenamingToContextF Empty_set) newest_unit_ren.
Proof.
  intros A [x | x]; [destruct x | destruct x].
  eapply tm_eq_trans.
  - apply tm_eq_unit_η.
  - apply tm_eq_sym. apply tm_eq_unit_η.
Defined.
