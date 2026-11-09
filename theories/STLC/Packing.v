From Cats Require Export STLC.Category.

(** * Packing Contexts into Product Types

    A context is represented by its nested product type. Packing simultaneous
    assignments and unpacking product terms are inverse up to beta/eta. Their
    substitution laws are structural, without equality of assignment functions. *)

(** * 将上下文打包为积类型

    上下文由其嵌套积类型表示。打包同时赋值与拆包积类型项在 βη 意义下互逆；
    它们的替换律是逐点结构方程，不要求赋值函数相等。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** The empty context contributes unit; extension contributes a binary product. *)

(** 空上下文贡献单位类型，每次扩张贡献一个二元积。 *)

Fixpoint CtxTy {B : Type} (Γ : Ctx B)
  : Ty B
  := match Γ with
  | ctx_empty => ⊤
  | ctx_snoc Γ A => CtxTy Γ × A
  end.

Notation "'⟦' Γ '⟧Ty'" := (CtxTy Γ) : stlc_ty_scope.

(** Package all assigned terms into a term of the context's product type. *)

(** 将所有已赋的项打包为上下文积类型中的一个项。 *)

Fixpoint ctx_pack {B : Type} {Γ Δ : Ctx B} (σ : Sub Δ Γ)
  : Tm Δ ⟦Γ⟧Ty
  := match Γ as Γ return Sub Δ Γ → Tm Δ ⟦Γ⟧Ty with
  | ctx_empty => λ _, ⋆
  | ctx_snoc Γ A => λ σ,
      ⟨ctx_pack (λ U x, σ U (var_succ x)), σ A var_zero⟩
  end σ.

Notation "'⌜' σ '⌝'" := (ctx_pack σ) : stlc_tm_scope.

(** Project a product term into simultaneous assignments for its context. *)

(** 将积类型项投影为其上下文的同时赋值。 *)

Fixpoint ctx_unpack {B : Type} (Γ : Ctx B) {Δ : Ctx B}
    (t : Tm Δ ⟦Γ⟧Ty)
  : Sub Δ Γ
  := match Γ as Γ return Tm Δ ⟦Γ⟧Ty → Sub Δ Γ with
  | ctx_empty => λ _, sub_empty
  | ctx_snoc Γ A => λ t, ctx_unpack Γ (π₁ t) ▻Sub π₂ t
  end t.

Notation "'⌞' t '⌟[' Γ ']'" := (ctx_unpack Γ t) : stlc_sub_scope.

(** Packing respects pointwise beta/eta equality of assignments. *)

(** 打包保持赋值的逐点 βη 相等。 *)

Global Instance ctx_pack_proper@{b e +} {B : Type@{b}} {Γ Δ : Ctx B}
  : Proper (SubTmEq@{b e _} ==> TmEq@{b e _}) (@ctx_pack B Γ Δ).
Proof.
  induction Γ as [|Γ IH A]; intros σ τ H; cbn.
  - apply tm_eq_refl.
  - apply tm_eq_pair; [apply IH | apply H]. intros U x. apply H.
Defined.

(** Every projection respects beta/eta equality of the packed term. *)

(** 每个拆包投影都保持所打包项的 βη 相等。 *)

Global Instance ctx_unpack_proper@{b e +} {B : Type@{b}}
    (Γ : Ctx B) {Δ : Ctx B}
  : Proper (TmEq@{b e _} ==> SubTmEq@{b e _}) (@ctx_unpack B Γ Δ).
Proof.
  induction Γ as [|Γ IH A]; intros t u H; cbn.
  - intros U x. destruct x.
  - apply sub_extend_tm_proper.
    + apply IH. now apply tm_eq_fst.
    + now apply tm_eq_snd.
Defined.

(** Packing commutes structurally with precomposition of assignments. *)

(** 打包与赋值的预合成在原始结构意义下交换。 *)

Lemma ctx_pack_subst {B : Type} {Γ Δ Θ : Ctx B}
    (σ : Sub Δ Γ) (τ : Sub Θ Δ)
  : ⌜σ⌝[τ] = ⌜σ ∘Sub τ⌝.
Proof.
  induction Γ as [|Γ IH A]; cbn; [reflexivity |].
  f_equal. apply IH.
Qed.

(** Unpacking commutes pointwise with substitution of its product term. *)

(** 拆包与积类型项的替换逐点交换。 *)

Lemma ctx_unpack_subst {B : Type} (Γ : Ctx B) {Δ Θ : Ctx B}
    (t : Tm Δ ⟦Γ⟧Ty) (σ : Sub Θ Δ)
  : (⌞t⌟[Γ]) ∘Sub σ ≈Sub ⌞t[σ]⌟[Γ].
Proof.
  induction Γ as [|Γ IH A]; intros U x; [destruct x |].
  destruct x as [x | x]; cbn; [apply IH | destruct x; reflexivity].
Qed.

(** Unpacking a packed assignment recovers every component, by product beta. *)

(** 由积 β 方程，拆包打包后的赋值恢复每个分量。 *)

Definition ctx_pack_β@{b e +} {B : Type@{b}} {Γ Δ : Ctx B}
    (σ : Sub Δ Γ)
  : SubTmEq@{b e _} (⌞⌜σ⌝⌟[Γ]) σ.
Proof.
  induction Γ as [|Γ IH A]; cbn.
  - intros U x. destruct x.
  - transitivity ((λ U x, σ U (var_succ x)) ▻Sub σ A var_zero).
    + apply sub_extend_tm_proper.
      * transitivity (ctx_unpack Γ (ctx_pack (λ U x, σ U (var_succ x)))).
        -- apply ctx_unpack_proper. apply tm_eq_product_β1.
        -- apply IH.
      * apply tm_eq_product_β2.
    + apply sub_tm_eq_of_eq. apply sub_extend_η.
Defined.

(** Repacking all projections recovers the product term, using unit/product eta. *)

(** 使用单位与积 η 方程，将所有投影重新打包后恢复原积类型项。 *)

Definition ctx_pack_η@{b e +} {B : Type@{b}} (Γ : Ctx B) {Δ : Ctx B}
    (t : Tm Δ ⟦Γ⟧Ty)
  : TmEq@{b e _} (⌜⌞t⌟[Γ]⌝) t.
Proof.
  induction Γ as [|Γ IH A]; cbn.
  - apply tm_eq_sym. apply tm_eq_unit_η.
  - transitivity (⟨π₁ t, π₂ t⟩).
    + apply tm_eq_pair; [apply IH | apply tm_eq_refl].
    + apply tm_eq_product_η.
Defined.

(** Packing as a respectful map from assignment sets to term sets. *)

(** 将打包表示为赋值广集到项广集的保相等映射。 *)

Program Definition ctx_pack_resp@{b e +} {B : Type@{b}} (Γ Δ : Ctx B)
  : SubS@{b e} Δ Γ →r TmS@{b e} Δ ⟦Γ⟧Ty
  :=
  {|func := ctx_pack
  |}.

(** Unpacking as the inverse respectful map. *)

(** 将拆包表示为反向的保相等映射。 *)

Program Definition ctx_unpack_resp@{b e +} {B : Type@{b}} (Γ Δ : Ctx B)
  : TmS@{b e} Δ ⟦Γ⟧Ty →r SubS@{b e} Δ Γ
  :=
  {|func := ctx_unpack Γ
  |}.

(** Pack the identity environment into the single variable of its product type. *)

(** 将恒等环境打包，赋给其积类型上下文中的单个变量。 *)

Definition ctx_pack_sub {B : Type} (Γ : Ctx B)
  : Sub Γ (ctx_empty ▻ ⟦Γ⟧Ty)
  := sub_empty ▻Sub ctx_pack (Γ := Γ) sub_id.

(** Unpack the single product variable into the original context. *)

(** 将单个积类型变量拆包到原上下文。 *)

Definition ctx_unpack_sub {B : Type} (Γ : Ctx B)
  : Sub (ctx_empty ▻ ⟦Γ⟧Ty) Γ
  := ctx_unpack Γ (# var_zero).

(** A context and the singleton context of its product type are isomorphic.
    The inverse substitutions remain computational; neither object equality
    nor equality of assignment functions is needed. *)

(** 上下文与其积类型的单变量上下文同构；互逆替换保持可计算，不要求对象相等
    或赋值函数相等。 *)

Definition ctx_pack_iso@{b e l +} {B : Type@{b}} (Γ : Ctx B)
  : Γ ≅[CtxCat@{b e l} B] (ctx_empty ▻ ⟦Γ⟧Ty).
Proof.
  exists (ctx_pack_sub Γ), (ctx_unpack_sub Γ).
  split; unfold is_linv_of, is_rinv_of.
  - transitivity (ctx_unpack Γ (ctx_pack (Γ := Γ) sub_id)).
    + apply sub_tm_eq_of_eq@{b e b b}.
      exact (ctx_unpack_subst Γ (# var_zero) (ctx_pack_sub Γ)).
    + apply ctx_pack_β.
  - intros A [x | x]; [destruct x | destruct x].
    cbn. rewrite ctx_pack_subst. apply ctx_pack_η.
Defined.
