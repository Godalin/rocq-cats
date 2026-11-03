From Cats Require Export STLC.Category.
From Cats Require Export STLC.Context.
From Cats Require Import Cat.Product.

(** * Products of Syntactic Contexts

    Concatenation represents pairs of simultaneous substitutions. In
    particular, extension by one type is product with its singleton context.
    The universal mediator computes by pairing the variable assignments. *)

(** * 语法上下文的积

    连接表示成对的同时替换；特别地，扩张一个类型就是与其单变量上下文取积。
    泛中介按变量赋值配对直接计算。 *)

Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_sub_scope.

(** The full product property, with uniqueness in pointwise beta/eta equality.
    Structural splitting supplies eta; respectful pairing changes its parts. *)

(** 完整的积泛性质，唯一性使用逐点 βη 相等；结构分解给出 η，保相等配对允许
    更换两个分量。 *)

Definition ctx_append_product@{b e l +} {B : Type@{b}} (Γ Δ : Ctx B)
  : @is_product (CtxCat@{b e l} B) Γ Δ (Γ ++Ctx Δ)
      (RenSub (ren_append_l Γ Δ)) (RenSub (ren_append_r Γ Δ)).
Proof.
  intros Θ σ τ. exists (⟨σ, τ⟩Sub).
  refine {|this := _
         ; that := _
         |}.
  - split; intros A x; cbn; apply tm_eq_of_eq.
    + apply sub_append_β1.
    + apply sub_append_β2.
  - intros υ [H1 H2]. cbn in H1, H2.
    transitivity (⟨λ A x, υ A (ren_append_l Γ Δ A x),
                    λ A x, υ A (ren_append_r Γ Δ A x)⟩Sub).
    + apply sub_tm_eq_of_eq@{b e b b}. symmetry. apply sub_append_η.
    + apply sub_append_tm_proper; assumption.
Defined.

(** Select concatenation and its two variable projections as binary products.
    No chosen structures are installed globally by importing this module. *)

(** 选定连接及其两个变量投影作为二元积；导入本模块不会全局启用选定结构。 *)

Program Definition CtxCat_HasProduct@{b e l +} (B : Type@{b})
  : HasProduct (CtxCat@{b e l} B)
  :=
  {|Prod := CtxAppend
  ; π1 Γ Δ := RenSub (ren_append_l Γ Δ)
  ; π2 Γ Δ := RenSub (ren_append_r Γ Δ)
  ; product_universal Γ Δ := ctx_append_product Γ Δ
  |}.
