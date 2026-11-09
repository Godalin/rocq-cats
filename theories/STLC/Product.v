From Cats Require Export STLC.Category.
From Cats Require Export STLC.Context.
From Cats Require Import Cat.Product.Core.

(** * Products of Syntactic Contexts

    Concatenation represents pairs of simultaneous substitutions. In
    particular, extension by one type is product with its singleton context.
    The universal mediator computes by pairing the variable assignments. *)

(** * 语法上下文的积

    连接表示成对的同时替换；特别地，扩张一个类型就是与其单变量上下文取积。
    泛中介按变量赋值配对直接计算。 *)

(** ** From tuple operations to a universal product

    Given [σ : Sub Θ Γ] and [τ : Sub Θ Δ], their pairing fills the
    concatenated context from [Θ]. The structural projection laws give
    the two beta equations. For uniqueness, restrict a proposed mediator
    to each block, replace those restrictions using the given hom
    equalities, and reconstruct the whole assignment by the structural
    eta law. This also explains why pairing must be respectful.

    Thus a syntactic product is chosen context concatenation, not the
    product-type constructor applied to contexts. Extension by [A] is
    concatenation with its singleton context. The universal property
    connects this concrete representation to the general category theory
    of products, which later supplies product maps and transport. *)

(** ** 从元组操作得到泛积

    给定 [σ : Sub Θ Γ] 与 [τ : Sub Θ Δ]，配对用 [Θ] 填充连接上下文。
    结构投影律给出两条 β 方程。证明唯一性时，把候选中介分别限制到两块，
    用给定的 Hom 相等替换这些限制，再由结构 η 律重建整个赋值。
    这也解释了为什么配对必须保持相等。

    因此，语法积选取的是上下文连接，不是把积类型构造器作用于上下文。
    扩张类型 [A] 就是连接其单变量上下文。泛性质把这个具体表示接到一般的
    范畴积理论，后者再提供积映射与运输。 *)

Local Open Scope stlc_ctx_scope.
(** ** Reading the uniqueness argument

    Suppose a candidate arrow into [Γ ++Ctx Δ] has the requested left and
    right projections. Reconstruction expresses that candidate as the
    pairing of its projections. Substituting the two given projection
    equations then identifies it with the chosen pairing. This is why
    projection beta equations alone would be insufficient: reconstruction
    supplies the eta step needed for uniqueness. All equations compare
    assignments at each variable, which is precisely the chosen hom equality. *)

(** ** 阅读唯一性论证

    假设指向 [Γ ++Ctx Δ] 的候选箭头具有所要求的左右投影。重建律把候选写成
    自身投影的配对，再代入两条给定投影方程，就得到它与选定配对相等。
    因此，仅有投影 β 方程还不够：重建律提供唯一性所需的 η 步骤。全部方程
    都在每个变量处比较赋值，恰好就是选定的 Hom 相等。 *)

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
