From Cats.STLC Require Import EtaCompletion.
From CatsTests Require Import STLCConfluence.

(** * Completed Beta/Eta Interfaces and Blocked-Head Computations

    The confluence interfaces below have no product-root premise. Check
    both strict path/classification orders and equal computational bounds.
    Endpoint computations retain abstract raw arguments and type labels. *)

(** * 已完成的 βη 接口与阻塞头部计算

    以下合流接口没有积根前提。检查路径与分类的两种严格次序，以及相等的
    计算界。端点计算保留抽象的原始实参与类型标签。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Recovery under a Large Signature

    Fix [Set < b]. Joint recovery must not make the signature small or
    resize stored raw arguments and their markers. *)

(** ** 大签名下的恢复

    固定 [Set < b]。联合恢复不能迫使签名变小，也不能重设存储实参及标记
    的大小。 *)

Section LargeSignature.
Universe b.
Constraint Set < b.
Context {B : Type@{b}} {Γ Δ : Ctx B} {D A U : Ty B}.

(** Two projected spine codes recover the whole original code. *)

(** 两个投影消去链编码恢复整个原编码。 *)

Definition large_signature_spine_recovery
    (p q : AlignedSpine Γ D (A × U))
    (left : spine_fst p = spine_fst q)
    (right : spine_snd p = spine_snd q)
  : p = q
  := spine_projections_injective Γ D p q left right.

(** Position tags remain part of recovery at the same signature bound. *)

(** 同一签名界处的恢复仍保持位置标签。 *)

Definition large_signature_position_recovery
    (p q : VariableSpine Γ Δ (A × U))
    (left : variable_spine_fst Γ Δ A U p = variable_spine_fst Γ Δ A U q)
    (right : variable_spine_snd Γ Δ A U p = variable_spine_snd Γ Δ A U q)
  : p = q
  := variable_spine_projections_injective Γ Δ p q left right.

End LargeSignature.

(** ** Paths below Trees and Classification

    Fix [b < e < p < s < l]. The constructed root diagrams and global
    theorem need no supplied diagram, despite their independent bounds. *)

(** ** 路径低于树与分类

    固定 [b < e < p < s < l]。已构造的根图式与全局定理无须提供任何图式
    输入，同时保持各自独立的界。 *)

Section SmallPaths.
Universes b e p s l.
Constraint b < e, e < p, p < s, s < l.
Context {B : Type@{b}}.

(** The original product-root interface is now populated. *)

(** 原积根接口现在已有构造。 *)

Definition small_path_completed_roots
  : @is_eta_product_root_joinable@{b e p l} B
  := eta_product_roots.

(** Eta/eta diagrams may have mixed residual paths. *)

(** η／η 图式允许混合剩余路径。 *)

Definition small_path_eta_diagrams (Γ : Ctx B) (A : Ty B)
  : is_locally_joinable@{b e e e p _}
      (@EtaContractStep@{b e l} B Γ A) (@EtaContractStep@{b e l} B Γ A)
      (@BetaEtaContractStep@{b e l} B Γ A)
  := eta_eta_joinable Γ A.

(** Local confluence has no remaining assumption. *)

(** 局部合流不再有剩余假设。 *)

Definition small_path_local_confluence (Γ : Ctx B) (A : Ty B)
  : is_locally_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_locally_confluent Γ A.

(** Global confluence keeps the smaller path bound. *)

(** 全局合流保持较小的路径界。 *)

Definition small_path_completed_confluence (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent Γ A.

(** Uniqueness requires only supplied paths and irreducible endpoints. *)

(** 唯一性只要求给定路径与不可约终点。 *)

Definition small_path_completed_uniqueness
    {Γ : Ctx B} {A : Ty B} {t u v : Tm Γ A}
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t u)
    (k : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t v)
    (hu : is_irreducible BetaEtaContractStep@{b e l} u)
    (hv : is_irreducible BetaEtaContractStep@{b e l} v)
  : u = v
  := beta_eta_irreducible_unique h k hu hv.

End SmallPaths.

(** ** Paths above Trees and Classification

    Reverse the order to [b < e < s < l < p]. No implicit dependency
    should require normalization trees or classification to contain paths. *)

(** ** 路径高于树与分类

    将次序反转为 [b < e < s < l < p]。隐式依赖不能迫使归一化树或分类界
    容纳路径。 *)

Section LargePaths.
Universes b e p s l.
Constraint b < e, e < s, s < l, l < p.
Context {B : Type@{b}}.

(** Construct the same root interface in the reverse order. *)

(** 在反向次序下构造同一根接口。 *)

Definition large_path_completed_roots
  : @is_eta_product_root_joinable@{b e p l} B
  := eta_product_roots.

(** The global theorem also accepts the larger path bound. *)

(** 全局定理也接受较大的路径界。 *)

Definition large_path_completed_confluence (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent Γ A.

End LargePaths.

(** ** Equal Bounds and Transparent Blocked Endpoints

    Syntax, edge, path and tree bounds may coincide. Classification alone
    remains larger. The endpoint join must compute while raw arguments,
    contexts and component types stay abstract. *)

(** ** 相等界与透明的阻塞端点

    语法、边、路径与树界可以相等，只有分类界保持更高。原始实参、上下文及
    分量类型保持抽象时，端点汇合仍须计算。 *)

Section Computation.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A U V : Ty B}.

(** Equal computational bounds support unconditional confluence. *)

(** 相等计算界支持无条件合流。 *)

Definition equal_bound_completed_confluence
  : is_confluent@{b b b _} (@BetaEtaContractStep@{b b l} B Γ A)
  := beta_eta_confluent Γ A.

(** A blocked function keeps an unreduced identity application as argument. *)

(** 被阻塞的函数将未归约的恒等应用保留为实参。 *)

Definition blocked_argument_root_join
    (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : let t := (# var_zero) · ((ƛ (# var_zero)) · a) in
    Join@{b b b} BetaEtaContractStep@{b b l} t t
  := let t := (# var_zero) · ((ƛ (# var_zero)) · a) in
     eta_head_elimination_roots _ _ _ t t
       (root_eta_contract_product t) eq_refl eq_refl eq_refl.

(** The common target keeps that redex and both paths are empty. *)

(** 共同目标保持该可归约式，两条路径均为空。 *)

Definition blocked_argument_root_computes
    (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : let h := blocked_argument_root_join a in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) =
    ((# var_zero) · ((ƛ (# var_zero)) · a), 0, 0).
Proof. reflexivity. Defined.

(** Nested projected heads use the same zero-step endpoint operation. *)

(** 嵌套投影头部使用同一个零步端点操作。 *)

Definition nested_projection_root_join
  : let t := π₂ (π₁ (# (@var_zero B Γ ((V × (A × U)) × V)))) in
    Join@{b b b} BetaEtaContractStep@{b b l} t t
  := let t := π₂ (π₁ (# (@var_zero B Γ ((V × (A × U)) × V)))) in
     eta_head_elimination_roots _ _ _ t t
       (root_eta_contract_product t) eq_refl eq_refl eq_refl.

(** The nested raw head and both empty paths compute by reflexivity. *)

(** 嵌套原始头部及两条空路径可通过自反性计算。 *)

Definition nested_projection_root_computes
  : (projT1 nested_projection_root_join,
      path_length (fst (projT2 nested_projection_root_join)),
      path_length (snd (projT2 nested_projection_root_join))) =
    (π₂ (π₁ (# (@var_zero B Γ ((V × (A × U)) × V)))), 0, 0).
Proof. reflexivity. Defined.

(** A selected older position remains distinct from an equal declaration. *)

(** 选定的旧位置仍区别于相同类型的另一个声明。 *)

Definition older_function_root_join
    (a : Tm (Γ ▻ (V ⇒ (A × U)) ▻ (V ⇒ (A × U))) V)
  : let t := (# (var_succ var_zero)) · a in
    Join@{b b b} BetaEtaContractStep@{b b l} t t
  := let t := (# (var_succ var_zero)) · a in
     eta_head_elimination_roots _ _ _ t t
       (root_eta_contract_product t) eq_refl eq_refl eq_refl.

(** Joint recovery does not collapse the two declaration positions. *)

(** 联合恢复不合并两个声明位置。 *)

Definition older_function_root_computes
    (a : Tm (Γ ▻ (V ⇒ (A × U)) ▻ (V ⇒ (A × U))) V)
  : let h := older_function_root_join a in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) =
    ((# (var_succ var_zero)) · a, 0, 0).
Proof. reflexivity. Defined.

End Computation.
