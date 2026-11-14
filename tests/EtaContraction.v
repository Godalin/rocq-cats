From Cats.STLC Require Import EtaNormalization.
From Cats.Set.Relation Require Import Compatible.

(** * Eta-Contraction Interface Regressions

    Check that the numerical measure does not collapse carrier, edge and
    tree universes. Exercise contextual contraction under a binder, its
    transparent reversal, and the beta/eta coproduct's branch tags. *)

(** * η 收缩接口回归

    检查数值度量不合并载体、边和树的宇宙。检验绑定下的上下文收缩、其透明
    反向变换，以及 βη 余积的分支标签。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Measures with Large Edges

    Fix [a < e < s]. A small natural-number measure can construct large
    trees without resizing the relation's edge witnesses. *)

(** ** 大边的度量

    固定 [a < e < s]。小的自然数度量可以构造大树，无须缩小关系边的见证。 *)

Section LargeEdges.
Universes a e s.
Constraint a < e, e < s.
Context {X : Type@{a}} (R : X → X → Type@{e}) (m : X → nat).
Context (decrease : ∀ x y, R x y → m y < m x).

(** The return type retains the requested large tree universe. *)

(** 返回类型保留所要求的大树宇宙。 *)

Definition large_edge_measure (x : X)
  : SN@{a e s} R x
  := sn_measure m decrease x.

End LargeEdges.

(** ** Measures with Large Carriers

    Fix [e < a < s] to check the opposite order of carrier and edge sizes. *)

(** ** 大载体的度量

    固定 [e < a < s]，检查载体与边大小的相反次序。 *)

Section LargeCarriers.
Universes e a s.
Constraint e < a, a < s.
Context {X : Type@{a}} (R : X → X → Type@{e}) (m : X → nat).
Context (decrease : ∀ x y, R x y → m y < m x).

(** Large carriers need not force the edge universe to grow. *)

(** 大载体无须使边的宇宙增大。 *)

Definition large_carrier_measure (x : X)
  : SN@{a e s} R x
  := sn_measure m decrease x.

End LargeCarriers.

(** ** Trees below Classification

    Fix [b < e < s < l]. Check all-term eta SN and preservation by
    substitution and renaming, with equation evidence still at [e]. *)

(** ** 低于分类界的树

    固定 [b < e < s < l]。检查所有项的 η 强归一化及替换、重命名保持性，
    其中等式证据仍位于 [e]。 *)

Section SmallTrees.
Universes b e s l.
Constraint b < e, e < s, s < l.
Context {B : Type@{b}} {Γ Δ : Ctx B} {A : Ty B}.

(** Eta trees may be smaller than relation classification. *)

(** η 树可以小于关系分类界。 *)

Definition small_eta_tree (t : Tm Γ A)
  : SN@{b e s} (@EtaContractStep@{b e l} B Γ A) t
  := eta_strong_normalization t.

(** Arbitrary simultaneous substitutions preserve the chosen step. *)

(** 任意同时替换保持选定的步骤。 *)

Definition separated_eta_subst {t u : Tm Γ A}
    (h : EtaContractStep@{b e l} t u) (σ : Sub Δ Γ)
  : EtaContractStep@{b e l} t[σ] u[σ]
  := eta_contract_subst h Δ σ.

(** Renaming does not require an injective variable map. *)

(** 重命名不要求变量映射为单射。 *)

Definition separated_eta_rename {t u : Tm Γ A}
    (h : EtaContractStep@{b e l} t u) (ρ : Ren Δ Γ)
  : EtaContractStep@{b e l} t⟨ρ⟩ u⟨ρ⟩
  := eta_contract_rename h Δ ρ.

(** Both coproduct branches have equation witnesses at the edge level. *)

(** 两个余积分支都在边的层级上具有等式见证。 *)

Definition separated_beta_eta_sound {t u : Tm Γ A}
    (h : BetaEtaContractStep@{b e l} t u)
  : TmEq@{b e b} t u
  := beta_eta_contract_to_tm_eq h.

(** The coproduct's substitution map retains its independent edge size. *)

(** 余积的替换映射保留独立的边大小。 *)

Definition separated_beta_eta_subst {t u : Tm Γ A}
    (h : BetaEtaContractStep@{b e l} t u) (σ : Sub Δ Γ)
  : BetaEtaContractStep@{b e l} t[σ] u[σ]
  := beta_eta_contract_subst h Δ σ.

(** The coproduct's renaming map has the same universe boundary. *)

(** 余积的重命名映射具有相同的宇宙边界。 *)

Definition separated_beta_eta_rename {t u : Tm Γ A}
    (h : BetaEtaContractStep@{b e l} t u) (ρ : Ren Δ Γ)
  : BetaEtaContractStep@{b e l} t⟨ρ⟩ u⟨ρ⟩
  := beta_eta_contract_rename h Δ ρ.

End SmallTrees.

(** ** Trees above Classification

    Fix [b < e < l < s]; classification must not bound the SN tree. *)

(** ** 高于分类界的树

    固定 [b < e < l < s]；分类界不应限制 SN 树的大小。 *)

Section LargeTrees.
Universes b e l s.
Constraint b < e, e < l, l < s.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The same theorem constructs a tree above the classification bound. *)

(** 同一定理构造高于分类界的树。 *)

Definition large_eta_tree (t : Tm Γ A)
  : SN@{b e s} (@EtaContractStep@{b e l} B Γ A) t
  := eta_strong_normalization t.

End LargeTrees.

(** ** Equal Computational Levels

    Fix a common syntax, edge and tree bound [b], with only [b < l]. *)

(** ** 相等的计算层级

    固定语法、边和树的共同界 [b]，只要求 [b < l]。 *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Strict separation of computational universes is optional. *)

(** 计算宇宙的严格分离是可选的。 *)

Definition equal_eta_tree (t : Tm Γ A)
  : SN@{b b b} (@EtaContractStep@{b b l} B Γ A) t
  := eta_strong_normalization t.

End EqualLevels.

(** ** Transparent Contexts and Branches

    Use an empty base signature. Check actual node counts, contraction
    beneath a lambda and observable branch tags after witness maps. *)

(** ** 透明上下文与分支

    使用空基签名。检查实际节点数、λ 下的收缩，以及见证映射后可观察的分支
    标签。 *)

Section Computations.

(** A free function whose eta expansion contains four nodes. *)

(** 一个自由函数，其 η 展开含四个节点。 *)

Definition free_function
  : Tm ((@ctx_empty Empty_set) ▻ (⊤ ⇒ ⊤)) (⊤ ⇒ ⊤)
  := # var_zero.

(** The weakening in function eta does not add syntax nodes. *)

(** 函数 η 中的弱化不增加语法节点。 *)

Example function_eta_size
  : tm_size (ƛ (free_function⟨wkRen⟩ · (# var_zero))) = 4
  := eq_refl.

(** A free product, used twice by its eta expansion. *)

(** 一个自由积项，在其 η 展开中使用两次。 *)

Definition free_product
  : Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤)) (⊤ × ⊤)
  := # var_zero.

(** Pairing and the two projections contribute three additional nodes. *)

(** 配对与两个投影贡献三个额外节点。 *)

Example product_eta_size
  : tm_size (⟨π₁ free_product, π₂ free_product⟩) = 5
  := eq_refl.

(** This witness contracts the weakened product under a fresh binder. *)

(** 此见证在新鲜绑定下收缩弱化后的积项。 *)

Definition binder_eta
  : EtaContractStep
      (ƛ (⟨π₁ free_product⟨ren_weaken (A := ⊤)⟩,
        π₂ free_product⟨wkRen⟩⟩)) (ƛ free_product⟨wkRen⟩)
  := eta_contract_lift op_lam
      (eta_contract_root (root_eta_contract_product free_product⟨wkRen⟩)).

(** Count enclosing operations to observe the reversal fold. *)

(** 计算外层操作数，以观察反向折叠。 *)

Fixpoint context_depth {I : Type} {X : I → Type}
    {K : ContextSystem X} {R : RelationFamily X}
    {i : I} {x y : X i} (h : ContextClosure K R i x y)
  : nat
  := match h with
  | context_step _ => 0
  | context_lift _ p => S (context_depth p)
  end.

(** Reversal retains the one surrounding lambda, by computation. *)

(** 反向变换通过计算保留唯一的外层 λ。 *)

Example reversed_binder_depth
  : context_depth (eta_contract_context binder_eta) = 1
  := eq_refl.

(** Reversing again still retains that surrounding operation. *)

(** 再次反向仍保留该外层操作。 *)

Example restored_binder_depth
  : context_depth (context_eta_contract (eta_contract_context binder_eta)) = 1
  := eq_refl.

(** The subtree after this contextual contraction remains accessible. *)

(** 该上下文收缩之后的子树仍可达。 *)

Example binder_eta_subtree
  : SN EtaContractStep (ƛ free_product⟨ren_weaken (A := ⊤)⟩)
  := sn_step (eta_strong_normalization _) binder_eta.

(** Observe the coproduct tag without inspecting its stored proof. *)

(** 观察余积标签，无须查看其存储的证明。 *)

Definition is_beta_branch {B : Type} {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : BetaEtaContractStep t u)
  : bool
  := match h with inl _ => true | inr _ => false end.

(** Substitution keeps the eta alternative even for a binder step. *)

(** 即使是绑定下步骤，替换也保持 η 备选。 *)

Example subst_eta_tag
  : is_beta_branch (beta_eta_contract_subst (inr binder_eta) _ idSub) = false
  := eq_refl.

(** Renaming likewise keeps the beta alternative. *)

(** 重命名同样保持 β 备选。 *)

Example rename_beta_tag
  : is_beta_branch (beta_eta_contract_rename
      (inl (context_step_root _
        (root_beta_function (# var_zero)
          (⋆ : Tm (@ctx_empty Empty_set) ⊤)))) _ idRen) = true
  := eq_refl.

End Computations.
