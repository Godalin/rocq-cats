From Cats.STLC Require Import NormalEta.

(** * Long Normal Form Interface Regressions *)

(** * 长正规形接口回归检查 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

Section LargerEvidence.
Universes b e.
Constraint b < e.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B) (n : Ne Γ A).

(** Eta correctness accepts evidence strictly above the syntax level. *)

(** η 正确性允许见证严格高于语法层级。 *)

Definition separated_eta_correctness
  : TmEq@{b e _} (embed_ne n) (embed_nf (eta_expand_ne n))
  := eta_expand_ne_sound A n.

End LargerEvidence.

Section SameLevel.
Universe b.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B) (n : Ne Γ A).

(** No strict inequality of evidence levels is required. *)

(** 见证层级也无须严格高于语法。 *)

Definition same_level_eta_correctness
  : TmEq@{b b _} (embed_ne n) (embed_nf (eta_expand_ne n))
  := eta_expand_ne_sound A n.

End SameLevel.

Section Computations.
Context {B : Type} (p q : B) (Γ : Ctx B).

(** Function expansion binds a fresh base argument and weakens its head. *)

(** 函数展开绑定新基类型实参，并弱化其头部。 *)

Example base_function_expansion (f : Ne Γ (ty_base p ⇒ ty_base q))
  : eta_expand_ne f = nf_lam
      (nf_base (ne_app (f⟨wkRen⟩ne) (nf_base (ne_var var_zero)))).
Proof. reflexivity. Qed.

(** A product-domain argument is a long pair, including canonical unit. *)

(** 积定义域的实参为长配对，其中单位分量取规范单位项。 *)

Example product_domain_expansion
    (f : Ne Γ ((ty_base p × ⊤) ⇒ ty_base q))
  : eta_expand_ne f = nf_lam
      (nf_base (ne_app (f⟨wkRen⟩ne)
        (nf_pair (nf_base (ne_fst (ne_var var_zero))) nf_unit))).
Proof. reflexivity. Qed.

(** A function-domain argument itself introduces a second binder; the
    first argument variable is weakened under that binder. *)

(** 函数定义域的实参自身引入第二个绑定；第一个实参变量在此绑定下弱化。 *)

Example function_domain_expansion
    (f : Ne Γ ((ty_base p ⇒ ty_base q) ⇒ ty_base q))
  : eta_expand_ne f = nf_lam
      (nf_base (ne_app (f⟨wkRen⟩ne)
        (nf_lam (nf_base
          (ne_app (ne_var (var_succ var_zero))
            (nf_base (ne_var var_zero))))))).
Proof. reflexivity. Qed.

(** Unit eta erases blocked syntax, while product eta keeps its projections. *)

(** 单位 η 忘却被阻塞语法，积 η 则保留两个投影。 *)

Example canonical_unit_expansion (n : Ne Γ ⊤)
  : eta_expand_ne n = nf_unit.
Proof. reflexivity. Qed.

Example product_expansion (n : Ne Γ (ty_base p × ty_base q))
  : eta_expand_ne n =
      nf_pair (nf_base (ne_fst n)) (nf_base (ne_snd n)).
Proof. reflexivity. Qed.

(** Renaming may duplicate positions: these are arbitrary renamings, not
    just order-preserving context embeddings. The bound variable remains
    newest while both older variables are identified. *)

(** 重命名允许复制位置：这里使用任意重命名，不只保序上下文嵌入。绑定变量
    保持最新位置，两个较旧变量则被识别。 *)

Definition merge_base_variables
  : Ren (Γ ▻ ty_base p) (Γ ▻ ty_base p ▻ ty_base p)
  := λ A x, match x with
     | inl x => x
     | inr x => inr x
     end.

Example rename_under_normal_binder
  : (nf_lam (nf_pair
      (nf_base (ne_var (var_succ (var_succ var_zero))))
      (nf_base (ne_var (var_succ var_zero))))
        : Nf (Γ ▻ ty_base p ▻ ty_base p)
            (ty_base q ⇒ (ty_base p × ty_base p)))
      ⟨merge_base_variables⟩nf =
      nf_lam (nf_pair
        (nf_base (ne_var (var_succ var_zero)))
        (nf_base (ne_var (var_succ var_zero)))).
Proof. reflexivity. Qed.

(** Expansion after variable identification agrees strictly with renaming
    the expanded form; arbitrary label equality is never decided. *)

(** 识别变量后再展开，与重命名已展开的正规形严格相同，从未判定任意标签相等。 *)

Example expansion_after_identification
  : eta_expand_ne
      ((ne_var (var_succ var_zero))⟨merge_base_variables⟩ne) =
      (eta_expand_ne (ne_var (var_succ var_zero)))
        ⟨merge_base_variables⟩nf.
Proof. apply eta_expand_ne_rename. Qed.

End Computations.
