From Cats.STLC Require Import NormalEta.

(** * Long Normal Form Interface Regressions *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** ** Eta Correctness above the Syntax Level

    Fix a signature, context, type and neutral term with [b < e].
    Check that eta correctness accepts the larger evidence universe. *)

Section LargerEvidence.
Universes b e.
Constraint b < e.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B) (n : Ne Γ A).

(** Eta correctness accepts evidence strictly above the syntax level. *)

Definition separated_eta_correctness
  : TmEq@{b e _} (embed_ne n) (embed_nf (eta_expand_ne n))
  := eta_expand_ne_sound A n.

End LargerEvidence.

(** ** Eta Correctness at the Syntax Level

    Keep the same syntactic inputs but choose evidence at [b] itself.
    Check that eta correctness needs no strict universe increase. *)

Section SameLevel.
Universe b.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B) (n : Ne Γ A).

(** No strict inequality of evidence levels is required. *)

Definition same_level_eta_correctness
  : TmEq@{b b _} (embed_ne n) (embed_nf (eta_expand_ne n))
  := eta_expand_ne_sound A n.

End SameLevel.

(** ** Executable Eta Expansions

    Fix arbitrary base labels [p] and [q] and a context [Γ]. Check
    type-directed expansion and its behavior under binders and renaming. *)

Section Computations.
Context {B : Type} (p q : B) (Γ : Ctx B).

(** Function expansion binds a fresh base argument and weakens its head. *)

Example base_function_expansion (f : Ne Γ (ty_base p ⇒ ty_base q))
  : eta_expand_ne f = nf_lam
      (nf_base (ne_app (f⟨wkRen⟩ne) (nf_base (ne_var var_zero)))).
Proof. reflexivity. Qed.

(** A product-domain argument is a long pair, including canonical unit. *)

Example product_domain_expansion
    (f : Ne Γ ((ty_base p × ⊤) ⇒ ty_base q))
  : eta_expand_ne f = nf_lam
      (nf_base (ne_app (f⟨wkRen⟩ne)
        (nf_pair (nf_base (ne_fst (ne_var var_zero))) nf_unit))).
Proof. reflexivity. Qed.

(** A function-domain argument itself introduces a second binder; the
    first argument variable is weakened under that binder. *)

Example function_domain_expansion
    (f : Ne Γ ((ty_base p ⇒ ty_base q) ⇒ ty_base q))
  : eta_expand_ne f = nf_lam
      (nf_base (ne_app (f⟨wkRen⟩ne)
        (nf_lam (nf_base
          (ne_app (ne_var (var_succ var_zero))
            (nf_base (ne_var var_zero))))))).
Proof. reflexivity. Qed.

(** Unit eta erases blocked syntax, while product eta keeps its projections. *)

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

Example expansion_after_identification
  : eta_expand_ne
      ((ne_var (var_succ var_zero))⟨merge_base_variables⟩ne) =
      (eta_expand_ne (ne_var (var_succ var_zero)))
        ⟨merge_base_variables⟩nf.
Proof. apply eta_expand_ne_rename. Qed.

End Computations.
