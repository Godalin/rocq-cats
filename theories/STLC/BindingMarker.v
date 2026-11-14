From Cats.STLC Require Export VariableProduct.

(** * Coherent Elimination of Binding Markers

    A marker can change the displayed type of a term. Projection and
    application commute with that change after reading the appropriate
    component markers. These are equations of raw terms, proved by
    eliminating a generalized marker; no marker witness is erased. *)

(** * 绑定标记的相干消去

    标记可以改变项所显示的类型。读取适当的分量标记后，投影和应用与这一
    改变交换。这些是原始项的等式，通过消去泛化的标记证明，不擦除标记见证。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Terms at Aligned Types

    Fix arbitrary labels. Only the indexed marker, not a decision about
    labels or equality proofs, supplies the alignment. *)

(** ** 对齐类型处的项

    固定任意标签。对齐仅由带索引标记给出，不依赖标签判定或相等证明判定。 *)

Section MarkerTerms.
Context {B : Type}.

(** Transport a term along the retained binding marker. *)

(** 沿保留的绑定标记运输项。 *)

Definition marker_tm {Γ : Ctx B} {A U : Ty B}
    (x : NewVar A U) (t : Tm Γ A)
  : Tm Γ U.
Proof. destruct x. exact t. Defined.

(** A possible domain marker, read at a declared function type. *)

(** 在声明的函数类型处读取可能的定义域标记。 *)

Definition ArrowMarkerDomain (A T : Ty B)
  : Set
  := match T with ty_arr D _ => NewVar A D | _ => Empty_set end.

(** The codomain marker is retained independently. *)

(** 独立保留陪域标记。 *)

Definition ArrowMarkerCodomain (U T : Ty B)
  : Set
  := match T with ty_arr _ V => NewVar U V | _ => Empty_set end.

(** Read the aligned domain without comparing function annotations. *)

(** 读取对齐的定义域，不比较函数类型注解。 *)

Definition arrow_marker_domain {A U T : Ty B} (x : NewVar (A ⇒ U) T)
  : ArrowMarkerDomain A T.
Proof. destruct x. exact new_var. Defined.

(** Read the aligned codomain in the same way. *)

(** 以相同方式读取对齐的陪域。 *)

Definition arrow_marker_codomain {A U T : Ty B} (x : NewVar (A ⇒ U) T)
  : ArrowMarkerCodomain U T.
Proof. destruct x. exact new_var. Defined.

(** Left projection retains only the left component marker. Generalizing
    the declared type makes this equation independent of UIP. *)

(** 左投影仅保留左分量标记。泛化声明类型使此等式独立于 UIP。 *)

Definition marker_tm_fst {Γ : Ctx B} {A U T : Ty B}
    (x : NewVar (A × U) T)
  : match T as T' return NewVar (A × U) T' → Type with
    | ty_prod D V => λ x, ∀ t : Tm Γ (D × V),
        π₁ (marker_tm (new_var_inv x) t) =
        marker_tm (new_var_inv (product_marker_left x)) (π₁ t)
    | _ => λ _, unit
    end x.
Proof. destruct x. intros t. reflexivity. Defined.

(** Right projection obeys the corresponding coherent equation. *)

(** 右投影满足对应的相干等式。 *)

Definition marker_tm_snd {Γ : Ctx B} {A U T : Ty B}
    (x : NewVar (A × U) T)
  : match T as T' return NewVar (A × U) T' → Type with
    | ty_prod D V => λ x, ∀ t : Tm Γ (D × V),
        π₂ (marker_tm (new_var_inv x) t) =
        marker_tm (new_var_inv (product_marker_right x)) (π₂ t)
    | _ => λ _, unit
    end x.
Proof. destruct x. intros t. reflexivity. Defined.

(** Application moves the domain alignment into the argument and keeps
    only the codomain alignment at the result. Arguments stay raw. *)

(** 应用将定义域对齐移入实参，只在结果处保留陪域对齐。实参仍是原始项。 *)

Definition marker_tm_app {Γ : Ctx B} {A U T : Ty B}
    (x : NewVar (A ⇒ U) T)
  : match T as T' return NewVar (A ⇒ U) T' → Type with
    | ty_arr D V => λ x, ∀ (f : Tm Γ (D ⇒ V)) (a : Tm Γ A),
        marker_tm (new_var_inv x) f · a =
        marker_tm (new_var_inv (arrow_marker_codomain x))
          (f · marker_tm (arrow_marker_domain x) a)
    | _ => λ _, unit
    end x.
Proof. destruct x. intros f a. reflexivity. Defined.

End MarkerTerms.
