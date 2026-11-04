From Cats.Set Require Import
  Morphism.

(** * Raw Indexed Products of Sets *)

(** * 集合的原始指标积 *)

(** Pointwise fiber equality on dependent functions; the index type has no
    additional specified relation or coherence requirement. *)

(** 依赖函数的逐点纤维相等；索引类型没有额外指定关系或相干性要求。 *)

Definition PiEq {I : Type} {D : I → SetC} (f g : ∀ i, D i)
  : Type
  := ∀ i, f i ≈S g i.

Infix "≈ΠS" := PiEq (at level 50) : set_scope.

(** The fiber equivalences give pointwise function equivalence. *)

(** 纤维等价给出逐点函数等价。 *)

Global Instance PiEq_Equivalence {I : Type} {D : I → SetC}
  : Equivalence (@PiEq I D).
Proof.
  split.
  - intros f i. reflexivity.
  - intros f g H i. symmetry. apply H.
  - intros f g h H K i. transitivity (g i); [apply H | apply K].
Defined.

(** The indexed product compares functions pointwise, without native
    function equality or function extensionality. *)

(** 指标积逐点比较函数，不使用原生函数相等或函数外延性。 *)

Program Canonical PiS (I : Type) (D : I → SetC)
  : SetC
  :=
  {|carrier := ∀ i, D i
  ; carrier_equiv := PiEq
  |}.

Notation "'ΠS[' D ']'" := (PiS _ D) : set_scope.

(** Evaluate a dependent function at one index. *)

(** 在一个索引处计算依赖函数。 *)

Program Definition pi_proj_resp {I : Type} (D : I → SetC) (i : I)
  : ΠS[D] →r D i
  :=
  {|func f := f i
  |}.
Next Obligation. intros f g H. exact (H i). Defined.

(** Assemble a family of respectful component maps pointwise. *)

(** 逐点组装保相等分量映射族。 *)

Program Definition pi_pair_resp {I : Type} {D : I → SetC} {X : SetC}
    (κ : ∀ i, X →r D i)
  : X →r ΠS[D]
  :=
  {|func x i := κ i x
  |}.
Next Obligation. intros x y H i. apply func_proper. exact H. Defined.
