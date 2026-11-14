From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Terminal
  DTT.CwF.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal.
From Cats Require Import
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  Instance.Set.Fam.Fixed.
From Cats Require Import
  Instance.Set.Fam.Section
  Instance.Set.Fam.SectionMap.

(** * A CwF from Type Codes and Their Decoding Family

    Types are respectful code-valued functions. Terms are coherent sections of
    the decoded family; type equality and term equality are pointwise. No
    closure under type formers is required of the chosen codes. *)

(** * 由类型代码及其解码族构造带族范畴

    类型是保相等的代码值函数，项是解码族的相干截面；类型与项按逐点相等比较。不
    要求所选代码在任何类型构造子下封闭。 *)

Section CodeFamilies.
Context {Code : SetC} (El : FamS Code).

(** Sections of decoded types form a coherent family over code-valued
    functions. *)

(** 解码类型的截面在代码值函数广集上组成相干族。 *)

Program Definition CodeTerms (Γ : SetC)
  : FamS (Γ →S Code)
  :=
  {|fam A := SectionS El[A]S
  ; transpS A B H := section_fam_map_resp El⟦H⟧Fam
  |}.
Next Obligation. intros γ. cbn. apply transpS_id. Defined.
Next Obligation. intros γ. cbn. apply transpS_comp. Defined.

(** Bundle code-valued types and their decoded section family at one context. *)

(** 在一个上下文中组合代码值类型及其解码截面族。 *)

Definition CodeFamily (Γ : SetC)
  : FamC
  :=
  {|famC_base := Γ →S Code
  ; famC_fam := CodeTerms Γ
  |}.

(** Substitute code-valued functions and decoded sections together. *)

(** 同时替换代码值函数及解码截面。 *)

Program Definition code_sub {Δ Γ : SetC} (σ : Δ →r Γ)
  : FamF (CodeFamily Γ) (CodeFamily Δ)
  :=
  {|famF_base :=
     {|func A := A ∘r σ
     |}
  ; famF_fam A := section_fam_map_resp El⟨A, σ⟩Fam
      ∘r section_reindex_resp El[A]S σ
  |}.
Next Obligation. intros A B H δ. exact (H (σ δ)). Defined.
Next Obligation. intros δ. cbn. apply transpS_witness_independent. Defined.

(** Codes and decoded sections form the type-and-term family-valued presheaf. *)

(** 代码与解码截面组成类型和项的族值预层。 *)

Program Definition CodeTyTmF
  : Fct (SetCat^op) FamCat
  :=
  {|F0 := CodeFamily
  ; F1 Γ Δ σ := code_sub σ
  |}.
Next Obligation.
  intros σ τ H. exists (λ A δ, @func_proper _ _ A _ _ (H δ)).
  intros A s δ. cbn. exact (section_proper s (H δ)).
Defined.
Next Obligation.
  exists (λ (A : X →r Code) δ, reflS (x := A δ)).
  intros A s δ. cbn. apply transpS_id.
Defined.
Next Obligation.
  exists (λ (A : X →r Code) δ, reflS (x := A (g (f δ)))).
  intros A s δ. cbn. apply transpS_id.
Defined.

(** Convert a section along the inverse decoding-composition comparison, then
    use the existing total-space pairing. The resulting map computes to
    [(σ δ; t δ)]. *)

(** 沿解码复合比较的逆转换截面，再使用已有全空间配对；所得映射计算为
    [(σ δ; t δ)]。 *)

Definition code_pair_resp {Δ Γ : SetC} (A : Γ →r Code) (σ : Δ →r Γ)
    (t : SectionS El[A ∘r σ]S)
  : Δ →r SigS Γ El[A]S
  := section_pair_resp El[A]S σ ((fam_map_reindex_comp_iso A σ El).1 ▷Fam t).

(** Choose decoded dependent sums as context extensions. *)

(** 选择解码依赖和作为上下文扩张。 *)

Program Definition CodeExtensions
  : HasContextExtension CodeTyTmF
  :=
  {|Ext Γ A := SigS Γ El[A]S
  ; context_proj Γ A := sig_base_resp El[A]S
  ; context_var Γ A :=
      El⟨A, sig_base_resp El[A]S⟩Fam ▷Fam section_var El[A]S
  |}.
Next Obligation.
  intros Δ σ t. exists (code_pair_resp A σ t). split.
  - exists (λ δ, reflS (x := σ δ)). intros δ. cbn. apply transpS_id.
  - intros h [H Ht] δ. exists (H δ).
    transitivity (transpS El
      (ty_sub_comm CodeTyTmF A (sig_base_resp El[A]S) h H δ) (h δ).2).
    + exact (transpS_witness_independent El _ _ (h δ).2).
    + exact (Ht δ).
Defined.

(** Enable a chosen model explicitly to obtain its terminal context and
    context extensions through the abstract CwF interface. *)

(** 显式启用选定模型，才能通过抽象带族范畴接口使用其终上下文和上下文扩张。 *)

Program Definition SetCwF
  : CwF SetCat
  :=
  {|hasTerminal := SetCat_HasTerminal
  ; TyTmF := CodeTyTmF
  ; hasContextExtension := CodeExtensions
  |}.

End CodeFamilies.
