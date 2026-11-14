From Cats Require Export
  STLC.NormalEta
  STLC.RenamingCategory.
From Cats Require Import
  STLC.Set
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Syntax Presheaves on Renaming Worlds

    For a fixed type, neutral terms, long normal forms and beta/eta terms
    vary contravariantly over the renaming category. Their context actions
    are the existing renaming functions. We use the ordinary functor and
    natural-transformation interfaces, without a second presheaf structure.

    Neutral and normal trees carry structural equality, while raw terms
    carry beta/eta equality. These policies have different purposes:
    expansion commutes strictly with renaming, but its correctness triangle
    commutes in beta/eta equality. Neither statement equates proof fields or
    functions. The hom-equality level of the world category is independent
    of the equality level of presheaf values.

    This packages the syntactic part of a Kripke interpretation. It does
    not yet construct semantic function values or presheaf exponentials.
    In particular, the neutral and normal presheaves are not identified
    with the term presheaf; embeddings are not asserted to be isomorphisms. *)

(** * 重命名世界上的语法预层

    固定一个类型后，中性项、长正规形与 βη 项随重命名范畴反变，其上下文作用
    就是既有的重命名函数。这里使用普通函子与自然变换接口，不另建预层结构。

    中性与正规语法树采用结构相等，原始项则采用 βη 相等。两种约定各有用途：
    展开与重命名严格交换，正确性三角则按 βη 相等交换。二者都不比较证明字段
    或函数本身。世界范畴的 Hom 相等层级独立于预层值的相等层级。

    这封装了 Kripke 解释的语法部分，尚未构造语义函数值或预层指数对象。
    特别地，中性与正规预层不与项预层视为相同，也不断言嵌入为同构。 *)

Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** Neutral syntax with its native structural equality. *)

(** 带原生结构相等的中性语法。 *)

Program Definition NeS@{b q +} {B : Type@{b}} (Γ : Ctx B) (A : Ty B)
  : SetC@{b q}
  :=
  {|carrier := Ne Γ A
  ; carrier_equiv := @eq (Ne Γ A)
  ; carrier_setoid := ltac:(split; red; intros; congruence)
  |}.

(** Long normal syntax with its native structural equality. *)

(** 带原生结构相等的长正规语法。 *)

Program Definition NfS@{b q +} {B : Type@{b}} (Γ : Ctx B) (A : Ty B)
  : SetC@{b q}
  :=
  {|carrier := Nf Γ A
  ; carrier_equiv := @eq (Nf Γ A)
  ; carrier_setoid := ltac:(split; red; intros; congruence)
  |}.

(** Reindex neutral syntax along one world arrow. *)

(** 沿一条世界箭头重索引中性语法。 *)

Program Definition ne_rename_resp@{b q +} {B : Type@{b}}
    {Γ Δ : Ctx B} {A : Ty B}
    (ρ : Ren Δ Γ)
  : NeS@{b q} Γ A →r NeS@{b q} Δ A
  :=
  {|func n := n⟨ρ⟩ne
  |}.
Next Obligation. intros n m h. destruct h. reflexivity. Defined.

(** Reindex normal syntax; its action preserves the long-form invariant. *)

(** 重索引正规语法，其作用保持长正规形不变量。 *)

Program Definition nf_rename_resp@{b q +} {B : Type@{b}}
    {Γ Δ : Ctx B} {A : Ty B}
    (ρ : Ren Δ Γ)
  : NfS@{b q} Γ A →r NfS@{b q} Δ A
  :=
  {|func v := v⟨ρ⟩nf
  |}.
Next Obligation. intros v w h. destruct h. reflexivity. Defined.

(** ** Syntax Presheaves for a Fixed Signature

    Fix a signature [B] and bounds for world equality, syntax equality and
    world laws. Construct neutral, normal and raw-term presheaves together
    with their embeddings and eta transformation. References within the
    section inherit these bounds. *)

(** ** 固定签名的语法预层

    固定签名 [B] 及世界相等、语法相等与世界定律界限，构造中性、正规与原始项
    预层及其嵌入和 η 变换。节内引用继承这些界限。 *)

Section SyntaxPresheaves.
Universes b r q l.
Context {B : Type@{b}}.

(** The neutral presheaf: a world arrow [Δ → Γ] acts from syntax at [Γ]
    to syntax at [Δ]. Functor laws reuse the already proved syntax laws. *)

(** 中性预层：世界箭头 [Δ → Γ] 从 [Γ] 处语法作用到 [Δ] 处语法。
    函子律复用已经证明的语法定律。 *)

Program Definition NePsh (A : Ty B)
  : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{b q _ _ _ _ _}
  :=
  {|F0 Γ := NeS Γ A
  ; F1 _ _ ρ := ne_rename_resp ρ
  |}.
Next Obligation. intros ρ τ h n. apply rename_ne_ext. exact h. Defined.
Next Obligation. intros n. apply rename_ne_id. Defined.
Next Obligation. intros n. symmetry. apply rename_ne_comp. Defined.

(** The normal presheaf has the same world category and its own carriers. *)

(** 正规预层使用相同世界范畴，并具有自己的语法载体。 *)

Program Definition NfPsh (A : Ty B)
  : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{b q _ _ _ _ _}
  :=
  {|F0 Γ := NfS Γ A
  ; F1 _ _ ρ := nf_rename_resp ρ
  |}.
Next Obligation. intros ρ τ h v. apply rename_nf_ext. exact h. Defined.
Next Obligation. intros v. apply rename_nf_id. Defined.
Next Obligation. intros v. symmetry. apply rename_nf_comp. Defined.

(** Raw terms with beta/eta equality also form a presheaf on these worlds.
    This does not allow arbitrary substitution into a normal-form tree. *)

(** 带 βη 相等的原始项也在这些世界上组成预层；这并不允许将任意替换直接
    作用于正规形语法树。 *)

Program Definition TmRenamingPsh (A : Ty B)
  : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat
  :=
  {|F0 Γ := TmS@{b q} Γ A
  ; F1 _ _ ρ := tm_rename_resp ρ
  |}.
Next Obligation.
  intros ρ τ h t. apply tm_eq_of_eq. apply rename_ext. exact h.
Defined.
Next Obligation. intros t. apply tm_eq_of_eq. apply rename_id. Defined.
Next Obligation.
  intros t. apply tm_eq_of_eq. symmetry. apply rename_comp.
Defined.

(** Embed neutral syntax into the term setoid. *)

(** 将中性语法嵌入项广集。 *)

Program Definition embed_ne_resp
    (Γ : Ctx B) (A : Ty B)
  : NeS@{b q} Γ A →r TmS@{b q} Γ A
  :=
  {|func := embed_ne
  |}.
Next Obligation. intros n m h. destruct h. apply tm_eq_refl. Defined.

(** Embed normal syntax into the term setoid. *)

(** 将正规语法嵌入项广集。 *)

Program Definition embed_nf_resp
    (Γ : Ctx B) (A : Ty B)
  : NfS@{b q} Γ A →r TmS@{b q} Γ A
  :=
  {|func := embed_nf
  |}.
Next Obligation. intros v w h. destruct h. apply tm_eq_refl. Defined.

(** Eta expansion is respectful for structural equality. *)

(** η 展开尊重结构相等。 *)

Program Definition eta_expand_ne_resp
    (Γ : Ctx B) (A : Ty B)
  : NeS@{b q} Γ A →r NfS@{b q} Γ A
  :=
  {|func := eta_expand_ne
  |}.
Next Obligation. intros n m h. destruct h. reflexivity. Defined.

(** The neutral embedding is natural by strict embedding/renaming
    compatibility, included into beta/eta equality. *)

(** 中性嵌入的自然性来自嵌入与重命名的严格相容律，再将其纳入 βη 相等。 *)

Program Definition NeEmbedN (A : Ty B)
  : NePsh A ⇒ TmRenamingPsh A
  :=
  {|nt Γ := embed_ne_resp Γ A
  |}.
Next Obligation. intros n. apply tm_eq_of_eq. apply embed_rename_ne. Defined.

(** The normal embedding is natural for the same reason. *)

(** 正规嵌入出于相同原因具有自然性。 *)

Program Definition NfEmbedN (A : Ty B)
  : NfPsh A ⇒ TmRenamingPsh A
  :=
  {|nt Γ := embed_nf_resp Γ A
  |}.
Next Obligation. intros v. apply tm_eq_of_eq. apply embed_rename_nf. Defined.

(** The strict eta-expansion/renaming law is exactly naturality. *)

(** η 展开与重命名的严格交换律恰好就是自然性。 *)

Program Definition NeutralEtaN (A : Ty B)
  : NePsh A ⇒ NfPsh A
  :=
  {|nt Γ := eta_expand_ne_resp Γ A
  |}.
Next Obligation. intros n. apply eta_expand_ne_rename. Defined.

(** The two paths from neutral syntax to beta/eta terms agree as natural
    transformations. This is expansion correctness, not equality or inverse
    laws for the derivation witnesses. *)

(** 从中性语法到 βη 项的两条路径按自然变换相等。这是展开正确性，不是推导
    见证的相等或互逆定律。 *)

Definition neutral_eta_triangle (A : Ty B)
  : NeEmbedN A ≈N (NfEmbedN A ∘Nv NeutralEtaN A).
Proof. intros Γ n. apply eta_expand_ne_sound. Defined.

End SyntaxPresheaves.
