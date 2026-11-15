From Cats Require Import
  Instance.Set.Simplicial.HornAttachment.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes for Constructive Attachments *)

(** * 构造性附着的独立大小 *)

(** ** Lower Abstract Hom Equality

    Keep object, arrow, equality and law sizes separate. Neither chosen
    pushouts nor respectful extension operations are assumed. *)

(** ** 较低抽象 Hom 相等

    保持对象、箭头、相等及定律大小独立，不假设选定推出或保相等的延拓操作。 *)

Section lowCategory.
Universes o h e l.
Constraint o < h, h < e, e < l.
Context (C : Cat@{o e h l l}) {A B D Z P Q : @Ob C}.
Context (f : Hom Z A) (g : Hom Z B) (i : Hom A P) (j : Hom B P)
    (HP : is_pushout f g P i j).

Definition low_pushout (E : is_extension_target g Q)
  : is_extension_target i Q
  := pushout_extension_target HP E.

Definition low_composite (v : Hom A B) (w : Hom B D)
    (E : is_extension_target v Q) (F : is_extension_target w Q)
  : is_extension_target (w ∘ v) Q
  := map_extension_target_comp v w E F.

End lowCategory.

(** ** Higher Abstract Hom Equality

    Keep object, arrow, equality and law sizes separate. Neither chosen
    pushouts nor respectful extension operations are assumed. *)

(** ** 较高抽象 Hom 相等

    保持对象、箭头、相等及定律大小独立，不假设选定推出或保相等的延拓操作。 *)

Section highCategory.
Universes o h e l.
Constraint o < h, h < e, e < l.
Context (C : Cat@{o h e l l}) {A B D Z P Q : @Ob C}.
Context (f : Hom Z A) (g : Hom Z B) (i : Hom A P) (j : Hom B P)
    (HP : is_pushout f g P i j).

Definition high_pushout (E : is_extension_target g Q)
  : is_extension_target i Q
  := pushout_extension_target HP E.

Definition high_composite (v : Hom A B) (w : Hom B D)
    (E : is_extension_target v Q) (F : is_extension_target w Q)
  : is_extension_target (w ∘ v) Q
  := map_extension_target_comp v w E F.

End highCategory.

(** ** Lower Simplicial Equality

    Supply one horn choice and a candidate attachment pushout at strict
    value sizes. No whole Kan structure or global model is available. *)

(** ** 较低单纯相等

    在严格取值大小下给定一份 horn 选择和候选附着推出，不提供完整 Kan 或全局模型。 *)

Section lowerHorn.
Universes l u p.
Constraint l < u, u < p.
Context (A P X B : Fct (Δ^op) SetCat@{u l _ _ _ _ _}).
Context (n : nat) (r : Ordinal n) (K K' : HasHornFillers X n r).
Context (h : Λ[n; r] ⇒ A) (i : A ⇒ P) (j : Δ[n] ⇒ P).
Context (HP : is_pushout (C := FctCat (Δ^op) SetCat@{u l _ _ _ _ _})
    h ιΛ[n; r] P i j).

Definition lower_target
  := horn_extension_target X n r K.

Definition lower_extension (a : A ⇒ X)
  : ∃ k : P ⇒ X, ((k ∘Nv i) ≈N a) ∧
      ((k ∘Nv j) ≈N (horn_extension_target X n r K (a ∘Nv h)).1)
  := HornAttachmentExtension h i j HP K a.

Definition lower_relative (a : A ⇒ X) (s : B ⇒ A) (c : B ⇒ X)
    (R : (a ∘Nv s) ≈N c)
  : ((lower_extension a).1 ∘Nv (i ∘Nv s)) ≈N c
  := horn_attachment_extension_relative h i j HP K a s c R.

Definition lower_unique (a : A ⇒ X) (k : P ⇒ X) (E : (k ∘Nv i) ≈N a)
    (F : (k ∘Nv j) ≈N (horn_extension_target X n r K (a ∘Nv h)).1)
  : k ≈N (lower_extension a).1
  := horn_attachment_extension_unique h i j HP K a k E F.

Definition lower_proper (a a' : A ⇒ X) (E : a ≈N a')
    (F : (horn_extension_target X n r K (a ∘Nv h)).1 ≈N
      (horn_extension_target X n r K' (a' ∘Nv h)).1)
  : (lower_extension a).1 ≈N (HornAttachmentExtension h i j HP K' a').1
  := horn_attachment_extension_proper h i j HP K K' a a' E F.

End lowerHorn.

(** ** Higher Simplicial Equality

    Supply one horn choice and a candidate attachment pushout at strict
    value sizes. No whole Kan structure or global model is available. *)

(** ** 较高单纯相等

    在严格取值大小下给定一份 horn 选择和候选附着推出，不提供完整 Kan 或全局模型。 *)

Section higherHorn.
Universes l u p.
Constraint l < u, u < p.
Context (A P X B : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).
Context (n : nat) (r : Ordinal n) (K K' : HasHornFillers X n r).
Context (h : Λ[n; r] ⇒ A) (i : A ⇒ P) (j : Δ[n] ⇒ P).
Context (HP : is_pushout (C := FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
    h ιΛ[n; r] P i j).

Definition higher_target
  := horn_extension_target X n r K.

Definition higher_extension (a : A ⇒ X)
  : ∃ k : P ⇒ X, ((k ∘Nv i) ≈N a) ∧
      ((k ∘Nv j) ≈N (horn_extension_target X n r K (a ∘Nv h)).1)
  := HornAttachmentExtension h i j HP K a.

Definition higher_relative (a : A ⇒ X) (s : B ⇒ A) (c : B ⇒ X)
    (R : (a ∘Nv s) ≈N c)
  : ((higher_extension a).1 ∘Nv (i ∘Nv s)) ≈N c
  := horn_attachment_extension_relative h i j HP K a s c R.

Definition higher_unique (a : A ⇒ X) (k : P ⇒ X) (E : (k ∘Nv i) ≈N a)
    (F : (k ∘Nv j) ≈N (horn_extension_target X n r K (a ∘Nv h)).1)
  : k ≈N (higher_extension a).1
  := horn_attachment_extension_unique h i j HP K a k E F.

Definition higher_proper (a a' : A ⇒ X) (E : a ≈N a')
    (F : (horn_extension_target X n r K (a ∘Nv h)).1 ≈N
      (horn_extension_target X n r K' (a' ∘Nv h)).1)
  : (higher_extension a).1 ≈N (HornAttachmentExtension h i j HP K' a').1
  := horn_attachment_extension_proper h i j HP K K' a a' E F.

End higherHorn.
