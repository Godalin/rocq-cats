From Cats Require Export
  Cat.Applicative.Closed.
From Cats Require Import
  Cat.Isomorphism
  Cat.Product.Transport.

Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.

(** * Operation-Preserving Applicative Comparisons

    Fix selected finite products on one category. A natural transformation
    between Applicatives preserves pure values and ordered pairing. These
    Type-valued laws imply preservation of all binary liftings, the lax
    unit and, when exponentials are selected, application. Invertible
    comparisons transfer the same laws to their chosen inverses. *)

(** * 保持运算的 Applicative 比较

    固定同一范畴上的选定有限积。Applicative 间的自然变换保持纯值与有序配对。
    这些 Type 值定律推出全部二元提升、lax 单位，以及选定指数时的应用保持性。
    可逆比较将同样的定律传递给其选定逆。 *)

Section Comparisons.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}.

(** Laws on a supplied natural transformation; no new underlying functor
    or equality of law records is selected. Pairing retains its order. *)

(** 所给自然变换上的定律；不另选底层函子，也不比较定律记录相等。
    配对保留原顺序。 *)

Definition is_applicative_hom (A B : Applicative C HT HP) (α : A ⇒ B)
  : Type
  := (∀ X, α X ∘ pure[A] X ≈ pure[B] X) ∧
      (∀ X Y, α (X × Y)%ob ∘ φ₂[A; X; Y] ≈
        φ₂[B; X; Y] ∘ (α X × α Y)).

(** Componentwise equal comparisons preserve the same operations. *)

(** 分量相等的比较保持同样的运算。 *)

Lemma applicative_hom_equiv (A B : Applicative C HT HP) (α β : A ⇒ B)
    (E : α ≈N β)
  : is_applicative_hom A B α ↔ is_applicative_hom A B β.
Proof.
  split; intros [Hu Hp]; split.
  - intros X. rewrite <- (E X). exact (Hu X).
  - intros X Y. rewrite <- (E (X × Y)%ob), <- (E X), <- (E Y).
    exact (Hp X Y).
  - intros X. rewrite (E X). exact (Hu X).
  - intros X Y. rewrite (E (X × Y)%ob), (E X), (E Y).
    exact (Hp X Y).
Qed.

(** Identity is an operation-preserving comparison. *)

(** 恒等是保持运算的比较。 *)

Lemma applicative_hom_id (A : Applicative C HT HP)
  : is_applicative_hom A A idN.
Proof.
  split; intros; cbn; rewrite ?cross_id, ?comp_id_l, ?comp_id_r;
    reflexivity.
Qed.

(** Composing comparisons preserves pure values and ordered pairing. *)

(** 复合比较保持纯值与有序配对。 *)

Lemma applicative_hom_comp (A B D : Applicative C HT HP)
    (β : B ⇒ D) (α : A ⇒ B)
    (Hβ : is_applicative_hom B D β) (Hα : is_applicative_hom A B α)
  : is_applicative_hom A D (β ∘Nv α).
Proof.
  destruct Hα as [Hαu Hαp], Hβ as [Hβu Hβp]. split.
  - intros X. change ((β X ∘ α X) ∘ pure[A] X ≈ pure[D] X).
    rewrite comp_assoc, Hαu. exact (Hβu X).
  - intros X Y.
    change ((β (X × Y)%ob ∘ α (X × Y)%ob) ∘ φ₂[A; X; Y] ≈
      φ₂[D; X; Y] ∘ ((β X ∘ α X) × (β Y ∘ α Y))).
    rewrite comp_assoc, Hαp, <- comp_assoc, Hβp, comp_assoc.
    apply comp_proper; [reflexivity|]. symmetry.
    exact (@cross_comp C HP _ _ _ _ _ _ (β X) (β Y) (α X) (α Y)).
Qed.

(** Pure preservation already includes the lax unit comparison. *)

(** 纯值保持性已经蕴含 lax 单位比较的保持性。 *)

Lemma applicative_hom_unit (A B : Applicative C HT HP) (α : A ⇒ B)
    (Hα : is_applicative_hom A B α)
  : α 1 ∘ φ₀[A] ≈ φ₀[B].
Proof.
  rewrite <- !applicative_pure_unit. exact (fst Hα 1).
Qed.

(** Naturality and pairing preservation imply every binary lifting law. *)

(** 自然性与配对保持性推出每个二元提升的保持律。 *)

Lemma applicative_hom_lift2 (A B : Applicative C HT HP) (α : A ⇒ B)
    (Hα : is_applicative_hom A B α)
    {X Y Z : @Ob C} (h : Hom (X × Y) Z)
  : α Z ∘ lift₂[A; h] ≈ lift₂[B; h] ∘ (α X × α Y).
Proof.
  unfold lax_lift2. rewrite <- comp_assoc, (nt_naturality α h),
    comp_assoc, (snd Hα X Y), comp_assoc. reflexivity.
Qed.

(** Pure preservation holds in every shared ordinary context. *)

(** 纯值保持性在每个共同通常上下文中成立。 *)

Lemma applicative_hom_pure_value (A B : Applicative C HT HP) (α : A ⇒ B)
    (Hα : is_applicative_hom A B α) {W X : @Ob C} (x : Hom W X)
  : α X ∘ pure[A; x] ≈ pure[B; x].
Proof.
  unfold applicative_pure_value. rewrite <- comp_assoc, (fst Hα X).
  reflexivity.
Qed.

(** Lifted operations are preserved in every shared input context. *)

(** 提升运算在每个共同输入上下文中得到保持。 *)

Lemma applicative_hom_lift2_context (A B : Applicative C HT HP)
    (α : A ⇒ B) (Hα : is_applicative_hom A B α)
    {W X Y Z : @Ob C} (h : Hom (X × Y) Z)
    (f : Hom W (A X)) (g : Hom W (A Y))
  : α Z ∘ (lift₂[A; h] ∘ ⟨f, g⟩) ≈
      lift₂[B; h] ∘ ⟨α X ∘ f, α Y ∘ g⟩.
Proof.
  rewrite <- comp_assoc, (applicative_hom_lift2 A B α Hα h), comp_assoc.
  apply comp_proper; [reflexivity|].
  exact (@product_comp_l C HP _ _ _ _ _ f g (α X) (α Y)).
Qed.

(** The chosen inverse of an operation-preserving natural isomorphism
    preserves the operations, by cancellation and the same inverse laws. *)

(** 保持运算的自然同构的选定逆，通过消去及同样的互逆律也保持运算。 *)

Lemma applicative_hom_inverse (A B : Applicative C HT HP) (α : A ⇒ B)
    (Hα : is_applicative_hom A B α) (I : α ⦂ A ≅N B)
  : is_applicative_hom B A (α ^-1N I).
Proof.
  destruct Hα as [Hu Hp]. split.
  - intros X. apply (iso_cancel_l (α X; I X)).
    change (α X ∘ ((I X).1 ∘ pure[B] X) ≈ α X ∘ pure[A] X).
    rewrite <- comp_assoc, (snd (I X).2), comp_id_l, Hu. reflexivity.
  - intros X Y. apply (iso_cancel_l (α (X × Y)%ob; I (X × Y)%ob)).
    change (α (X × Y)%ob ∘ ((I (X × Y)%ob).1 ∘ φ₂[B; X; Y]) ≈
      α (X × Y)%ob ∘ (φ₂[A; X; Y] ∘ ((I X).1 × (I Y).1))).
    rewrite <- !comp_assoc, (snd (I (X × Y)%ob).2), comp_id_l,
      Hp, comp_assoc,
      <- (@cross_comp C HP _ _ _ _ _ _ (α X) (α Y) (I X).1 (I Y).1),
      (snd (I X).2), (snd (I Y).2), (@cross_id C HP), comp_id_r.
    reflexivity.
Qed.

End Comparisons.

(** * Application Preservation in a Closed Base

    Add selected exponentials to the same finite products. Application is
    lifted evaluation, so the preceding binary law supplies its comparison. *)

(** * 闭基底中的应用保持性

    在同一有限积上添加选定指数。应用是提升后的求值，因此前面的二元定律
    给出其比较。 *)

Section Application.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP}.

(** Preserve effectful application without additional strength assumptions. *)

(** 保持带效应应用，不另加强度假设。 *)

Lemma applicative_hom_ap (A B : Applicative C HT HP) (α : A ⇒ B)
    (Hα : is_applicative_hom A B α) (X Y : @Ob C)
  : α Y ∘ ap[A] ≈ ap[B] ∘ (α (Y ^ X)%ob × α X).
Proof. exact (applicative_hom_lift2 A B α Hα eval). Qed.

(** Preserve application of two computations in an arbitrary shared context. *)

(** 保持任意共同上下文中两个计算的应用。 *)

Lemma applicative_hom_apply (A B : Applicative C HT HP) (α : A ⇒ B)
    (Hα : is_applicative_hom A B α)
    {W X Y : @Ob C} (f : Hom W (A (Y ^ X))) (x : Hom W (A X))
  : α Y ∘ (f ⋆[A] x) ≈ (α (Y ^ X)%ob ∘ f) ⋆[B] (α X ∘ x).
Proof. exact (applicative_hom_lift2_context A B α Hα eval f x). Qed.

End Application.
