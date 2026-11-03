From Cats Require Import
  Cat.Core
  Cat.Equalizer.

(** * Coequalizers *)

(** * 余等化子 *)

(** A candidate coequalizer is an equalizer in the opposite category. *)

(** 候选余等化子就是反范畴中的等化子。 *)

Definition is_coequalizer {C : Cat} {X Y : @Ob C} (f g : Hom X Y)
    (Q : @Ob C) (q : Hom Y Q)
  := @is_equalizer (C^op) Y X f g Q q.

Notation "q '⦂' 'Coeq(' f ',' g ')'" := (is_coequalizer f g _ q)
  (at level 50, no associativity) : cat_scope.

(** Store only the chosen equalizers of the opposite category. *)

(** 只存储反范畴的选定等化子。 *)

Class HasCoequalizer (C : Cat)
  :=
  { hasOpEqualizer :: HasEqualizer (C^op)
  }.

Section Coequalizer.
Context {C : Cat} `{HC : !HasCoequalizer C}.

(** The selected coequalizer object is its opposite equalizer object. *)

(** 选定余等化子对象就是反范畴中的等化子对象。 *)

Definition CoeqObj {X Y} (f g : Hom X Y)
  : @Ob C
  := @EqObj (C^op) (@hasOpEqualizer C HC) Y X f g.

(** The coequalizer projection is the opposite equalizer inclusion. *)

(** 余等化子投影就是反范畴中的等化子包含箭头。 *)

Definition coeqπ {X Y} (f g : Hom X Y)
  : Hom Y (CoeqObj f g)
  := @eqι (C^op) (@hasOpEqualizer C HC) Y X f g.

(** The full universal property is inherited without additional data. *)

(** 完整泛性质直接继承，不增加数据。 *)

Definition coequalizer_universal {X Y} {f g : Hom X Y}
  : is_coequalizer f g (CoeqObj f g) (coeqπ f g)
  := @equalizer_universal (C^op) (@hasOpEqualizer C HC) Y X f g.

(** Factor a coequalizing arrow using the original equalizer mediator. *)

(** 使用原等化子中介分解余等化箭头。 *)

Definition coequalize {X Y Q} {f g : Hom X Y} (q : Hom Y Q)
    (H : q ∘ f ≈ q ∘ g)
  : Hom (CoeqObj f g) Q
  := @equalize (C^op) (@hasOpEqualizer C HC) Y X Q f g q H.

(** The chosen projection coequalizes the pair. *)

(** 选定投影余等化给定平行箭头对。 *)

Theorem coequalizer_comm {X Y} {f g : Hom X Y}
  : coeqπ f g ∘ f ≈ coeqπ f g ∘ g.
Proof. exact (@equalizer_comm (C^op) (@hasOpEqualizer C HC) Y X f g). Qed.

(** The factor is unique with its specified projection composite. *)

(** 分解由其与投影的指定复合唯一确定。 *)

Theorem coequalizer_mediator_unique {X Y Q} {f g : Hom X Y}
    (q : Hom Y Q) (H : q ∘ f ≈ q ∘ g)
  : is_unique (λ h, h ∘ coeqπ f g ≈ q) (coequalize q H).
Proof.
  exact (@equalizer_mediator_unique (C^op) (@hasOpEqualizer C HC)
    Y X Q f g q H).
Qed.

(** Factoring and composing with the projection recovers the arrow. *)

(** 分解后与投影复合恢复原箭头。 *)

Theorem coequalizer_β {X Y Q} {f g : Hom X Y}
    (q : Hom Y Q) (H : q ∘ f ≈ q ∘ g)
  : coequalize q H ∘ coeqπ f g ≈ q.
Proof. exact (@equalizer_β (C^op) (@hasOpEqualizer C HC) Y X Q f g q H). Qed.

(** Respectfulness does not compare the commutativity witnesses. *)

(** 保相等性不比较交换性见证。 *)

Theorem coequalizer_proper {X Y Q} {f g : Hom X Y} {q q' : Hom Y Q}
    (H : q ∘ f ≈ q ∘ g) (H' : q' ∘ f ≈ q' ∘ g) (Hq : q ≈ q')
  : coequalize q H ≈ coequalize q' H'.
Proof.
  exact (@equalizer_proper (C^op) (@hasOpEqualizer C HC)
    Y X Q f g q q' H H' Hq).
Qed.

(** Factoring commutes with postcomposition. *)

(** 分解与后合成交换。 *)

Theorem coequalizer_comp {X Y Q R} {f g : Hom X Y} (q : Hom Y Q)
    (H : q ∘ f ≈ q ∘ g) (k : Hom Q R)
    (Hk : (k ∘ q) ∘ f ≈ (k ∘ q) ∘ g)
  : coequalize (k ∘ q) Hk ≈ k ∘ coequalize q H.
Proof.
  exact (@equalizer_comp (C^op) (@hasOpEqualizer C HC)
    Y X Q R f g q H k Hk).
Qed.

(** Factoring a projection composite recovers its original factor. *)

(** 分解投影复合后恢复原分解。 *)

Theorem coequalizer_η {X Y Q} {f g : Hom X Y}
    (h : Hom (CoeqObj f g) Q)
    (H : (h ∘ coeqπ f g) ∘ f ≈ (h ∘ coeqπ f g) ∘ g)
  : coequalize (h ∘ coeqπ f g) H ≈ h.
Proof. exact (@equalizer_η (C^op) (@hasOpEqualizer C HC) Y X Q f g h H). Qed.

End Coequalizer.

Notation "'Coeq[' f ',' g ']'" := (CoeqObj f g) : ob_scope.
Notation "'πcoeq[' f ',' g ']'" := (coeqπ f g) : hom_scope.
Notation "'coeq⟨' q ',' H '⟩'" := (coequalize q H) : hom_scope.

(** Cancellation follows directly from opposite equalizer cancellation. *)

(** 消去律直接来自反范畴中等化子的消去律。 *)

Theorem coequalizer_hom_ext {C : Cat} {X Y E Q : @Ob C} {f g : Hom X Y}
    {e : Hom Y E} (HE : is_coequalizer f g E e) (u v : Hom E Q)
    (H : u ∘ e ≈ v ∘ e)
  : u ≈ v.
Proof. exact (@equalizer_hom_ext (C^op) Y X E Q f g e HE u v H). Qed.
