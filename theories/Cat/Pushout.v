From Cats Require Import
  Cat.Core
  Cat.Pullback.

(** * Pushouts through Opposite Pullbacks *)

(** * 通过反范畴拉回构造推出 *)

(** A candidate pushout is the original pullback property in the opposite
    category. Its legs have a common source in [C]. *)

(** 候选推出就是反范畴中的原拉回性质；两条腿在 [C] 中具有共同源。 *)

Definition is_pushout {C : Cat} {X Y Z : @Ob C}
    (f : Hom Z X) (g : Hom Z Y) (P : @Ob C)
    (i : Hom X P) (j : Hom Y P)
  := @is_pullback (C^op) X Y Z f g P i j.

(** Store only the selected pullbacks of the opposite category. *)

(** 只存储反范畴的选定拉回。 *)

Class HasPushout (C : Cat)
  :=
  { hasOpPullback :: HasPullback (C^op)
  }.

(** The selected pushout object is the opposite pullback object. *)

(** 选定推出对象就是反范畴中的拉回对象。 *)

Definition Po {C : Cat} `{HP : !HasPushout C} {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : @Ob C
  := @Pb (C^op) (@hasOpPullback C HP) X Y Z f g.

Notation "X '⊔[' f ',' g ']' Y" := (@Po _ _ X Y _ f g)
  (at level 52, no associativity) : ob_scope.

(** The first injection is the original opposite first projection. *)

(** 第一注入就是原反范畴中的第一投影。 *)

Definition po1 {C : Cat} `{HP : !HasPushout C} {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : Hom X (X ⊔[f,g] Y)
  := @Cat.Pullback.pb1 (C^op) (@hasOpPullback C HP) X Y Z f g.

Notation "'ιpo1[' f ',' g ']'" := (po1 f g) : hom_scope.

(** The second injection is the original opposite second projection. *)

(** 第二注入就是原反范畴中的第二投影。 *)

Definition po2 {C : Cat} `{HP : !HasPushout C} {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : Hom Y (X ⊔[f,g] Y)
  := @Cat.Pullback.pb2 (C^op) (@hasOpPullback C HP) X Y Z f g.

Notation "'ιpo2[' f ',' g ']'" := (po2 f g) : hom_scope.

(** The full pushout property is inherited from the stored pullback. *)

(** 完整推出性质继承自存储的拉回。 *)

Definition pushout_universal {C : Cat} `{HP : !HasPushout C}
    {X Y Z} {f : Hom Z X} {g : Hom Z Y}
  : is_pushout f g (X ⊔[f,g] Y) ιpo1[f,g] ιpo2[f,g]
  := @pullback_universal (C^op) (@hasOpPullback C HP) X Y Z f g.

(** The universal map out of a pushout is the original pullback mediator.
    The commutativity witness remains computational data. *)

(** 从推出出发的泛映射就是原拉回中介；交换性见证仍为计算数据。 *)

Definition po {C : Cat} `{HP : !HasPushout C} {X Y Z}
    {f : Hom Z X} {g : Hom Z Y} {P}
    (i : Hom X P) (j : Hom Y P) (H : i ∘ f ≈ j ∘ g)
  : Hom (X ⊔[f,g] Y) P
  := @pb (C^op) (@hasOpPullback C HP) X Y Z f g P i j H.

Notation "'po⟨' i ',' j ',' H '⟩'" := (po i j H) : hom_scope.

Section Pushout.
Context {C : Cat} `{HP : !HasPushout C}.
Context {X Y Z} {f : Hom Z X} {g : Hom Z Y}.

(** The selected pushout square commutes. *)

(** 选定推出方形交换。 *)

Theorem pushout_comm
  : ιpo1[f,g] ∘ f ≈ ιpo2[f,g] ∘ g.
Proof. exact (@pullback_comm (C^op) (@hasOpPullback C HP) X Y Z f g). Qed.

(** The mediator is unique with its two specified injection composites. *)

(** 中介由其与两个注入的指定复合唯一确定。 *)

Theorem pushout_mediator_unique {P} {i : Hom X P} {j : Hom Y P}
    (H : i ∘ f ≈ j ∘ g)
  : is_unique (λ h, h ∘ ιpo1[f,g] ≈ i ∧ h ∘ ιpo2[f,g] ≈ j) po⟨i,j,H⟩.
Proof.
  exact (@pullback_mediator_unique (C^op) (@hasOpPullback C HP)
    X Y Z f g P i j H).
Qed.

(** The first injection followed by the mediator gives the first map. *)

(** 第一注入后接中介得到第一条映射。 *)

Theorem po_β1 {P} (i : Hom X P) (j : Hom Y P) (H : i ∘ f ≈ j ∘ g)
  : po⟨i,j,H⟩ ∘ ιpo1[f,g] ≈ i.
Proof. exact (@pb_β1 (C^op) (@hasOpPullback C HP) X Y Z f g P i j H). Qed.

(** The second injection followed by the mediator gives the second map. *)

(** 第二注入后接中介得到第二条映射。 *)

Theorem po_β2 {P} (i : Hom X P) (j : Hom Y P) (H : i ∘ f ≈ j ∘ g)
  : po⟨i,j,H⟩ ∘ ιpo2[f,g] ≈ j.
Proof. exact (@pb_β2 (C^op) (@hasOpPullback C HP) X Y Z f g P i j H). Qed.

(** The two injection equations characterize the chosen mediator. *)

(** 两个注入方程刻画选定中介。 *)

Theorem po_η {P} (i : Hom X P) (j : Hom Y P) (H : i ∘ f ≈ j ∘ g)
    (h : Hom (X ⊔[f,g] Y) P)
  : h ∘ ιpo1[f,g] ≈ i ∧ h ∘ ιpo2[f,g] ≈ j → h ≈ po⟨i,j,H⟩.
Proof. exact (@pb_η (C^op) (@hasOpPullback C HP) X Y Z f g P i j H h). Qed.

(** Equal input maps produce equal mediators without comparing their
    commutativity witnesses. *)

(** 相等的输入映射给出相等的中介，无需比较交换性见证。 *)

Theorem po_proper {P} {i i' : Hom X P} {j j' : Hom Y P}
    (H : i ∘ f ≈ j ∘ g) (H' : i' ∘ f ≈ j' ∘ g)
    (Hi : i ≈ i') (Hj : j ≈ j')
  : po⟨i,j,H⟩ ≈ po⟨i',j',H'⟩.
Proof.
  exact (@pb_proper (C^op) (@hasOpPullback C HP)
    X Y Z f g P i j H i' j' H' Hi Hj).
Qed.

(** The mediator is independent of the chosen commutativity witness. *)

(** 中介不依赖所选交换性见证。 *)

Theorem po_witness_independent {P} (i : Hom X P) (j : Hom Y P)
    (H H' : i ∘ f ≈ j ∘ g)
  : po⟨i,j,H⟩ ≈ po⟨i,j,H'⟩.
Proof.
  exact (@pb_witness_independent (C^op) (@hasOpPullback C HP)
    X Y Z f g P i j H H').
Qed.

End Pushout.

(** Maps out of any candidate pushout are detected by both injections. *)

(** 从任意候选推出出发的映射由两个注入检测。 *)

Theorem pushout_hom_ext {C : Cat} {X Y Z P Q : @Ob C}
    {f : Hom Z X} {g : Hom Z Y} {i : Hom X P} {j : Hom Y P}
    (HP : is_pushout f g P i j) (u v : Hom P Q)
    (H1 : u ∘ i ≈ v ∘ i) (H2 : u ∘ j ≈ v ∘ j)
  : u ≈ v.
Proof. exact (@pullback_hom_ext (C^op) X Y Z P Q f g i j HP u v H1 H2). Qed.

(** Pushout uniqueness uses the inverse arrows of opposite pullback
    uniqueness, with the inverse laws read in [C]. *)

(** 推出唯一性使用反范畴拉回唯一性的逆向箭头，并将互逆定律读回 [C]。 *)

Definition pushout_unique {C : Cat} {X Y Z P Q : @Ob C}
    {f : Hom Z X} {g : Hom Z Y}
    {i : Hom X P} {j : Hom Y P} {i' : Hom X Q} {j' : Hom Y Q}
    (HP : is_pushout f g P i j) (HQ : is_pushout f g Q i' j')
  : P ≅[C] Q.
Proof.
  pose (e := @pullback_unique (C^op) X Y Z f g Q i' j' P i j HQ HP).
  exists e.1, e.2.1. split;
    [exact (snd e.2.2) | exact (fst e.2.2)].
Defined.

(** The identity square is an opposite identity pullback square. *)

(** 恒等方形就是反范畴中的恒等拉回方形。 *)

Definition pushout_id {C : Cat} {Y Z : @Ob C} (g : Hom Z Y)
  : is_pushout id g Y g id
  := @pullback_id (C^op) Y Z g.

(** Pasting pushout squares is the original pullback pasting theorem. *)

(** 推出方形的粘合就是原来的拉回粘合定理。 *)

Definition pushout_comp {C : Cat} {X Y Z W P Q : @Ob C}
    {f : Hom Z X} {g : Hom Z Y} {h : Hom X W}
    {i : Hom X P} {j : Hom Y P} {k : Hom W Q} {l : Hom P Q}
    (HP : is_pushout f g P i j) (HQ : is_pushout h i Q k l)
  : is_pushout (h ∘ f) g Q k (l ∘ j)
  := @pullback_comp (C^op) X Y Z W f g h P Q i j k l HP HQ.
