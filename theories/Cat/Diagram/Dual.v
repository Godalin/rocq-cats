From Cats Require Export
  Cat.Diagram.Core.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Cocones and Opposite Cones *)

(** * 余锥与反范畴中的锥 *)

(** A cocone is a natural transformation into a constant diagram. *)

(** 余锥是指向常图式的自然变换。 *)

Definition Cocone {J C : Cat} (D : Functor J C) (X : @Ob C)
  := D ⇒ ConstF J X.

Notation "D '⇒∇' X" := (Cocone D X)
  (at level 50, no associativity) : cat_scope.

(** A cocone leg factors through the next leg along a diagram arrow. *)

(** 沿图式箭头，余锥腿经过下一条余锥腿分解。 *)

Lemma cocone_naturality {J C : Cat} {D : Functor J C} {X}
    (κ : D ⇒∇ X) {i j : @Ob J} (f : Hom i j)
  : κ j ∘ fmap D f ≈ κ i.
Proof.
  pose proof (nt_naturality κ f) as H. cbn in H.
  rewrite comp_id_l in H. exact H.
Qed.

(** Postcompose every leg with an apex map. *)

(** 将每条余锥腿与顶点映射后合成。 *)

Definition cocone_comp {J C : Cat} {D : Functor J C} {X Y : @Ob C}
    (f : Hom X Y) (κ : D ⇒∇ X)
  : D ⇒∇ Y
  := fmap (DiagonalF J C) f ∘Nv κ.

Infix "∘Cocone" := cocone_comp
  (at level 40, left associativity) : cat_scope.

(** Postcomposition respects hom equality and pointwise cocone equality. *)

(** 后合成保持 Hom 相等及余锥的逐点相等。 *)

Global Instance cocone_comp_proper {J C : Cat} {D : Functor J C}
    {X Y : @Ob C}
  : Proper (@HomEq[X, Y] ==> NatEq ==> NatEq)
      (@cocone_comp J C D X Y).
Proof.
  intros f g H κ μ K j. cbn. rewrite H, (K j). reflexivity.
Qed.

(** Postcomposing by an identity leaves a cocone unchanged. *)

(** 与恒等后合成不改变余锥。 *)

Lemma cocone_comp_id {J C : Cat} {D : Functor J C} {X}
    (κ : D ⇒∇ X)
  : id ∘Cocone κ ≈N κ.
Proof. intros j. apply comp_id_l. Qed.

(** Postcomposition of cocones is associative. *)

(** 余锥的后合成满足结合律。 *)

Lemma cocone_comp_assoc {J C : Cat} {D : Functor J C} {X Y Z}
    (g : Hom Y Z) (f : Hom X Y) (κ : D ⇒∇ X)
  : g ∘Cocone (f ∘Cocone κ) ≈N (g ∘ f) ∘Cocone κ.
Proof. intros j. symmetry. apply comp_assoc. Qed.

(** Apply a functor to every cocone leg and its apex. *)

(** 将函子作用于每条余锥腿及其顶点。 *)

Program Definition MapCocone {J C E : Cat} (F : Functor C E)
    {D : Functor J C} {X : @Ob C} (κ : D ⇒∇ X)
  : (F ∘F D) ⇒∇ F X
  :=
  {|nt j := fmap F (κ j)
  |}.
Next Obligation.
  rewrite comp_id_l, <- (functor_comp C E F).
  apply functor_fmap_proper. apply cocone_naturality.
Qed.

(** Reverse a cocone into a cone on the opposite diagram. The legs retain
    their underlying arrows; no equality of functor records is required. *)

(** 将余锥反转为反图式上的锥。锥腿保留底层箭头，不要求函子记录相等。 *)

Program Definition CoconeOp {J C : Cat} {D : Functor J C} {X : @Ob C}
    (κ : D ⇒∇ X)
  : X ⇒Δ D^opF
  :=
  {|nt j := κ j
  |}.
Next Obligation.
  rewrite comp_id_l. symmetry.
  exact (@cocone_naturality J C D X κ Y X0 f).
Qed.

(** Recover a cocone from a cone on the opposite diagram. *)

(** 从反图式上的锥恢复余锥。 *)

Program Definition CoconeUnop {J C : Cat} {D : Functor J C}
    {X : @Ob C} (κ : X ⇒Δ D^opF)
  : D ⇒∇ X
  :=
  {|nt j := κ j
  |}.
Next Obligation.
  rewrite comp_id_l. symmetry.
  exact (@cone_naturality (J^op) (C^op) (D^opF) X κ Y X0 f).
Qed.

(** Reversing a cone gives a cocone on the opposite diagram. *)

(** 反转锥得到反图式上的余锥。 *)

Program Definition ConeOp {J C : Cat} {D : Functor J C} {X : @Ob C}
    (κ : X ⇒Δ D)
  : D^opF ⇒∇ X
  :=
  {|nt j := κ j
  |}.
Next Obligation.
  rewrite comp_id_r. symmetry.
  exact (@cone_naturality J C D X κ Y X0 f).
Qed.

(** Recover an original cone from a cocone on the opposite diagram. *)

(** 从反图式上的余锥恢复原来的锥。 *)

Program Definition ConeUnop {J C : Cat} {D : Functor J C}
    {X : @Ob C} (κ : D^opF ⇒∇ X)
  : X ⇒Δ D
  :=
  {|nt j := κ j
  |}.
Next Obligation.
  rewrite comp_id_r. symmetry.
  exact (@cocone_naturality (J^op) (C^op) (D^opF) X κ Y X0 f).
Qed.

(** Reversing cocones preserves their pointwise equality. *)

(** 反转余锥保持其逐点相等。 *)

Global Instance cocone_op_proper {J C : Cat} {D : Functor J C} {X}
  : Proper (NatEq ==> NatEq) (@CoconeOp J C D X).
Proof. intros κ μ H j. exact (H j). Qed.

(** Recovering cocones preserves their pointwise equality. *)

(** 恢复余锥保持其逐点相等。 *)

Global Instance cocone_unop_proper {J C : Cat} {D : Functor J C} {X}
  : Proper (NatEq ==> NatEq) (@CoconeUnop J C D X).
Proof. intros κ μ H j. exact (H j). Qed.

(** Reversing cones preserves their pointwise equality. *)

(** 反转锥保持其逐点相等。 *)

Global Instance cone_op_proper {J C : Cat} {D : Functor J C} {X}
  : Proper (NatEq ==> NatEq) (@ConeOp J C D X).
Proof. intros κ μ H j. exact (H j). Qed.

(** Recovering cones preserves their pointwise equality. *)

(** 恢复锥保持其逐点相等。 *)

Global Instance cone_unop_proper {J C : Cat} {D : Functor J C} {X}
  : Proper (NatEq ==> NatEq) (@ConeUnop J C D X).
Proof. intros κ μ H j. exact (H j). Qed.

(** The two conversions cancel componentwise, without comparing proof fields. *)

(** 两种转换逐分量抵消，不比较证明字段。 *)

Lemma cocone_unop_op {J C : Cat} {D : Functor J C} {X}
    (κ : D ⇒∇ X)
  : CoconeUnop (CoconeOp κ) ≈N κ.
Proof. intros j. reflexivity. Qed.

(** The reverse round trip also preserves all legs. *)

(** 反向往返也保持所有锥腿。 *)

Lemma cocone_op_unop {J C : Cat} {D : Functor J C} {X : @Ob C}
    (κ : X ⇒Δ D^opF)
  : CoconeOp (CoconeUnop κ) ≈N κ.
Proof. intros j. reflexivity. Qed.

(** The two cone conversions cancel on the original diagram. *)

(** 两种锥转换在原图式上抵消。 *)

Lemma cone_unop_op {J C : Cat} {D : Functor J C} {X}
    (κ : X ⇒Δ D)
  : ConeUnop (ConeOp κ) ≈N κ.
Proof. intros j. reflexivity. Qed.

(** The reverse cone round trip preserves all legs as well. *)

(** 反向的锥往返同样保持所有锥腿。 *)

Lemma cone_op_unop {J C : Cat} {D : Functor J C} {X : @Ob C}
    (κ : D^opF ⇒∇ X)
  : ConeOp (ConeUnop κ) ≈N κ.
Proof. intros j. reflexivity. Qed.

(** Reversing cocone postcomposition gives cone precomposition. *)

(** 反转余锥后合成得到锥的预合成。 *)

Lemma cocone_op_comp {J C : Cat} {D : Functor J C} {X Y : @Ob C}
    (f : Hom X Y) (κ : D ⇒∇ X)
  : CoconeOp (f ∘Cocone κ) ≈N CoconeOp κ ∘Cone f.
Proof. intros j. reflexivity. Qed.

(** Cocones form the opposite of the cone category of the opposite diagram.
    Its morphisms point from the source apex to the target apex in [C]. *)

(** 余锥构成反图式的锥范畴之反范畴；态射在 [C] 中从源顶点指向目标顶点。 *)

Definition CoconeCat {J C : Cat} (D : Functor J C)
  : Cat
  := (ConeCat (D^opF))^op.

(** Forget a cocone and its morphism to their apex and apex map in [C]. *)

(** 将余锥及其态射忘却为 [C] 中的顶点及顶点映射。 *)

Program Definition CoconeApexF {J C : Cat} (D : Functor J C)
  : Functor (CoconeCat D) C
  :=
  {|F0 κ := κ.1
  ; F1 κ μ f := f.1
  |}.
Next Obligation. intros f g H. exact H. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
