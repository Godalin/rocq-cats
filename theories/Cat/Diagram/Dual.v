From Cats Require Export
  Cat.Diagram.Core.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Cocones as Opposite Cones *)

(** * 余锥直接取反范畴中的锥 *)

(** A cocone is the original cone construction on the opposite diagram.
    Its components are arrows from diagram objects to the apex in [C]. *)

(** 余锥直接使用反图式上的原锥构造；其分量在 [C] 中从图式对象指向顶点。 *)

Record Cocone {J C : Cat} (D : Fct J C) (X : @Ob C)
  :=
  { op_cone : @Cone (J^op) (C^op) (D^opF) X
  }.

Arguments op_cone {_ _ _ _} _.

(** The ordinary natural-transformation interface reads the stored opposite
    legs in [C]; its naturality is inherited from the cone. *)

(** 通常的自然变换接口将存储的反锥腿读回 [C]，自然性直接继承自锥。 *)

Program Definition CoconeN {J C : Cat} {D : Fct J C} {X : @Ob C}
    (κ : Cocone D X)
  : D ⇒ ConstF J X
  :=
  {|nt j := op_cone κ j
  |}.
Next Obligation.
  rewrite comp_id_l. symmetry.
  exact (@cone_naturality (J^op) (C^op) (D^opF) X (op_cone κ) Y X0 f).
Qed.

Coercion CoconeN : Cocone >-> Nat.

Notation "D '⇒∇' X" := (Cocone D X)
  (at level 50, no associativity) : cat_scope.

(** The ordinary cocone equation is opposite-cone naturality. *)

(** 通常的余锥方程就是反锥的自然性。 *)

Lemma cocone_naturality {J C : Cat} {D : Fct J C} {X}
    (κ : D ⇒∇ X) {i j : @Ob J} (f : Hom i j)
  : κ j ∘ fmap D f ≈ κ i.
Proof.
  symmetry.
  exact (@cone_naturality (J^op) (C^op) (D^opF) X (op_cone κ) j i f).
Qed.

(** Postcomposition is cone precomposition in the opposite category. *)

(** 后合成就是反范畴中锥的预合成。 *)

Definition cocone_comp {J C : Cat} {D : Fct J C} {X Y : @Ob C}
    (f : Hom X Y) (κ : D ⇒∇ X)
  : D ⇒∇ Y
  :=
  {|op_cone := op_cone κ ∘Cone f
  |}.

Infix "∘Cocone" := cocone_comp
  (at level 40, left associativity) : cat_scope.

(** Respectfulness is inherited from cone precomposition. *)

(** 保相等性继承自锥的预合成。 *)

Global Instance cocone_comp_proper {J C : Cat} {D : Fct J C}
    {X Y : @Ob C}
  : Proper (@HomEq[X, Y] ==>
      (λ κ μ : D ⇒∇ X, κ ≈N μ) ==>
      (λ κ μ : D ⇒∇ Y, κ ≈N μ))
      (@cocone_comp J C D X Y).
Proof.
  intros f g H κ μ K.
  exact (@cone_comp_proper (J^op) (C^op) (D^opF) X Y
    (op_cone κ) (op_cone μ) K f g H).
Qed.

(** The cocone identity law is the cone identity law. *)

(** 余锥的恒等律就是锥的恒等律。 *)

Lemma cocone_comp_id {J C : Cat} {D : Fct J C} {X}
    (κ : D ⇒∇ X)
  : id ∘Cocone κ ≈N κ.
Proof. exact (cone_comp_id (op_cone κ)). Qed.

(** Cocone associativity reverses the two apex maps. *)

(** 余锥结合律反转两个顶点映射的次序。 *)

Lemma cocone_comp_assoc {J C : Cat} {D : Fct J C} {X Y Z}
    (g : Hom Y Z) (f : Hom X Y) (κ : D ⇒∇ X)
  : g ∘Cocone (f ∘Cocone κ) ≈N (g ∘ f) ∘Cocone κ.
Proof. exact (cone_comp_assoc (op_cone κ) f g). Qed.

(** Precompose a cocone by a diagram transformation using its opposite
    transformation and the original vertical composition. *)

(** 用图式自然变换预合成余锥，底层使用其反变换及原来的垂直复合。 *)

Definition cocone_precompose {J C : Cat} {D E : Fct J C} {X : @Ob C}
    (κ : E ⇒∇ X) (α : D ⇒ E)
  : D ⇒∇ X
  :=
  {|op_cone := α^opN ∘Nv op_cone κ
  |}.

Infix "∘∇" := cocone_precompose
  (at level 51, right associativity) : cat_scope.

(** The diagram-action interface respects the same pointwise equalities. *)

(** 图式作用接口保持同样的逐点相等。 *)

Global Instance cocone_precompose_proper {J C : Cat}
    {D E : Fct J C} {X : @Ob C}
  : Proper ((λ κ μ : E ⇒∇ X, κ ≈N μ) ==> NatEq ==>
      (λ κ μ : D ⇒∇ X, κ ≈N μ)) (@cocone_precompose J C D E X).
Proof.
  intros κ μ H α β K j. cbn. rewrite (H j), (K j). reflexivity.
Qed.

(** Functor images use [MapCone] on opposites, followed by the existing
    comparison between opposition and composition. *)

(** 函子像使用反范畴中的 [MapCone]，再沿取反与复合的已有比较转换图式。 *)

Definition MapCocone {J C E : Cat} (F : Fct C E)
    {D : Fct J C} {X : @Ob C} (κ : D ⇒∇ X)
  : (F ∘F D) ⇒∇ F X
  :=
  {|op_cone := ((OpF_comp F D).1 ^-1N (OpF_comp F D).2) ∘Nv
      MapCone (F^opF) (op_cone κ)
  |}.

(** Supply ordinary natural-transformation components to the opposite-cone
    representation, without a second cocone record. *)

(** 将通常自然变换的分量送入反锥表示，不另设第二种余锥记录。 *)

Program Definition CoconeOfN {J C : Cat} {D : Fct J C} {X : @Ob C}
    (κ : D ⇒ ConstF J X)
  : D ⇒∇ X
  :=
  {|op_cone :=
      {|nt j := κ j
      |}
  |}.
Next Obligation.
  pose proof (nt_naturality κ f) as H. cbn in H.
  rewrite comp_id_l in H. rewrite comp_id_l. symmetry. exact H.
Qed.

(** Reading a cone on the double-opposite diagram only rebuilds naturality
    at the required endpoints; its component arrows stay unchanged. *)

(** 将锥读入双重反图式时只在相应端点重组自然性，分量箭头保持不变。 *)

Program Definition ConeOp {J C : Cat} {D : Fct J C} {X : @Ob C}
    (κ : X ⇒Δ D)
  : D^opF ⇒∇ X
  :=
  {|op_cone :=
      {|nt j := κ j
      |}
  |}.
Next Obligation. exact (nt_naturality κ f). Qed.

(** Read an opposite-target diagram as an ordinary diagram of opposite
    shape, retaining its object and arrow maps. *)

(** 将反目标范畴中的图式读作反形状的通常图式，保留其对象及箭头映射。 *)

Definition DualDiagram {J C : Cat} (D : Fct J (C^op))
  : Fct (J^op) C
  := FromDoubleOpF ∘F D^opF.

(** Read its original cone as a cocone. Only the naturality endpoints are
    adapted; component arrows and all computational witnesses are retained. *)

(** 将其原锥读作余锥；仅适配自然性端点，保留分量箭头及所有计算见证。 *)

Program Definition DualCone {J C : Cat} {D : Fct J (C^op)} {X}
    (κ : X ⇒Δ D)
  : DualDiagram D ⇒∇ X
  :=
  {|op_cone :=
      {|nt j := κ j
      |}
  |}.
Next Obligation. exact (nt_naturality κ f). Qed.

(** Recover the original cone presentation from the double-opposite one. *)

(** 从双重反图式的锥表示恢复原来的锥表示。 *)

Program Definition ConeUnop {J C : Cat} {D : Fct J C} {X : @Ob C}
    (κ : D^opF ⇒∇ X)
  : X ⇒Δ D
  :=
  {|nt j := κ j
  |}.
Next Obligation. exact (nt_naturality (op_cone κ) f). Qed.

(** Cocone objects and morphisms are supplied by the opposite cone category. *)

(** 余锥对象及态射直接由反锥范畴给出。 *)

Definition CoconeCat {J C : Cat} (D : Fct J C)
  : Cat
  := (ConeCat (D^opF))^op.

(** The apex functor is the opposite of the original apex functor, read
    back in [C]. *)

(** 顶点函子为原顶点函子取反后读回 [C] 的结果。 *)

Definition CoconeApexF {J C : Cat} (D : Fct J C)
  : Fct (CoconeCat D) C
  := FromDoubleOpF ∘F (ConeApexF (D^opF))^opF.
