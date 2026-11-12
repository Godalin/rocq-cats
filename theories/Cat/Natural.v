From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.Core.



(** * Natural Transformations *)

(** * 自然变换 *)

(** Given functors [F] and [G] from [C] to [D], a natural transformation
    compares their object images by arrows in [D]. Naturality is the
    compatibility that makes a component family one transformation between
    functors. The components need not be invertible, and their endpoints
    need not be equal objects. *)

(** 给定从 [C] 到 [D] 的函子 [F]、[G]，自然变换用 [D] 中的箭头比较它们的
    对象像。自然性使各分量相容，组成函子之间的同一个变换。分量无须可逆，
    其两端也无须是相等的对象。 *)

Class Nat {C D : Cat} (F G : Functor C D)
  := mkNat
  (** [nt X] is the component from [F X] to [G X]. The [:>] coercion lets
      a transformation [α] act as a component family, written [α X]. *)

  (** [nt X] 是从 [F X] 到 [G X] 的分量。[:>] 强制转换使自然变换 [α]
      可直接作为分量族使用，记作 [α X]。 *)

  { nt (X : @Ob C) :> (@Hom D) (F X) (G X)

  (** [nt_naturality] requires [α Y ∘ fmap F f ≈ fmap G f ∘ α X].
      Both sides go from [F X] to [G Y]: one first follows [F] along [f]
      and then changes to [G]; the other first changes to [G] and then
      follows [G] along [f]. The paths agree in [D]'s hom equality. *)

  (** [nt_naturality] 要求 [α Y ∘ fmap F f ≈ fmap G f ∘ α X]。
      两侧都是从 [F X] 到 [G Y] 的箭头：一条先沿 [F] 映射的 [f] 前进，
      再切换到 [G]；另一条先切换到 [G]，再沿 [G] 映射的 [f] 前进。
      两条路径在 [D] 的 Hom 相等下相等。 *)

  ; nt_naturality
    : ∀ X Y : @Ob C, ∀ f : Hom X Y,
      nt Y ∘ fmap F f ≈ fmap G f ∘ nt X
  }.

Arguments mkNat {_ _ _ _} _ _.
Arguments nt {_ _ _ _} _ _.
Arguments nt_naturality {_ _ _ _} _ {_ _} _.

Notation "F ⇒ G" := (Nat F G)
  (at level 50, no associativity) : type_scope.

(** Two transformations with fixed endpoints are equal when every pair of
    corresponding components is equal in [D]. This is written [α ≈N β].
    No native equality of the component functions or naturality witnesses
    is required. Hom equivalence laws therefore suffice to prove that
    [NatEq] is an equivalence relation. *)

(** 固定两端函子后，两个自然变换相等是指对应分量在 [D] 中逐点相等，记作
    [α ≈N β]。不要求分量函数或自然性见证的原生相等，因此仅用 Hom 等价律
    就能证明 [NatEq] 是等价关系。 *)

Definition NatEq {C D : Cat} {F G : Functor C D} (α β : F ⇒ G)
  := ∀ X, α X ≈ β X.

Infix "≈N" := NatEq
  (at level 50, no associativity).

(** [NatEq] is an equivalence relation. *)

(** [NatEq] 是等价关系。 *)

Program Instance NatEq_Equivalence {C D F G}
  : Equivalence (@NatEq C D F G).
Next Obligation. repeat intro. cato. Qed.
Next Obligation. repeat intro. symmetry. apply X. Qed.
Next Obligation. repeat intro. transitivity (y X1); auto. Qed.

(** Every component of the given natural transformation is invertible. *)

(** 给定自然变换的每个分量都可逆。 *)

Definition is_NatIso_of {C D : Cat} (F G : Functor C D)
    (α : F ⇒ G)
  : Type
  := ∀ X, is_iso (α X).

(** A natural isomorphism retains a transformation and, at each object,
    an inverse arrow with both inverse laws. The Type-valued existential
    stores these data. The inverse components form a natural transformation:
    their naturality is derived below, rather than supplied as another field.
    Thus [F ≅N G] compares functors by compatible isomorphisms of their images,
    without requiring equality of their object maps or law fields. *)

(** 自然同构保留一个自然变换，以及每个对象处分量的逆箭头和两条互逆定律。
    Type 值存在类型保存这些数据。逆分量也组成自然变换；其自然性由下文导出，
    无须作为额外字段提供。因此 [F ≅N G] 通过对象像之间相容的同构比较函子，
    不要求对象映射或定律字段相等。 *)

Definition NatIso {C D : Cat} (F G : Functor C D)
  := ∃ α : F ⇒ G, is_NatIso_of F G α.

Notation "α '⦂' F '≅N' G" := (is_NatIso_of F G α)
  (at level 50, no associativity,
    F at level 49, G at level 49) : cat_scope.

Infix "≅N" := NatIso
  (at level 50, no associativity) : cat_scope.

(** Invert each component; naturality follows from the original
    transformation. *)

(** 逐分量取逆，自然性由原变换导出。 *)

Program Definition NatIso_inv {C D : Cat} {F G : Functor C D}
    (α : F ⇒ G) (Niso : is_NatIso_of F G α)
  : G ⇒ F
  :=
  {|nt := λ X, (Niso X).1
  |}.
Next Obligation.
  pose (Hid := λ X, (Niso X).2).
  simpl in Hid.
  rewrite <- comp_id_r. cacr.
  rewrite <- (snd (Hid X)).
  cacl (fmap G f). rewrite <- nt_naturality.
  cacl. cacl. rewrite (fst (Hid Y)). carw.
Qed.

Notation "α '^-1N'" := (NatIso_inv α).

(** The inverse natural transformation also has invertible components. *)

(** 逆自然变换也具有可逆分量。 *)

Proposition NatIso_inv_NatIso {C D : Cat} {F G : Functor C D} (α : F ⇒ G)
    (Niso : α ⦂ F ≅N G)
  : (α ^-1N Niso) ⦂ G ≅N F.
Proof. intro X. exists (α X). apply is_inv_of_comm.
  simpl. apply (Niso X).2.
Defined.

(** The identity natural transformation. *)

(** 恒等自然变换。 *)

Program Instance nt_id {C D : Cat} {F : Functor C D}
  : F ⇒ F
  :=
  { nt _ := id }.
Next Obligation.
  rewrite comp_id_l.
  rewrite comp_id_r.
  reflexivity.
Qed.

(** Compose [β : F ⇒ G] followed by [α : G ⇒ H] at each object, giving
    the component [α X ∘ β X]. Naturality follows by applying the two
    naturality laws in sequence. This is vertical composition, written
    [α ∘Nv β]; it keeps the source and target categories fixed. *)

(** 将 [β : F ⇒ G] 与随后作用的 [α : G ⇒ H] 逐点复合，得到分量
    [α X ∘ β X]。依次使用两者的自然性即可证明复合的自然性。这称为垂直复合，
    记为 [α ∘Nv β]；整个过程保持源范畴和目标范畴不变。 *)

Program Instance nt_comp_v {C D : Cat} {F G H : Functor C D}
    (α : G ⇒ H) (β : F ⇒ G)
  : F ⇒ H
  :=
  { nt X := (α X) ∘ (β X) }.
Next Obligation.
  rewrite comp_assoc.
  rewrite (nt_naturality β f).
  rewrite <- (comp_assoc) at 1.
  rewrite (nt_naturality α f).
  rewrite comp_assoc.
  reflexivity.
Qed.

Notation idN := nt_id.

Infix "∘Nv" := nt_comp_v
  (at level 51, right associativity).



(** ** The Functor Category *)

(** ** 函子范畴 *)

(** The category [Fct C D] assembles functors and natural transformations.
    Its unit and associativity laws hold componentwise by the laws of [D].
    Equality of arrows here compares transformations, while isomorphism of
    objects compares functors. The later equivalence with componentwise
    natural isomorphism connects these two descriptions. *)

(** 函子范畴 [Fct C D] 将函子与自然变换组合起来。单位律和结合律逐分量由
    [D] 的对应定律得到。这里的箭头相等比较自然变换，对象同构则比较函子。
    下文证明它与逐分量定义的自然同构等价，从而连接这两种描述。 *)

Program Instance Fct (C D : Cat)
  : Cat
  :=
  (** Objects are functors from [C] to [D]. *)

  (** 对象是从 [C] 到 [D] 的函子。 *)

  { Ob := Functor C D
  (** The hom-set has natural transformations as its carrier and pointwise
      equality [NatEq] as its specified relation. *)

  (** Hom 广集以自然变换为载体，以逐点相等 [NatEq] 为指定关系。 *)

; HomSet F G :=
   {|carrier := F ⇒ G
   ; carrier_equiv := NatEq
   ; carrier_setoid := NatEq_Equivalence
   |}
  (** The identity transformation has an identity arrow at each object. *)

  (** 恒等自然变换在每个对象处的分量都是恒等箭头。 *)

; id _ := idN
  (** Composition is vertical composition, performed at each object. *)

  (** 复合是垂直复合，在每个对象处逐分量进行。 *)

; comp _ _ _ := nt_comp_v
}.
Next Obligation.
  intros a a' Ha b b' Hb O.
  simpl. rewrite (Ha O), (Hb O). cato.
Qed.
Next Obligation. intros O. simpl. cato. Qed.
Next Obligation. intros O. simpl. cato. Qed.
Next Obligation. intros O; simpl.
  rewrite comp_assoc. cato.
Qed.

(** Vertical composition preserves equality of natural transformations. *)

(** 垂直复合保持自然变换的相等。 *)

Global Instance nt_comp_v_proper {C D : Cat} {F G H : Functor C D}
  : Proper (NatEq ==> NatEq ==> NatEq) (@nt_comp_v C D F G H).
Proof.
  intros α α' Eα β β' Eβ X.
  exact (comp_proper (α X) (α' X) (Eα X) (β X) (β' X) (Eβ X)).
Qed.

(** ** Isomorphisms in a Functor Category

    Fix functors [F], [G] between [C] and [D]. Compare an isomorphism in their
    functor category with componentwise natural-isomorphism data. *)

(** ** 函子范畴中的同构

    固定 [C] 到 [D] 的函子 [F]、[G]，比较函子范畴中的同构与逐分量的自然同构数据。 *)

Section Fct.
Context {C D : Cat} {F G : Functor C D}.

(** Identify functor-category isomorphisms with componentwise natural
    isomorphisms. *)

(** 将函子范畴同构与逐分量自然同构对应。 *)

Theorem iso_NatIso
  : F ≅[Fct C D] G ↔ F ≅N G.
Proof. split.
  - intros (a & b & H1 & H2); simpl in *.
    exists a. intros X. exists (b X). simpl. split; cato.
  - intros [a H]. exists a. exists (a ^-1N H).
    split; simpl; intro X; apply (H X).2.
Qed.

End Fct.

(** View a natural isomorphism as an invertible functor-category morphism. *)

(** 将自然同构视为函子范畴中的可逆态射。 *)

Definition NatIso_is_iso {C D : Cat} {F G : Functor C D}
    (α : F ⇒ G) (Hα : α ⦂ F ≅N G)
  : @is_iso (Fct C D) F G α.
Proof.
  exists (α ^-1N Hα). split; intros X.
  - (* .unfold .all *)
    exact (fst (Hα X).2).
  - (* .unfold .all *)
    exact (snd (Hα X).2).
Defined.

(** An inverse in the functor category gives component inverses directly. *)

(** 函子范畴中的逆直接给出逐分量的逆。 *)

Definition is_iso_NatIso {C D : Cat} {F G : Functor C D}
    (α : F ⇒ G) (Hα : @is_iso (Fct C D) F G α)
  : α ⦂ F ≅N G.
Proof.
  intros X. exists (Hα.1 X). split.
  - exact ((fst Hα.2) X).
  - exact ((snd Hα.2) X).
Defined.

(** ** Functors Compared by Natural Isomorphism

    The comparison retains its natural transformation and component inverses.
    It imposes no Rocq equality on objects or on functor-law proofs. *)

(** ** 通过自然同构比较函子

    比较保留自然变换及各分量的逆，不要求对象或函子定律字段原生相等。 *)

Definition nt_id_NatIso {C D : Cat} (F : Functor C D)
  : idN ⦂ F ≅N F.
Proof. intros X. exists id. split; cbn; apply comp_id_l. Defined.

(** Vertical composition preserves invertibility of natural transformations. *)

(** 垂直复合保持自然变换的可逆性。 *)

Definition nt_comp_v_NatIso {C D : Cat} {F G H : Functor C D}
    (β : G ⇒ H) (α : F ⇒ G) (Hβ : β ⦂ G ≅N H) (Hα : α ⦂ F ≅N G)
  : (β ∘Nv α) ⦂ F ≅N H.
Proof.
  intros X. exists ((Hα X).1 ∘ (Hβ X).1). split; cbn.
  - rewrite comp_assoc, <- (comp_assoc (Hβ X).1), (fst (Hβ X).2), comp_id_l.
    exact (fst (Hα X).2).
  - rewrite comp_assoc, <- (comp_assoc (α X)), (snd (Hα X).2), comp_id_l.
    exact (snd (Hβ X).2).
Defined.

(** [NatIso] is an equivalence relation. *)

(** [NatIso] 是等价关系。 *)

Global Instance NatIso_Equivalence {C D : Cat}
  : Equivalence (@NatIso C D).
Proof.
  split.
  - intros F. exists idN. apply nt_id_NatIso.
  - intros F G [α Hα]. exists (α ^-1N Hα). apply NatIso_inv_NatIso.
  - intros F G H [α Hα] [β Hβ]. exists (β ∘Nv α).
    exact (nt_comp_v_NatIso β α Hβ Hα).
Defined.

(** Whiskering applies a functor to a natural transformation, or evaluates
    that transformation after another functor. *)

(** 须化将函子作用于自然变换，或将自然变换沿另一个函子求值。 *)

Program Definition nt_whisker_l {C D E : Cat} (G : Functor D E)
    {F F' : Functor C D} (α : F ⇒ F')
  : (G ∘F F) ⇒ (G ∘F F')
  :=
  {|nt X := fmap G (α X)
  |}.
Next Obligation.
  rewrite <- (@functor_comp D E G _ _ _ (α Y) (fmap F f)),
    <- (@functor_comp D E G _ _ _ (fmap F' f) (α X)).
  apply functor_fmap_proper. apply nt_naturality.
Qed.

(** Evaluate a natural transformation after a source functor. *)

(** 沿源函子求值自然变换。 *)

Program Definition nt_whisker_r {C D E : Cat} {G G' : Functor D E}
    (β : G ⇒ G') (F : Functor C D)
  : (G ∘F F) ⇒ (G' ∘F F)
  :=
  {|nt X := β (F X)
  |}.
Next Obligation. apply nt_naturality. Qed.

Infix "∘Nl" := nt_whisker_l (at level 51, right associativity) : cat_scope.
Infix "∘Nr" := nt_whisker_r (at level 51, right associativity) : cat_scope.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance nt_whisker_l_proper {C D E : Cat} (G : Functor D E)
    {F F' : Functor C D}
  : Proper (NatEq ==> NatEq) (@nt_whisker_l C D E G F F').
Proof.
  intros α β H X. change (fmap G (α X) ≈ fmap G (β X)).
  apply functor_fmap_proper. exact (H X).
Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance nt_whisker_r_proper {C D E : Cat} {G G' : Functor D E}
    (F : Functor C D)
  : Proper (NatEq ==> NatEq) (λ β : G ⇒ G', β ∘Nr F).
Proof. intros α β H X. exact (H (F X)). Qed.

(** Left whiskering preserves componentwise invertibility. *)

(** 左须化保持逐分量可逆性。 *)

Definition nt_whisker_l_NatIso {C D E : Cat} (G : Functor D E)
    {F F' : Functor C D} (α : F ⇒ F') (Hα : α ⦂ F ≅N F')
  : (G ∘Nl α) ⦂ (G ∘F F) ≅N (G ∘F F').
Proof. intros X. exact (functor_is_iso G (α X) (Hα X)). Defined.

(** Right whiskering preserves componentwise invertibility. *)

(** 右须化保持逐分量可逆性。 *)

Definition nt_whisker_r_NatIso {C D E : Cat} {G G' : Functor D E}
    (β : G ⇒ G') (F : Functor C D) (Hβ : β ⦂ G ≅N G')
  : (β ∘Nr F) ⦂ (G ∘F F) ≅N (G' ∘F F).
Proof. intros X. exact (Hβ (F X)). Defined.

(** ** Horizontal Composition *)

(** ** 水平复合 *)

(** Horizontal composition obtained from whiskering and vertical composition. *)

(** 由须化与垂直复合构造水平复合。 *)

Definition nt_comp_h {C D E : Cat} {G G' : Functor D E} {F F' : Functor C D}
    (β : G ⇒ G') (α : F ⇒ F')
  : (G ∘F F) ⇒ (G' ∘F F')
  := (β ∘Nr F') ∘Nv (G ∘Nl α).

Infix "∘Nh" := nt_comp_h (at level 50, left associativity) : cat_scope.

(** The two whiskering orders give equal horizontal composites. *)

(** 两种须化次序给出相等的水平复合。 *)

Theorem nt_comp_h_alt {C D E : Cat} {G G' : Functor D E} {F F' : Functor C D}
    (β : G ⇒ G') (α : F ⇒ F')
  : (β ∘Nh α) ≈N ((G' ∘Nl α) ∘Nv (β ∘Nr F)).
Proof. intros X. exact (nt_naturality β (α X)). Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance nt_comp_h_proper {C D E : Cat}
    {G G' : Functor D E} {F F' : Functor C D}
  : Proper (NatEq ==> NatEq ==> NatEq) (@nt_comp_h C D E G G' F F').
Proof.
  intros β β' Hβ α α' Hα X.
  change (β (F' X) ∘ fmap G (α X) ≈ β' (F' X) ∘ fmap G (α' X)).
  apply comp_proper; [apply Hβ | apply functor_fmap_proper; apply Hα].
Qed.

(** Compatibility with identities for [nt_comp_h]. *)

(** [nt_comp_h] 与恒等的相容性。 *)

Theorem nt_comp_h_id {C D E : Cat} (G : Functor D E) (F : Functor C D)
  : (idN (F := G) ∘Nh idN (F := F)) ≈N idN.
Proof.
  intros X. change (id ∘ fmap G (@id (F X)) ≈ @id (G (F X))).
  rewrite functor_id. apply comp_id_l.
Qed.

(** Horizontal and vertical composition satisfy the interchange law. *)

(** 水平与垂直复合满足交换律。 *)

Theorem nt_comp_h_interchange {C D E : Cat}
    {G0 G1 G2 : Functor D E} {F0 F1 F2 : Functor C D}
    (β2 : G1 ⇒ G2) (β1 : G0 ⇒ G1) (α2 : F1 ⇒ F2) (α1 : F0 ⇒ F1)
  : ((β2 ∘Nv β1) ∘Nh (α2 ∘Nv α1)) ≈N
      ((β2 ∘Nh α2) ∘Nv (β1 ∘Nh α1)).
Proof.
  intros X.
  change ((β2 (F2 X) ∘ β1 (F2 X)) ∘ fmap G0 (α2 X ∘ α1 X) ≈
    (β2 (F2 X) ∘ fmap G1 (α2 X)) ∘ (β1 (F1 X) ∘ fmap G0 (α1 X))).
  rewrite functor_comp, !comp_assoc.
  rewrite <- (comp_assoc (β1 (F2 X))), (nt_naturality β1 (α2 X)).
  rewrite comp_assoc. reflexivity.
Qed.

(** Horizontal composition is a functor on the two hom-categories. *)

(** 水平复合是两个 Hom 范畴上的函子。 *)

Program Definition CompNF (C D E : Cat)
  : Functor (Fct D E ×C Fct C D) (Fct C E)
  :=
  {|F0 p := fst p ∘F snd p
  ; F1 p q α := fst α ∘Nh snd α
  |}.
Next Obligation.
  intros [β α] [β' α'] [Hβ Hα].
  exact (nt_comp_h_proper β β' Hβ α α' Hα).
Defined.
Next Obligation. apply nt_comp_h_id. Defined.
Next Obligation. apply nt_comp_h_interchange. Defined.

(** Horizontal composition preserves natural isomorphisms. *)

(** 水平复合保持自然同构。 *)

Definition nt_comp_h_NatIso {C D E : Cat}
    {G G' : Functor D E} {F F' : Functor C D}
    (β : G ⇒ G') (α : F ⇒ F') (Hβ : β ⦂ G ≅N G') (Hα : α ⦂ F ≅N F')
  : (β ∘Nh α) ⦂ (G ∘F F) ≅N (G' ∘F F').
Proof.
  apply nt_comp_v_NatIso.
  - exact (nt_whisker_r_NatIso β F' Hβ).
  - exact (nt_whisker_l_NatIso G α Hα).
Defined.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance CompF_proper {C D E : Cat}
  : Proper (NatIso ==> NatIso ==> NatIso) (@CompF C D E).
Proof.
  intros G G' [β Hβ] F F' [α Hα].
  exists (β ∘Nh α). exact (nt_comp_h_NatIso β α Hβ Hα).
Defined.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance π1F_proper {C D E : Cat} (d : @Ob D)
  : Proper (NatIso ==> NatIso) (λ F : Functor (C ×C D) E, π1F F d).
Proof.
  intros F G [α Hα].
  unshelve notypeclasses refine (({|nt := _
                                  |}); _).
  - exact (λ c, α (c, d)).
  - intros X Y f. exact (nt_naturality α (X := (X, d)) (Y := (Y, d)) (f, id)).
  - intros X. exact (Hα (X, d)).
Defined.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance π2F_proper {C D E : Cat} (c : @Ob C)
  : Proper (NatIso ==> NatIso) (λ F : Functor (C ×C D) E, π2F F c).
Proof.
  intros F G [α Hα].
  unshelve notypeclasses refine (({|nt := _
                                  |}); _).
  - exact (λ d, α (c, d)).
  - intros X Y f. exact (nt_naturality α (X := (c, X)) (Y := (c, Y)) (id, f)).
  - intros X. exact (Hα (c, X)).
Defined.

(** The comparison components for the functor laws are identities, even when
    the functor records have different proof fields. *)

(** 即使函子记录包含不同证明字段，函子律的比较分量仍是恒等态射。 *)

Program Definition CompF_id_l {C D : Cat} (F : Functor C D)
  : IdF ∘F F ≅N F
  := ({|nt X := id
      |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation. intros X. exists id. split; cbn; apply comp_id_l. Defined.

(** Right identity law for [CompF]. *)

(** [CompF] 右单位律。 *)

Program Definition CompF_id_r {C D : Cat} (F : Functor C D)
  : F ∘F IdF ≅N F
  := ({|nt X := id
      |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation. intros X. exists id. split; cbn; apply comp_id_l. Defined.

(** Associativity law for [CompF]. *)

(** [CompF] 结合律。 *)

Program Definition CompF_assoc {B C D E : Cat}
    (H : Functor D E) (G : Functor C D) (F : Functor B C)
  : (H ∘F G) ∘F F ≅N H ∘F (G ∘F F)
  := ({|nt X := id
      |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation. intros X. exists id. split; cbn; apply comp_id_l. Defined.

(** ** Opposite Natural Transformations

    Components keep their underlying morphisms. Their direction, and the order
    of vertical composition, are reversed in the opposite category. *)

(** ** 反自然变换

    分量保留底层态射，但其方向和垂直复合的次序在反范畴中反转。 *)

Program Definition nt_op {C D : Cat} {F G : Functor C D} (α : F ⇒ G)
  : G^opF ⇒ F^opF
  :=
  {|nt X := α X
  |}.
Next Obligation. symmetry. exact (nt_naturality α f). Qed.

Notation "α '^opN'" := (nt_op α) (at level 35) : cat_scope.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance nt_op_proper {C D : Cat} {F G : Functor C D}
  : Proper (NatEq ==> NatEq) (@nt_op C D F G).
Proof. intros α β Hαβ X. exact (Hαβ X). Qed.

(** Compatibility with identities for [nt_op]. *)

(** [nt_op] 与恒等的相容性。 *)

Theorem nt_op_id {C D : Cat} {F : Functor C D}
  : (idN (F := F))^opN ≈N idN.
Proof. intros X. reflexivity. Qed.

(** Compatibility with vertical composition for [nt_op]. *)

(** [nt_op] 与垂直复合的相容性。 *)

Theorem nt_op_comp_v {C D : Cat} {F G H : Functor C D}
    (β : G ⇒ H) (α : F ⇒ G)
  : (β ∘Nv α) ^opN ≈N (α ^opN ∘Nv β ^opN).
Proof. intros X. reflexivity. Qed.

(** Taking opposites as a functor between the corresponding functor
    categories. *)

(** 将取反组织为对应函子范畴之间的函子。 *)

Program Definition OpFctF {C D : Cat}
  : Functor ((Fct C D) ^op) (Fct (C ^op) (D ^op))
  :=
  {|F0 F := F^opF
  ; F1 F G α := α^opN
  |}.
Next Obligation. apply nt_op_id. Qed.
Next Obligation. apply nt_op_comp_v. Qed.

(** Taking opposites preserves natural isomorphisms. *)

(** 取反保持自然同构。 *)

Definition nt_op_NatIso {C D : Cat} {F G : Functor C D}
    (α : F ⇒ G) (Hα : α ⦂ F ≅N G)
  : α ^opN ⦂ G^opF ≅N F^opF.
Proof.
  intros X. exists (Hα X).1. split.
  - exact (snd (Hα X).2).
  - exact (fst (Hα X).2).
Defined.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance OpF_proper {C D : Cat}
  : Proper (NatIso ==> NatIso) (@OpF C D).
Proof.
  intros F G [α Hα]. symmetry. exists (α ^opN). exact (nt_op_NatIso α Hα).
Defined.

(** Compatibility with identities for [OpF]. *)

(** [OpF] 与恒等的相容性。 *)

Program Definition OpF_id {C : Cat}
  : (@IdF C)^opF ≅N (@IdF (C ^op))
  := ({|nt X := id
      |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation.
  intros X. exists id. split; exact (@comp_id_l C X X (@Cats.Cat.Core.id C X)).
Defined.

(** Compatibility with composition for [OpF]. *)

(** [OpF] 与复合的相容性。 *)

Program Definition OpF_comp {C D E : Cat} (G : Functor D E) (F : Functor C D)
  : (G ∘F F)^opF ≅N (G^opF ∘F F^opF)
  := ({|nt X := id
      |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation.
  intros X. exists id. split;
    exact (@comp_id_l E (G (F X)) (G (F X)) (@Cats.Cat.Core.id E (G (F X)))).
Defined.

(** A natural isomorphism compares double opposition with the original
    functor. *)

(** 通过自然同构比较双重取反与原函子。 *)

Program Definition OpF_involution {C D : Cat} (F : Functor C D)
  : FromDoubleOpF ∘F (F^opF^opF ∘F ToDoubleOpF) ≅N F
  := ({|nt X := id
      |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation. intros X. exists id. split; cbn; apply comp_id_l. Defined.

(** Opposing a functor read in the original categories recovers the given
    functor by an identity-component natural isomorphism. *)

(** 将读回原范畴的函子再取反，通过恒等分量自然同构恢复给定函子。 *)

Program Definition OpUnopF {C D : Cat} (F : Functor (C^op) (D^op))
  : (F^unopF)^opF ≅N F
  := ({|nt X := id
      |}; _).
Next Obligation. cbn. carw. Defined.
Next Obligation.
  intros X. exists id. split;
    exact (@comp_id_l (D^op) (F X) (F X) (@Cat.Core.id (D^op) (F X))).
Defined.
