From Cats Require Import
  Cat.Core
  Cat.Terminal.



(** * Morphisms *)

(** * 态射 *)

Section Morphism.
Context {C : Cat}.

(** ** Monomorphisms

    An arrow [f : Hom Y Z] is monic when it can be cancelled on the left
    of a composite: [f ∘ x ≈ f ∘ y] implies [x ≈ y]. The test arrows
    [x] and [y] may start at any common object [X]. This describes
    distinguishability by arrows, without requiring elements of objects.

    Cancellation implies its contrapositive constructively. The converse does
    not follow in general without additional assumptions, so the two
    properties are kept distinct. Use the weakest sufficient assumption.

    Similar definitions are provided for epimorphisms. *)

(** ** 单态射

    若 [f : Hom Y Z] 可从复合的左侧消去，即 [f ∘ x ≈ f ∘ y] 推出 [x ≈ y]，
    则称 [f] 为单态射。测试箭头 [x]、[y] 可以从任意共同对象 [X] 出发。
    这个定义用箭头描述可区分性，不要求对象具有元素。

    消去性质构造性地推出其逆否形式；一般情况下，反方向需要额外假设，故两种性质
    分开并使用最弱的充分假设。满态射也有类似定义。 *)

Definition is_mono {Y Z} (f : Hom Y Z)
  := ∀ X, ∀ x y : Hom X Y, f ∘ x ≈ f ∘ y → x ≈ y.

(** Distinct parallel inputs remain distinct after postcomposition. *)

(** 后合成后，不同的平行输入仍然不同。 *)

Definition is_mono_contrapositive {Y Z} (f : Hom Y Z)
  := ∀ X, ∀ x y : Hom X Y, x ≉ y → f ∘ x ≉ f ∘ y.

(** Left cancellation implies preservation of inequality constructively. *)

(** 左消去构造性地推出保持不相等。 *)

Proposition mono_implies_contrapositive {Y Z} (f : Hom Y Z)
  : is_mono f → is_mono_contrapositive f.
Proof. firstorder. Qed.

(** An identity arrow is monic. *)

(** 恒等箭头是单态射。 *)

Proposition mono_id {X}
  : is_mono (@id X).
Proof. intros Y x y Heq.
  rewrite comp_id_l in Heq.
  rewrite comp_id_l in Heq. auto.
Qed.

(** A composite of monomorphisms is monic. *)

(** 单态射的复合仍为单态射。 *)

Proposition mono_comp {X Y Z} (f : Hom X Y) (g : Hom Y Z)
  : is_mono f → is_mono g → is_mono (g ∘ f).
Proof. intros Hf Hg W x y Heq.
  apply Hf. apply Hg.
  repeat rewrite <- comp_assoc. auto.
Qed.

(** The contrapositive mono property is closed under composition. *)

(** 单态射的逆否性质在复合下封闭。 *)

Proposition mono_contrapositive_comp {X Y Z} (f : Hom X Y) (g : Hom Y Z)
  : is_mono_contrapositive f → is_mono_contrapositive g
    → is_mono_contrapositive (g ∘ f).
Proof. intros Hf Hg W x y Hneq.
  repeat rewrite comp_assoc.
  apply Hg. apply Hf. auto.
Qed.

(* TODO: contrapositive version of left cancellation. *)

(** If a composite is monic, its first-applied factor is monic. *)

(** 复合为单态射时，先作用的因子也是单态射。 *)

Proposition mono_cancel_l {X Y Z} (f : Hom X Y) (g : Hom Y Z)
  : is_mono (g ∘ f) → is_mono f.
Proof. intros Hgf W x y Hf.
  apply (comp_l g) in Hf. apply Hgf.
  repeat rewrite comp_assoc. auto.
Qed.

(** Every invertible arrow is monic. *)

(** 每条可逆箭头都是单态射。 *)

Proposition iso_mono {X Y} (f : Hom X Y)
  : is_iso f → is_mono f.
Proof. intros [fi [H1 H2]] Z x y H.
  apply (comp_l fi) in H.
  repeat rewrite <- comp_assoc in H.
  repeat rewrite H1 in H.
  repeat rewrite comp_id_l in H. auto.
Qed.



(** An arrow bundled with its left-cancellation property. *)

(** 箭头及其左消去性质的组合。 *)

Record Mono (X Y : Ob)
  :=
  { mor :> Hom X Y
  ; mor_mono : is_mono mor
  }.

Notation "X ↣ Y" := (Mono X Y)
  (at level 35, no associativity) : cat_scope.

(** The identity arrow bundled as a monomorphism. *)

(** 将恒等箭头组合为单态射。 *)

Program Canonical Mono_id {X}
  :=
  {|mor := @id X
  |}.
Next Obligation. apply mono_id. Qed.

(** Compose two bundled monomorphisms. *)

(** 复合两个组合单态射。 *)

Program Canonical Mono_comp {X Y Z} (f : Y ↣ Z) (g : X ↣ Y)
  :=
  {|mor := f ∘ g
  |}.
Next Obligation. apply mono_comp.
  apply mor_mono. apply mor_mono.
Qed.

(** An arrow from a terminal object is monic. *)

(** 从终对象出发的箭头是单态射。 *)

Program Canonical Mono_term `{HT : !HasTerminal C} {X} (f : Hom 1 X)
  :=
  {|mor := f
  |}.
Next Obligation. intros Y x y _.
  rewrite term_η. rewrite (term_η y). reflexivity.
Qed.

(** An arrow factors through another with a retained factorization witness. *)

(** 箭头经过另一条箭头分解，并保留分解见证。 *)

Definition is_factored_through {X Y Z} (g : Hom Y Z) (f : Hom X Z)
  := ∃ h, f ≈ g ∘ h.

(** Monic arrows factoring through each other have isomorphic domains. *)

(** 彼此分解的单态射具有同构定义域。 *)

Proposition iso_by_factor {X Y Z} {f : X ↣ Z} {g : Y ↣ Z}
  : is_factored_through g f → is_factored_through f g
  → X ≅ Y.
Proof. intros [h1 H1] [h2 H2].
  exists h1, h2. split; simpl.
  assert (f ∘ (h2 ∘ h1) ≈ f ∘ id).
  { cacl. rewrite <- H2, H1. cato. }
  eapply mor_mono. eauto.
  assert (g ∘ (h1 ∘ h2) ≈ g ∘ id).
  { cacl. rewrite <- H1, H2. cato. }
  eapply mor_mono. eauto.
Qed.



(** *** Sub-Objects *)

(** *** 子对象 *)

(** An object together with a monomorphism into the ambient object. *)

(** 对象及其指向环境对象的单态射。 *)

Record Sub (X : Ob)
  :=
  { sub : Ob
  ; sub_mono :> sub ↣ X
  }.

(** The domain object of a bundled monomorphism. *)

(** 组合单态射的定义域对象。 *)

Definition object_of_Sub {X Y} (f : X ↣ Y)
  := X.
Coercion object_of_Sub : Mono >-> Ob.

(** The largest subobject, represented by the identity monomorphism. *)

(** 由恒等单态射表示的最大子对象。 *)

Program Canonical id_Sub {X : Ob}
  : Sub X
  :=
  {|sub := X
  ; sub_mono := Mono_id
  |}.

(** A global point regarded as a subobject. *)

(** 将全局点视为子对象。 *)

Program Canonical term_Sub
    `{HT : !HasTerminal C} {X : Ob} (f : Hom 1 X)
  : Sub X
  :=
  {|sub := 1
  ; sub_mono := f
  |}.

(** The subobject preorder given by factorization. *)

(** 由分解给出的子对象预序。 *)

Definition Sub_le Z (i j : Sub Z)
  := is_factored_through j i.

Infix "≲Sub" := (Sub_le _)
  (at level 50, no associativity) : cat_scope.

Infix "≲Sub[ Z  ]" := (Sub_le Z)
  (at level 50, no associativity) : cat_scope.

(** Subobject equivalence means mutual factorization. *)

(** 子对象等价就是相互分解。 *)

Definition Sub_eq Z (i j : Sub Z)
  := i ≲Sub j ∧ j ≲Sub i.

Infix "~Sub" := (Sub_eq _)
  (at level 50, no associativity) : cat_scope.

Infix "~Sub[ Z  ]" := (Sub_eq Z)
  (at level 50, no associativity) : cat_scope.

(** [Sub_le] is reflexive. *)

(** [Sub_le] 是自反的。 *)

Global Program Instance Sub_le_Reflexive {Z}
  : Reflexive (Sub_le Z).
Next Obligation. exists id. cato. Qed.

(** [Sub_le] is transitive. *)

(** [Sub_le] 是传递的。 *)

Global Program Instance Sub_le_Transitive {Z}
  : Transitive (Sub_le Z).
Next Obligation. destruct X as [g Hg]. destruct X0 as [h Hh].
  exists (h ∘ g).
  rewrite <- comp_assoc.
  rewrite Hg. rewrite Hh. cato.
Qed.

(** [Sub_le] is a preorder. *)

(** [Sub_le] 是预序。 *)

Global Program Instance Sub_le_PreOrder {Z}
  : PreOrder (Sub_le Z).

(** Sub_eq is [Equivalence] *)

(** [Sub_eq] 是 [Equivalence]。 *)

Global Program Instance Sub_eq_Reflexive {Z}
  : Reflexive (Sub_eq Z).
Next Obligation. split; reflexivity. Qed.

(** [Sub_eq] is symmetric. *)

(** [Sub_eq] 是对称的。 *)

Global Program Instance Sub_eq_Symmetric {Z}
  : Symmetric (Sub_eq Z).
Next Obligation. destruct X. split; auto. Qed.

(** [Sub_eq] is transitive. *)

(** [Sub_eq] 是传递的。 *)

Global Program Instance Sub_eq_Transitive {Z}
  : Transitive (Sub_eq Z).
Next Obligation. destruct X, X0. split; transitivity y; auto. Qed.

(** [Sub_eq] is an equivalence relation. *)

(** [Sub_eq] 是等价关系。 *)

Global Program Instance Sub_eq_Equivalence {Z}
  : Equivalence (Sub_eq Z).

(** The factor between two subobjects is monic. *)

(** 两个子对象之间的分解映射为单态射。 *)

Proposition Sub_le_Mono {Z} {i j : Sub Z}
  : i ≲Sub j → ∃ k : Hom i j, is_mono k.
Proof. intros [h H].
  assert (Hmi : is_mono (j ∘ h)).
  { intros W x y H1. rewrite <- H in H1.
    apply sub_mono. auto. }
  assert (Hmh : is_mono h).
  { eapply mono_cancel_l. eauto. }
  exists {|sub := i
         ; sub_mono :=
{|mor := h
; mor_mono := Hmh
|}
         |}.
  auto.
Qed.

(** Equivalent subobjects have isomorphic representing domains. *)

(** 等价子对象具有同构的表示定义域。 *)

Proposition iso_by_Sub_eq {Z} {i j : Sub Z}
  : i ~Sub j → i ≅ j .
Proof. intros [H1 H2]. eapply iso_by_factor; eauto. Qed.



(** ** Epimorphisms

    Cancellation and its contrapositive are distinguished as for
    monomorphisms. *)

(** ** 满态射

    与单态射一样，消去性质与其逆否形式分开。 *)

Definition is_epi {X Y} (f : Hom X Y)
  := ∀ Z, ∀ x y : Hom Y Z, x ∘ f ≈ y ∘ f → x ≈ y.

(** Distinct parallel outputs remain distinct after precomposition. *)

(** 预合成后，不同的平行输出仍然不同。 *)

Definition is_epi_contrapositive {X Y} (f : Hom X Y)
  := ∀ Z, ∀ x y : Hom Y Z, x ≉ y → x ∘ f ≉ y ∘ f.

(** Right cancellation implies its contrapositive constructively. *)

(** 右消去构造性地推出其逆否形式。 *)

Proposition epi_implies_contrapositive {X Y} (f : Hom X Y)
  : is_epi f → is_epi_contrapositive f.
Proof. firstorder. Qed.

End Morphism.



Arguments is_factored_through {_ _ _ _} _ _ /.
Arguments sub {_ _} _.

Notation "X '↣' Y" := (Mono X Y)
  (at level 35, no associativity) : cat_scope.

Notation "X '⊆' Z" := (X : Sub Z)
  (at level 50) : cat_scope.

Infix "≲Sub" := (Sub_le _)
  (at level 50, no associativity) : cat_scope.

Infix "≲Sub[ Z  ]" := (Sub_le Z)
  (at level 50, no associativity) : cat_scope.

Infix "~Sub" := (Sub_eq _)
  (at level 50, no associativity) : cat_scope.

Infix "~Sub[ Z  ]" := (Sub_eq Z)
  (at level 50, no associativity) : cat_scope.
