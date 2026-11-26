From Cats.Set Require Import
  Subset.
From Cats Require Export
  Cat.Monoidal.Monoidal.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Monoid Objects

    Multiplication uses the selected tensor, not an implicit categorical
    product. All diagrams use designated hom equality and explicitly retain
    the associator and unitors. The carrier and operations are stored data;
    no equality of the law witnesses is requested. *)

(** * 幺半群对象

    乘法使用选定张量，不默认为范畴积。全部图表使用指定 Hom 相等，并显式保留
    结合子和单位子。载体及运算作为数据保存，不要求定律见证相等。 *)

(** The monoid laws for fixed carrier, unit and multiplication. This
    predicate compares presentations without quantifying over packages
    whose data could differ. *)

(** 固定载体、单位和乘法上的幺半群定律；此谓词可比较不同呈现，而不必量化
    数据可能不同的完整结构包。 *)

Minks.Mixin IsMonoidObj {C : Cat}
    `{MC : HasMonoidal C}
    (A : C) (e : Hom 𝐈 A) (m : Hom (A ⊗ A) A)
  :=
  { monoid_obj_unit_l : m ∘ (e ⊗ id) ≈ λ[A]
  ; monoid_obj_unit_r : m ∘ (id ⊗ e) ≈ ρ[A]
  ; monoid_obj_assoc
    : m ∘ (m ⊗ id) ≈ m ∘ (id ⊗ m) ∘ α[A; A; A]
  }.

Arguments monoid_obj_unit_l {_ _ _ _ _} _.
Arguments monoid_obj_unit_r {_ _ _ _ _} _.
Arguments monoid_obj_assoc {_ _ _ _ _} _.

(** Choose a unit and multiplication on [A] and verify their diagrams. *)

(** 在 [A] 上选定单位和乘法，并验证它们的交换图。 *)

Minks.Mixin HasMonoidObj {C : Cat}
    `{MC : HasMonoidal C} (A : C)
  :=
  { monoid_obj_unit : Hom 𝐈 A
  ; monoid_obj_mul : Hom (A ⊗ A) A
  ; isMonoidObj
    :: IsMonoidObj A monoid_obj_unit monoid_obj_mul
  }.

Arguments monoid_obj_unit {_ _} _ {_}.
Arguments monoid_obj_mul {_ _} _ {_}.
Arguments isMonoidObj {_ _} _ {_}.

(** A monoid object bundles its carrier with the selected monoid structure. *)

(** 幺半群对象打包一个载体对象及其上选定的幺半群结构。 *)

Minks.Struct MonoidObj (C : Cat)
    `{MC : HasMonoidal C}
  extends @Ob C
  with  hasMonoidObj as hasMonoidObj
    : HasMonoidObj [C, MC, carrier].

Arguments MonoidObjToOb {_ _} _.
Arguments MakeMonoidObj {_ _} _ _.
Arguments hasMonoidObj {_ _} _.

Notation "'e[' A ']'"
  := (@monoid_obj_unit _ _ _ (hasMonoidObj A))
  (at level 0)
  : monoidal_scope.
Notation "'m[' A ']'"
  := (@monoid_obj_mul _ _ _ (hasMonoidObj A))
  (at level 0)
  : monoidal_scope.

(** ** Homomorphisms of Monoid Objects

    Fix a monoidal structure [MC] on [C]. Define homomorphisms by preservation
    of unit and multiplication, compare their underlying arrows, and construct
    identity and composite homomorphisms. *)

(** ** 幺半群对象的同态

    固定 [C] 上的幺半结构 [MC]，以保持单位和乘法定义同态，比较底层箭头，并构造恒等与复合同态。 *)

Section MonoidMorphisms.
Context {C : Cat} `{MC : HasMonoidal C}.

(** A homomorphism preserves the unit and multiplication. The commuting
    diagrams are Type-valued evidence, not an equality of structure records. *)

(** 同态保持单位和乘法；交换图表是 Type 值证据，不是结构记录的相等。 *)

Definition is_monoid_hom (A B : MonoidObj C)
    (f : Hom A B)
  : Type
  := f ∘ e[A] ≈ e[B] ∧ f ∘ m[A] ≈ m[B] ∘ (f ⊗ f).

(** Equal arrows satisfy the same homomorphism diagrams. *)

(** 相等箭头满足相同的同态交换方程。 *)

Lemma monoid_hom_equiv (A B : MonoidObj C)
    (f g : Hom A B) (E : f ≈ g)
  : is_monoid_hom A B f ↔ is_monoid_hom A B g.
Proof.
  split; intros [Hu Hm]; split.
  - rewrite <- E. exact Hu.
  - rewrite <- E. exact Hm.
  - rewrite E. exact Hu.
  - rewrite E. exact Hm.
Qed.

(** Homomorphisms form a subset of the underlying hom-set. Their equality
    compares the arrows only; preservation witnesses remain stored and are
    not identified by proof irrelevance. *)

(** 同态组成底层 Hom 广集的子集，相等只比较箭头；保持性见证仍然保存，并未
    通过证明无关性将它们等同。 *)

Definition MonoidHomS (A B : MonoidObj C)
  : SetC
  := SubsetS (HomSet A B) (is_monoid_hom A B).

(** The identity arrow preserves both operations. *)

(** 恒等箭头保持两个运算。 *)

Definition monoid_hom_id (A : MonoidObj C)
  : MonoidHomS A A.
Proof.
  exists id. split; [apply comp_id_l |].
  rewrite tensor_map_id, comp_id_r. apply comp_id_l.
Defined.

(** Composition preserves the operations by tensor bifunctoriality. *)

(** 由张量双函子性，复合保持两个运算。 *)

Definition monoid_hom_comp {A B D : MonoidObj C}
    (g : MonoidHomS B D) (f : MonoidHomS A B)
  : MonoidHomS A D.
Proof.
  exists (g.1 ∘ f.1).
  destruct f as [f [Hfe Hfm]], g as [g [Hge Hgm]].
  cbn. split.
  - rewrite comp_assoc, Hfe. exact Hge.
  - rewrite comp_assoc, Hfm,
      <- comp_assoc, Hgm, comp_assoc.
    rewrite <- tensor_map_comp. reflexivity.
Defined.

End MonoidMorphisms.

(** ** The Category of Monoid Objects

    Fix a category [C] with a chosen monoidal structure. Assemble its monoid
    objects into a category and define the faithful forgetful functor. *)

(** ** 幺半群对象范畴

    固定范畴 [C] 及其选定的幺半结构，将其幺半群对象组装为范畴，并定义忠实的忘却函子。 *)

Section MonoidCategories.

(** The category of monoid objects and operation-preserving arrows.
    Its hom equality is inherited from [C]. The object universe [o] is
    independent of the bound [s] used by the chosen monoidal structure. *)

(** 幺半群对象及保持运算箭头组成的范畴。Hom 相等继承自 [C]；
    对象宇宙 [o] 与选定幺半结构使用的界 [s] 相互独立。 *)

Program Definition MonoidCat@{s o +} (C : Cat)
    `{MC : !HasMonoidal@{_ _ _ _ s _ _ _} C}
  : Cat@{o _ _ _ _}
  :=
  {|Ob := MonoidObj C
  ; HomSet := MonoidHomS
  ; id := monoid_hom_id
  ; comp _ _ _ := monoid_hom_comp
  |}.
Next Obligation.
  intros [g Hg] [g' Hg'] Eg [f Hf] [f' Hf'] Ef.
  exact (comp_proper g g' Eg f f' Ef).
Qed.
Next Obligation. exact (comp_id_r f.1). Qed.
Next Obligation. exact (comp_id_l f.1). Qed.
Next Obligation. exact (comp_assoc f.1 g.1 h.1). Qed.

Context (C : Cat) `{MC : !HasMonoidal C}.

(** Forget a monoid's operations and a homomorphism's preservation proofs. *)

(** 忘却幺半群的运算及同态的保持性证明。 *)

Program Definition MonoidForgetF
  : Fct (MonoidCat C) C
  :=
  {|fobj A := A
  ; fmap A B f := f.1
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros f g H. exact H. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** Forgetting a homomorphism is faithful because equality already compares
    only its underlying arrow. *)

(** 同态的相等本就只比较底层箭头，因此忘却函子忠实。 *)

Lemma monoid_forget_faithful
  : is_faithful MonoidForgetF.
Proof. intros A B f g H. exact H. Qed.

End MonoidCategories.
