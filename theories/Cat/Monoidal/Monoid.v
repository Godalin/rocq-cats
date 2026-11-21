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

Minks.Mixin IsMonoidObj {C : Cat} (MC : HasMonoidal C)
    (A : @Ob C) (e : Hom (𝐈[MC]) A) (m : Hom (A ⊗ A) A)
  : Type
  :=
  { monoid_object_unit_l : m ∘ (e ⊗ id) ≈ λ[A]
  ; monoid_object_unit_r : m ∘ (id ⊗ e) ≈ ρ[A]
  ; monoid_object_assoc
    : m ∘ (m ⊗ id) ≈ m ∘ (id ⊗ m) ∘ α[A; A; A]
  }.

Arguments monoid_object_unit_l {_ _ _ _ _} _.
Arguments monoid_object_unit_r {_ _ _ _ _} _.
Arguments monoid_object_assoc {_ _ _ _ _} _.

(** A chosen carrier and operations satisfying the monoid diagrams.
    Coercion exposes the carrier object in the ambient category. *)

(** 满足幺半群交换图表的选定载体及运算；强制转换暴露所在范畴中的载体对象。 *)

Class MonoidObj {C : Cat} (MC : HasMonoidal C)
  :=
  { MonoidCarrier :> @Ob C
  ; monoid_object_unit : Hom (𝐈[MC]) MonoidCarrier
  ; monoid_object_mul : Hom (MonoidCarrier ⊗ MonoidCarrier) MonoidCarrier
  ; isMonoidObj
    :: IsMonoidObj MC MonoidCarrier monoid_object_unit monoid_object_mul
  }.

Arguments MonoidCarrier {_ _} _.
Arguments monoid_object_unit {_ _} _.
Arguments monoid_object_mul {_ _} _.
Arguments isMonoidObj {_ _} _.

Notation "'e[' A ']'" := (monoid_object_unit A) : monoidal_scope.
Notation "'m[' A ']'" := (monoid_object_mul A) : monoidal_scope.

(** ** Homomorphisms of Monoid Objects

    Fix a monoidal structure [MC] on [C]. Define homomorphisms by preservation
    of unit and multiplication, compare their underlying arrows, and construct
    identity and composite homomorphisms. *)

(** ** 幺半群对象的同态

    固定 [C] 上的幺半结构 [MC]，以保持单位和乘法定义同态，比较底层箭头，并构造恒等与复合同态。 *)

Section MonoidMorphisms.
Context {C : Cat} {MC : HasMonoidal C}.

(** A homomorphism preserves the unit and multiplication. The commuting
    diagrams are Type-valued evidence, not an equality of structure records. *)

(** 同态保持单位和乘法；交换图表是 Type 值证据，不是结构记录的相等。 *)

Definition is_monoid_hom (A B : MonoidObj MC)
    (f : Hom (MonoidCarrier A) (MonoidCarrier B))
  : Type
  := f ∘ e[A] ≈ e[B] ∧ f ∘ m[A] ≈ m[B] ∘ (f ⊗ f).

(** Equal arrows satisfy the same homomorphism diagrams. *)

(** 相等箭头满足相同的同态交换方程。 *)

Lemma monoid_hom_equiv (A B : MonoidObj MC)
    (f g : Hom (MonoidCarrier A) (MonoidCarrier B))
    (E : f ≈ g)
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

Definition MonoidHomS (A B : MonoidObj MC)
  : SetC
  := SubsetS (HomSet (MonoidCarrier A) (MonoidCarrier B))
      (is_monoid_hom A B).

(** The identity arrow preserves both operations. *)

(** 恒等箭头保持两个运算。 *)

Definition monoid_hom_id (A : MonoidObj MC)
  : MonoidHomS A A.
Proof.
  exists id. split; [apply comp_id_l |].
  rewrite tensor_map_id, comp_id_r. apply comp_id_l.
Defined.

(** Composition preserves the operations by tensor bifunctoriality. *)

(** 由张量双函子性，复合保持两个运算。 *)

Definition monoid_hom_comp {A B D : MonoidObj MC}
    (g : MonoidHomS B D) (f : MonoidHomS A B)
  : MonoidHomS A D.
Proof.
  exists (g.1 ∘ f.1). destruct f as [f [Hfe Hfm]], g as [g [Hge Hgm]].
  cbn. split.
  - rewrite comp_assoc, Hfe. exact Hge.
  - rewrite comp_assoc, Hfm, <- comp_assoc, Hgm, comp_assoc.
    rewrite <- tensor_map_comp. reflexivity.
Defined.

End MonoidMorphisms.

(** ** The Category of Monoid Objects

    Fix the underlying category [C]. For a monoidal structure supplied to each
    construction, assemble its monoid objects into a category and define the
    faithful forgetful functor. *)

(** ** 幺半群对象范畴

    固定底层范畴 [C]，在各构造中给定幺半结构后，将其幺半群对象组装为范畴，并定义忠实的忘却函子。 *)

Section MonoidCategories.
Context {C : Cat}.

(** The category of monoid objects and operation-preserving arrows.
    Its hom equality inherits that of [C], without comparing proof fields. *)

(** 幺半群对象及保持运算箭头组成的范畴；Hom 相等继承自 [C]，不比较证明字段。 *)

Program Definition MonoidCat (MC : HasMonoidal C)
  : Cat
  :=
  {|Ob := MonoidObj MC
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

(** Forget a monoid's operations and a homomorphism's preservation proofs. *)

(** 忘却幺半群的运算及同态的保持性证明。 *)

Program Definition MonoidForgetF (MC : HasMonoidal C)
  : Fct (MonoidCat MC) C
  :=
  {|fobj := MonoidCarrier
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

Lemma monoid_forget_faithful (MC : HasMonoidal C)
  : is_faithful (MonoidForgetF MC).
Proof. intros A B f g H. exact H. Qed.

End MonoidCategories.
