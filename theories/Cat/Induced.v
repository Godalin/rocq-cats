From Cats Require Export
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Categories Induced by an Object Map *)

(** * 由对象映射诱导的范畴 *)

(** Keep the hom-sets and all operations of an ambient category, while
    selecting a possibly redundant family of objects. No object equality
    or injectivity of the selection is required. *)

(** 保留环境范畴的 Hom 广集及全部运算，选取可重复的对象族；不要求对象相等
    或选取映射具有单射性。 *)

Program Definition InducedCat {C : Cat} (O : Type) (j : O → @Ob C)
  : Cat
  :=
  {|Ob := O
  ; HomSet X Y := HomSet (j X) (j Y)
  ; id X := id
  ; comp X Y Z := comp
  ; comp_proper X Y Z := comp_proper
  |}.
Next Obligation. apply comp_id_r. Qed.
Next Obligation. apply comp_id_l. Qed.
Next Obligation. apply comp_assoc. Qed.

(** The inclusion acts identically on every hom-set. Its laws remain
    transparent when equality contains computational inverse data. *)

(** 嵌入在每个 Hom 广集上恒等作用；相等包含可计算逆数据时，其定律仍保持透明。 *)

Program Definition InducedInclusionF {C : Cat} (O : Type) (j : O → @Ob C)
  : Functor (InducedCat O j) C
  :=
  {|F0 := j
  ; F1 X Y f := f
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** * Representatives for an Induced Category *)

(** * 诱导范畴的对象代表 *)

Section Representatives.
Context {C : Cat} (O : Type) (j : O → @Ob C)
    (r : @Ob C → O) (ε : ∀ X, j (r X) ≅ X).

(** Chosen representatives define a quasi-inverse to the inclusion. *)

(** 选定对象代表给出嵌入的拟逆函子。 *)

Program Definition InducedRepresentativesF
  : Functor C (InducedCat O j)
  :=
  {|F0 := r
  ; F1 X Y f := ((ε Y).2.1 ∘ f ∘ (ε X).1)%hom
  |}.
Next Obligation. intros f g H. rewrite H. reflexivity. Qed.
Next Obligation. rewrite comp_id_r. exact (fst (ε X).2.2). Qed.
Next Obligation.
  rewrite !comp_assoc, <- (comp_assoc (ε Y).1),
    (snd (ε Y).2.2), comp_id_l. reflexivity.
Qed.

(** The representative isomorphisms are natural in the ambient category. *)

(** 代表同构在环境范畴中自然。 *)

Program Definition InducedCounitN
  : (InducedInclusionF O j ∘F InducedRepresentativesF) ⇒ (@IdF C)
  :=
  {|nt X := (ε X).1
  |}.
Next Obligation.
  rewrite <- !comp_assoc, (snd (ε Y).2.2), comp_id_l. reflexivity.
Qed.

(** Inclusion followed by representation is naturally isomorphic to identity. *)

(** 嵌入与代表的复合自然同构于恒等。 *)

Definition induced_counit_nat_iso
  : (InducedInclusionF O j ∘F InducedRepresentativesF) ≅N (@IdF C).
Proof. exists InducedCounitN. intros X. exact (ε X).2. Defined.

(** The same comparisons give the other composite. *)

(** 同一组比较给出另一个复合的自然变换。 *)

Program Definition InducedUnitN
  : (InducedRepresentativesF ∘F InducedInclusionF O j) ⇒
      (@IdF (InducedCat O j))
  :=
  {|nt X := (ε (j X)).1
  |}.
Next Obligation.
  change ((ε (j Y)).1 ∘ ((ε (j Y)).2.1 ∘ f ∘ (ε (j X)).1) ≈
    f ∘ (ε (j X)).1)%cat.
  rewrite <- !comp_assoc, (snd (ε (j Y)).2.2), comp_id_l. reflexivity.
Qed.

(** These two natural isomorphisms exhibit an equivalence, with no choice
    principle beyond the explicitly supplied representatives. *)

(** 两个自然同构给出范畴等价；只使用显式提供的代表，不附加选择原理。 *)

Definition induced_unit_nat_iso
  : (InducedRepresentativesF ∘F InducedInclusionF O j) ≅N
      (@IdF (InducedCat O j)).
Proof. exists InducedUnitN. intros X. exact (ε (j X)).2. Defined.

End Representatives.

(** The induced inclusion is full and faithful, with identity preimages. *)

(** 诱导嵌入全忠实，原像直接取原箭头。 *)

Definition induced_inclusion_fully_faithful {C : Cat}
    (O : Type) (j : O → @Ob C)
  : is_fully_faithful (InducedInclusionF O j).
Proof.
  split.
  - intros X Y f. exists f. reflexivity.
  - intros X Y f g H. exact H.
Defined.
