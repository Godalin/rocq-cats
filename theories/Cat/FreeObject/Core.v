From Cats Require Export
  Cat.Comma.Structured.

(** * Chosen Free Objects

    A functor has chosen free objects when each structured-arrow category
    has a selected initial object. This is additional structure, never an
    assertion that every functor has a left adjoint. *)

(** * 选定自由对象

    函子具有选定自由对象，指每个结构箭头范畴均有选定始对象。这是额外结构，
    并不声称每个函子都具有左伴随。 *)

Class HasFreeObjects {C D : Cat} (U : Functor D C)
  :=
  { free_initial (X : @Ob C) : HasInitial (X ↓[U]) }.

Arguments free_initial {_ _ _ _} _.

Section FreeObjects.
Context {C D : Cat} (U : Functor D C) `{HF : !HasFreeObjects U}.

(** The free object is the right endpoint of the selected initial arrow. *)

(** 自由对象是选定始箭头的右端点。 *)

Definition FreeOb (X : @Ob C)
  : @Ob D
  := comma_right_ob (@Init (X ↓[U]) (free_initial X)).

(** The stored structured arrow supplies the unit at [X]. *)

(** 保存的结构箭头给出 [X] 处的单位。 *)

Definition free_unit (X : @Ob C)
  : Hom X (U (FreeOb X))
  := comma_arrow (@Init (X ↓[U]) (free_initial X)).

(** The selected initial object satisfies the direct universal property. *)

(** 选定始对象满足直接泛性质。 *)

Definition free_universal (X : @Ob C)
  : free_unit X ⦂ UnivArr(U)
  := structured_initial_universal U _
      (@initial_universal (X ↓[U]) (free_initial X)).

(** Extend an arrow uniquely through the unit; this projection is transparent. *)

(** 通过单位唯一延拓箭头；这个投影保持透明。 *)

Definition free_object_extend {X : @Ob C} {A : @Ob D} (f : Hom X (U A))
  : Hom (FreeOb X) A
  := (free_universal X A f).1.

(** The extension factors the original arrow through the unit. *)

(** 延拓通过单位分解原箭头。 *)

Lemma free_object_extend_β {X : @Ob C} {A : @Ob D} (f : Hom X (U A))
  : fmap U (free_object_extend f) ∘ free_unit X ≈ f.
Proof. exact (@this _ _ _ _ _ (free_universal X A f).2). Qed.

(** Any factorization is the selected extension. *)

(** 任意分解均等于选定延拓。 *)

Lemma free_object_extend_unique {X : @Ob C} {A : @Ob D} (f : Hom X (U A))
    (g : Hom (FreeOb X) A) (H : fmap U g ∘ free_unit X ≈ f)
  : g ≈ free_object_extend f.
Proof. exact (@that _ _ _ _ _ (free_universal X A f).2 g H). Qed.

(** Extending a unit-factorized arrow recovers the arrow. *)

(** 延拓已通过单位分解的箭头，恢复原箭头。 *)

Lemma free_object_extend_η {X : @Ob C} {A : @Ob D} (g : Hom (FreeOb X) A)
  : free_object_extend (fmap U g ∘ free_unit X) ≈ g.
Proof. symmetry. apply free_object_extend_unique. reflexivity. Qed.

(** Equivalent arrows have equivalent extensions, by uniqueness. *)

(** 由唯一性，相等箭头具有相等延拓。 *)

Global Instance free_object_extend_proper {X : @Ob C} {A : @Ob D}
  : Proper (@HomEq C X (U A) ==> @HomEq D (FreeOb X) A) free_object_extend.
Proof.
  intros f g E. apply free_object_extend_unique.
  rewrite free_object_extend_β. exact E.
Qed.

(** Postcomposition commutes with extension by functoriality and uniqueness. *)

(** 由函子性和唯一性，后合成与延拓交换。 *)

Lemma free_object_extend_comp_l {X : @Ob C} {A B : @Ob D}
    (g : Hom A B) (f : Hom X (U A))
  : g ∘ free_object_extend f ≈ free_object_extend (fmap U g ∘ f).
Proof.
  apply free_object_extend_unique.
  rewrite functor_comp, comp_assoc, free_object_extend_β. reflexivity.
Qed.

End FreeObjects.

(** Direct universal arrows assemble chosen initial objects. The function
    selecting those arrows is supplied explicitly, without a choice axiom. *)

(** 直接泛箭头组装为选定始对象；选取箭头的函数显式给出，不使用选择公理。 *)

Program Definition FreeObjectsFromUniversal {C D : Cat} (U : Functor D C)
    (A : @Ob C → @Ob D) (η : ∀ X, Hom X (U (A X)))
    (Hη : ∀ X, η X ⦂ UnivArr(U))
  : HasFreeObjects U
  :=
  {|free_initial X :=
     {|hasOpTerminal :=
        {|Term := StructuredOb U (η X)
        ; terminal_universal := universal_arrow_is_initial U (Hη X)
        |}
     |}
  |}.
