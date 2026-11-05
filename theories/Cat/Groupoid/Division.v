From Cats Require Export
  Cat.Groupoid.Core.

(** * Division Characterizes Groupoids

    Chosen right division solves [g ∘ f ≈ h]. It retains a solution in
    Type, without assuming unique solutions or a choice principle.
    Left division is the same structure on the opposite category. *)

(** * 除法刻画群胚

    选定右除法求解 [g ∘ f ≈ h]，在 Type 中保留解，不预先要求唯一解或选择原理。
    左除法为反范畴上的同一结构。 *)

(** Right division selects a missing later arrow. *)

(** 右除法选取缺失的后续箭头。 *)

Class HasRightDivision (C : Cat)
  :=
  { right_division {X Y Z : @Ob C} (f : Hom X Y) (h : Hom X Z)
    : ∃ g : Hom Y Z, g ∘ f ≈ h
  }.

Arguments right_division {_ _ _ _ _} _ _.

(** Left division is right division in the opposite. *)

(** 左除法为反范畴中的右除法。 *)

Definition HasLeftDivision (C : Cat)
  : Type
  := HasRightDivision (C^op).

(** A groupoid solves right division by composing with the inverse. Enable
    the chosen division structure explicitly. *)

(** 群胚通过与逆复合求解右除法；选定除法结构须显式启用。 *)

Program Definition groupoid_HasRightDivision (C : Cat)
    `{HC : !IsGroupoid C}
  : HasRightDivision C
  :=
  {|right_division X Y Z f h := (h ∘ f⁻¹; _)
  |}.
Next Obligation.
  destruct (iso_precomp_universal (groupoid_arrow_iso f) h) as [H _].
  exact H.
Defined.

(** The left structure is the opposite right structure, keeping the same
    inverse data and swapping the inverse laws. *)

(** 左除法结构为反范畴中的右除法结构，保留同一逆数据并交换互逆定律。 *)

Definition groupoid_HasLeftDivision (C : Cat) `{HC : !IsGroupoid C}
  : HasLeftDivision C
  := @groupoid_HasRightDivision (C^op) (op_IsGroupoid C).

(** Right division alone supplies a left inverse for every arrow. Applying
    it once more to that inverse and using inverse uniqueness gives both
    inverse equations. No uniqueness of the original choices is assumed. *)

(** 仅有右除法即可为每条箭头给出左逆；再对该左逆应用除法，并复用逆唯一性，
    得到两条互逆方程。不要求原始选择的唯一性。 *)

Program Definition right_division_IsGroupoid (C : Cat)
    `{HD : !HasRightDivision C}
  : C ⦂ Gpd
  :=
  {|groupoid_iso X Y f := ((right_division f (@id X)).1; _)
  |}.
Next Obligation.
  pose (g := (right_division f (@id X)).1).
  pose proof (right_division f (@id X)).2 as Hg.
  split; [exact Hg |].
  destruct (right_division g (@id Y)) as [k Hk].
  pose proof (inverse_unique g k f Hk Hg) as H.
  change (f ∘ g ≈ id). rewrite <- H. exact Hk.
Defined.

(** Opposing the right-division result gives the left-division criterion. *)

(** 对右除法结论取对偶得到左除法判据。 *)

Program Definition left_division_IsGroupoid (C : Cat)
    `{HD : !HasLeftDivision C}
  : C ⦂ Gpd
  :=
  {|groupoid_iso X Y f :=
      ((@groupoid_iso (C^op)
        (@right_division_IsGroupoid (C^op) HD) Y X f).1; _)
  |}.
Next Obligation.
  pose (H := @groupoid_iso (C^op)
    (@right_division_IsGroupoid (C^op) HD) Y X f).
  split; [exact (snd H.2) | exact (fst H.2)].
Defined.

(** Chosen right division and groupoid structure imply each other. *)

(** 选定右除法与群胚结构相互导出。 *)

Definition right_division_groupoid_iff (C : Cat)
  : HasRightDivision C ↔ C ⦂ Gpd.
Proof.
  split; [intros H; exact (@right_division_IsGroupoid C H) |
    intros H; exact (@groupoid_HasRightDivision C H)].
Defined.

(** The same characterization holds for left division. *)

(** 左除法具有同样的刻画。 *)

Definition left_division_groupoid_iff (C : Cat)
  : HasLeftDivision C ↔ C ⦂ Gpd.
Proof.
  split; [intros H; exact (@left_division_IsGroupoid C H) |
    intros H; exact (@groupoid_HasLeftDivision C H)].
Defined.
