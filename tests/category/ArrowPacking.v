From Cats Require Import
  Cat.Computational.Arrow.Apply
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Terminal.

Local Open Scope computation_scope.

(** Two Arrows on the same pure functor may choose different context
    actions. Bundle notation must use the action selected by that bundle. *)

Section SelectedAction.
Context {C K : Cat} `{MC : !HasMonoidal C} (F : Fct C K)
    (chosen : HasArrow F) `{other : !HasArrow F}.
Context {X Y : C} (Z : C) (f : Hom (F X) (F Y)).

Let A := MakeArrow F chosen.

Example selected_functor : ArrowToFct A = F := eq_refl.

Example selected_action
  : context[A; Z; f] = @arrow_context C K MC F chosen X Y Z f := eq_refl.

Example inferred_action
  : arrow_context F Z f = @arrow_context C K MC F other X Y Z f := eq_refl.

Fail Definition confused_actions
  : context[A; Z; f] = arrow_context F Z f := eq_refl.

Example context_rewrite (g : Hom (F X) (F Y)) (H : f ≈ g)
  : context[A; Z; f] ≈ context[A; Z; g].
Proof. rewrite H. reflexivity. Qed.

End SelectedAction.

(** Packed application uses the chosen extension even when another application
    instance is in scope. The parent and its hom-set universe bounds survive packing. *)

Section SelectedApplication.
Universes o u p.
Constraint p < u, u < o.
Context {K : Cat@{o u p _ _}} (A : Arrow (SetCat@{u p _ _ _ _ _}) K)
  (chosen : HasArrowApply A) `{other : !HasArrowApply A}.

Let AA := ArrowApplyOfArrow A chosen.

Example selected_parent_functor : ArrowToFct (ArrowApplyToArrow AA) = ArrowToFct A
  := eq_refl.
Example selected_parent_action : hasArrow (ArrowApplyToArrow AA) = hasArrow A
  := eq_refl.
Example selected_application (X Y : SetC@{u p})
  : apply[AA; X; Y] = @arrow_apply _ _ _ chosen X Y := eq_refl.
Fail Definition confused_applications (X Y : SetC@{u p})
  : apply[AA; X; Y] = @arrow_apply _ _ _ other X Y := eq_refl.

End SelectedApplication.
