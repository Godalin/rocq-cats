From Cats Require Export
  Graph.Morphism
  Graph.Path
  Cat.Core.
From Cats Require Import
  Cat.Functor
  Cat.Natural.

(** * Free Categories on Graphs *)
Program Definition FreeCat (G : Graph)
  : Cat
  := {| Ob := @Vertex G
      ; HomSet := PathS G
      ; id x := path_id x
      ; comp x y z := path_comp |}.
Next Obligation. apply path_id_r. Defined.
Next Obligation. apply path_id_l. Defined.
Next Obligation. apply path_assoc. Defined.

Program Definition UnderlyingGraph (C : Cat)
  : Graph
  := {| Vertex := @Ob C; EdgeSet := @HomSet C |}.

Section Interpretation.
Context {G : Graph} {C : Cat} (D : G →G UnderlyingGraph C).

Fixpoint path_eval {x y} (f : Path G x y)
  : Hom (D x) (D y)
  := match f with
  | path_id _ => id
  | path_edge e => edge_map D e
  | path_comp g f => path_eval g ∘ path_eval f
  end.

Global Instance path_eval_proper {x y}
  : Proper (PathEq ==> HomEq) (@path_eval x y).
Proof.
  intros f g H. induction H; cbn.
  - reflexivity.
  - symmetry. assumption.
  - etransitivity; eassumption.
  - apply func_proper. assumption.
  - apply comp_proper; assumption.
  - apply comp_id_r.
  - apply comp_id_l.
  - apply comp_assoc.
Defined.

Program Definition FreeF
  : Functor (FreeCat G) C
  := {| F0 := vertex_map D; F1 x y := path_eval |}.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

End Interpretation.

Lemma free_extend_β {G : Graph} {C : Cat} (D : G →G UnderlyingGraph C)
    {x y} (e : Edge x y)
  : fmap (FreeF D) (path_edge e) ≈ edge_map D e.
Proof. reflexivity. Qed.

(** A functor is determined on paths by its action on generating edges.
    Object functions are fixed; comparisons below use hom equivalence. *)
Program Definition RestrictGraph {G : Graph} {C : Cat}
    (F : Functor (FreeCat G) C)
  : G →G UnderlyingGraph C
  := {| vertex_map := F
      ; edge_map x y := {| func e := fmap F (path_edge e) |} |}.
Next Obligation. intros e f H. apply functor_fmap_proper. apply path_edge_equiv. exact H. Qed.

Lemma free_extend_η {G : Graph} {C : Cat} (F : Functor (FreeCat G) C)
    {x y} (p : Path G x y)
  : fmap (FreeF (RestrictGraph F)) p ≈ fmap F p.
Proof.
  induction p; cbn.
  - symmetry. apply functor_id.
  - reflexivity.
  - rewrite IHp1, IHp2. symmetry. apply functor_comp.
Qed.

(** Naturality on generators extends to every path. This is shared by
    cones over every graph-generated diagram, not reproved for each shape. *)
Program Definition FreeN {G : Graph} {C : Cat}
    {F H : Functor (FreeCat G) C}
    (α : ∀ x, Hom (F x) (H x))
    (Hα : ∀ x y (e : Edge x y),
      α y ∘ fmap F (path_edge e) ≈ fmap H (path_edge e) ∘ α x)
  : F ⇒ H
  := {| nt := α |}.
Next Obligation.
  induction f; cbn.
  - rewrite !functor_id. rewrite comp_id_r, comp_id_l. reflexivity.
  - apply Hα.
  - rewrite (@functor_comp (FreeCat G) C F x y z f1 f2),
      (@functor_comp (FreeCat G) C H x y z f1 f2).
    rewrite <- comp_assoc, IHf1, comp_assoc, IHf2, <- comp_assoc.
    reflexivity.
Defined.

Definition free_extend_nat_iso {G : Graph} {C : Cat} (F : Functor (FreeCat G) C)
  : FreeF (RestrictGraph F) ≅N F.
Proof.
  exists (@FreeN G C (FreeF (RestrictGraph F)) F (λ _, id)
    (λ x y e, transitivity (comp_id_l _) (symmetry (comp_id_r _)))).
  intros x. exists id. split; apply comp_id_l.
Defined.
