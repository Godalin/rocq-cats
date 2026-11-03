From Cats Require Export
  Graph.Morphism
  Graph.Path
  Cat.Core.
From Cats Require Import
  Cat.Functor.Core
  Cat.Natural.

(** * Free Categories on Graphs *)

(** * 图上的自由范畴 *)

(** The free category of formal paths modulo specified path equivalence. *)

(** 以形式路径及指定路径相等构造的自由范畴。 *)

Program Definition FreeCat (G : Graph)
  : Cat
  :=
  {|Ob := @Vertex G
  ; HomSet := PathS G
  ; id x := path_id x
  ; comp x y z := path_comp
  |}.
Next Obligation. apply path_id_r. Defined.
Next Obligation. apply path_id_l. Defined.
Next Obligation. apply path_assoc. Defined.

(** Forget identities and composition, retaining hom-setoids as edge sets. *)

(** 忘却恒等与复合，保留 Hom 广集作为边集。 *)

Program Definition UnderlyingGraph (C : Cat)
  : Graph
  :=
  {|Vertex := @Ob C
  ; EdgeSet := @HomSet C
  |}.

Section Interpretation.
Context {G : Graph} {C : Cat} (D : G →G UnderlyingGraph C).

(** Interpret identities, generators and path composites recursively. *)

(** 递归解释恒等、生成边与路径复合。 *)

Fixpoint path_eval {x y} (f : Path G x y)
  : Hom (D x) (D y)
  := match f with
  | path_id _ => id
  | path_edge e => edge_map D e
  | path_comp g f => path_eval g ∘ path_eval f
  end.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

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

(** The functor induced by an interpretation of generating edges. *)

(** 由生成边解释诱导的函子。 *)

Program Definition FreeF
  : Functor (FreeCat G) C
  :=
  {|F0 := vertex_map D
  ; F1 x y := path_eval
  |}.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

End Interpretation.

(** The extended functor has the specified action on each generator. *)

(** 延拓函子在每条生成边上具有给定作用。 *)

Lemma free_extend_β {G : Graph} {C : Cat} (D : G →G UnderlyingGraph C)
    {x y} (e : Edge x y)
  : fmap (FreeF D) (path_edge e) ≈ edge_map D e.
Proof. reflexivity. Qed.

(** A functor is determined on paths by its action on generating edges. Object
    functions are fixed; comparisons below use hom equivalence. *)

(** 函子在路径上的作用由生成边上的作用决定；对象映射固定，以下比较均使用 Hom
    指定相等。 *)

Program Definition RestrictGraph {G : Graph} {C : Cat}
    (F : Functor (FreeCat G) C)
  : G →G UnderlyingGraph C
  :=
  {|vertex_map := F
  ; edge_map x y :=
      {|func e := fmap F (path_edge e)
      |}
  |}.
Next Obligation. intros e f H. apply functor_fmap_proper. apply path_edge_equiv. exact H. Qed.

(** Restriction followed by free extension recovers the original path action. *)

(** 先限制再自由延拓，恢复原来在路径上的作用。 *)

Lemma free_extend_η {G : Graph} {C : Cat} (F : Functor (FreeCat G) C)
    {x y} (p : Path G x y)
  : fmap (FreeF (RestrictGraph F)) p ≈ fmap F p.
Proof.
  induction p; cbn.
  - symmetry. apply functor_id.
  - reflexivity.
  - rewrite IHp1, IHp2. symmetry. apply functor_comp.
Qed.

(** Naturality on generators extends to every path. This is shared by cones
    over every graph-generated diagram, not reproved for each shape. *)

(** 生成边上的自然性延伸到所有路径；所有自由图式上的锥共同复用此结论，无需按形
    状重证。 *)

Program Definition FreeN {G : Graph} {C : Cat}
    {F H : Functor (FreeCat G) C}
    (α : ∀ x, Hom (F x) (H x))
    (Hα : ∀ x y (e : Edge x y),
      α y ∘ fmap F (path_edge e) ≈ fmap H (path_edge e) ∘ α x)
  : F ⇒ H
  :=
  {|nt := α
  |}.
Next Obligation.
  induction f; cbn.
  - rewrite !functor_id. rewrite comp_id_r, comp_id_l. reflexivity.
  - apply Hα.
  - rewrite (@functor_comp (FreeCat G) C F x y z f1 f2),
      (@functor_comp (FreeCat G) C H x y z f1 f2).
    rewrite <- comp_assoc, IHf1, comp_assoc, IHf2, <- comp_assoc.
    reflexivity.
Defined.

(** Compare restriction followed by extension to the original functor
    naturally. *)

(** 用自然同构比较限制后延拓的函子与原函子。 *)

Definition free_extend_nat_iso {G : Graph} {C : Cat} (F : Functor (FreeCat G) C)
  : FreeF (RestrictGraph F) ≅N F.
Proof.
  exists (@FreeN G C (FreeF (RestrictGraph F)) F (λ _, id)
    (λ x y e, transitivity (comp_id_l _) (symmetry (comp_id_r _)))).
  intros x. exists id. split; apply comp_id_l.
Defined.
