From Cats Require Import Cat.Core Cat.Functor Cat.Natural.
From Cats Require Import Instance.Set.Core Instance.Set.Fam.

(** * The Category of Coherent Families *)

Record FamC :=
  { famC_base : SetC
  ; famC_fam :> FamS famC_base
  }.

Record FamF (U V : FamC) :=
  { famF_base :> famC_base U →r famC_base V
  ; famF_fam (x : famC_base U) : U x →r V (famF_base x)
  ; famF_naturality {x y : famC_base U} (p : x ≈S y) (a : U x)
    : famF_fam y (transpS U p a) ≈S
        transpS V (@func_proper _ _ famF_base x y p) (famF_fam x a)
  }.

Arguments famF_base {_ _} _.
Arguments famF_fam {_ _} _ _.
Arguments famF_naturality {_ _} _ {_ _} _ _.

(** Base maps are compared pointwise. Their witnesses transport the fiber
    outputs into the same fiber; law proofs are not compared. *)
Definition FamFEq {U V : FamC} (f g : FamF U V) :=
  ∃ p : famF_base f ≈f famF_base g,
    ∀ x (a : U x),
      transpS V (p x) (famF_fam f x a) ≈S famF_fam g x a.

Global Instance FamFEq_Equivalence {U V} : Equivalence (@FamFEq U V).
Proof.
  split.
  - intros f. exists (λ x, reflS (x := famF_base f x)).
    intros x a. apply transpS_id.
  - intros f g [p Hp].
    assert (q : famF_base g ≈f famF_base f).
    { intros x. symmetry. exact (p x). }
    exists q. intros x a.
    transitivity (transpS V (q x) (transpS V (p x) (famF_fam f x a))).
    + apply func_proper. symmetry. exact (Hp x a).
    + apply transpS_inv.
  - intros f g h [p Hp] [q Hq].
    assert (r : famF_base f ≈f famF_base h).
    { intros x. transitivity (famF_base g x); [exact (p x) | exact (q x)]. }
    exists r. intros x a.
    transitivity (transpS V (q x) (transpS V (p x) (famF_fam f x a))).
    + apply transpS_comp.
    + transitivity (transpS V (q x) (famF_fam g x a)).
      * apply func_proper. exact (Hp x a).
      * exact (Hq x a).
Qed.

(** ** Identity and Composition *)

Definition fam_id {U : FamC} : FamF U U.
Proof.
  refine (@Build_FamF U U (id_resp (X := famC_base U))
    (λ x, id_resp (X := U x)) _).
  intros x y p a. simpl. apply transpS_witness_independent.
Defined.

Definition fam_comp {U V W : FamC} (g : FamF V W) (f : FamF U V)
  : FamF U W.
Proof.
  refine (@Build_FamF U W (famF_base g ∘r famF_base f)
    (λ x, famF_fam g (famF_base f x) ∘r famF_fam f x) _).
  intros x y p a. simpl.
  pose (q := @func_proper _ _ (famF_base f) x y p).
  transitivity (famF_fam g (famF_base f y)
    (transpS V q (famF_fam f x a))).
  - apply func_proper. apply famF_naturality.
  - etransitivity. apply famF_naturality.
    apply transpS_witness_independent.
Defined.

Global Instance fam_comp_proper {U V W}
  : Proper (FamFEq ==> FamFEq ==> FamFEq) (@fam_comp U V W).
Proof.
  intros g g' [q Hq] f f' [p Hp].
  assert (r : (famF_base g ∘r famF_base f) ≈f
              (famF_base g' ∘r famF_base f')).
  { intros x. transitivity (famF_base g (famF_base f' x)).
    - exact (@func_proper _ _ (famF_base g) _ _ (p x)).
    - exact (q (famF_base f' x)). }
  exists r. intros x a.
  pose (s := @func_proper _ _ (famF_base g)
    (famF_base f x) (famF_base f' x) (p x)).
  transitivity (transpS W (q (famF_base f' x))
    (transpS W s (famF_fam g (famF_base f x) (famF_fam f x a)))).
  - apply transpS_comp.
  - transitivity (transpS W (q (famF_base f' x))
      (famF_fam g (famF_base f' x) (transpS V (p x) (famF_fam f x a)))).
    + apply func_proper. symmetry. apply famF_naturality.
    + transitivity (famF_fam g' (famF_base f' x)
        (transpS V (p x) (famF_fam f x a))).
      * exact (Hq (famF_base f' x) (transpS V (p x) (famF_fam f x a))).
      * exact (@func_proper _ _ (famF_fam g' (famF_base f' x)) _ _ (Hp x a)).
Qed.

Theorem fam_comp_id_r {U V} (f : FamF U V) : FamFEq (fam_comp f fam_id) f.
Proof.
  exists (λ x, reflS (x := famF_base f x)).
  intros x a. apply transpS_id.
Qed.

Theorem fam_comp_id_l {U V} (f : FamF U V) : FamFEq (fam_comp fam_id f) f.
Proof.
  exists (λ x, reflS (x := famF_base f x)).
  intros x a. apply transpS_id.
Qed.

Theorem fam_comp_assoc {U V W Z} (h : FamF W Z) (g : FamF V W) (f : FamF U V)
  : FamFEq (fam_comp (fam_comp h g) f) (fam_comp h (fam_comp g f)).
Proof.
  exists (λ x, reflS (x := famF_base h (famF_base g (famF_base f x)))).
  intros x a. apply transpS_id.
Qed.

(** ** Category Structure *)

Global Instance FamCat : Cat :=
  {| Ob := FamC
   ; Hom := FamF
   ; HomEq _ _ := FamFEq
   ; HomEq_Equivalence _ _ := FamFEq_Equivalence
   ; id _ := fam_id
   ; comp _ _ _ := fam_comp
   ; comp_proper _ _ _ := fam_comp_proper
   ; comp_id_r _ _ := fam_comp_id_r
   ; comp_id_l _ _ := fam_comp_id_l
   ; comp_assoc _ _ _ _ := fam_comp_assoc |}.

(** ** Base and Total-Space Functors *)

Definition FamBaseF : Functor FamCat SetCat.
Proof.
  refine (@Build_Functor FamCat SetCat famC_base
    (λ U V f, famF_base f) _ _ _).
  - intros U V f g [p Hp]. exact p.
  - intros U x. reflexivity.
  - intros U V W g f x. reflexivity.
Defined.

(** A family morphism acts on both coordinates. Its compatibility with
    transport makes this action respectful of dependent-sum equivalence. *)
Definition fam_total_resp {U V : FamC} (f : FamF U V)
  : SigS (famC_base U) U →r SigS (famC_base V) V.
Proof.
  unshelve refine (@Build_FunS_resp (SigS (famC_base U) U)
    (SigS (famC_base V) V)
    (λ a, (famF_base f a.1; famF_fam f a.1 a.2)) _).
  intros [x a] [y b] [p Hp].
  exists (@func_proper _ _ (famF_base f) x y p).
  transitivity (famF_fam f y (transpS U p a)).
  - symmetry. apply famF_naturality.
  - apply func_proper. exact Hp.
Defined.

Global Instance fam_total_resp_proper {U V : FamC}
  : Proper (FamFEq ==> FunEq) (@fam_total_resp U V).
Proof.
  intros f g [p Hp] [x a]. exists (p x). exact (Hp x a).
Qed.

Definition FamTotalF : Functor FamCat SetCat.
Proof.
  refine (@Build_Functor FamCat SetCat (λ U, SigS (famC_base U) U)
    (λ U V f, fam_total_resp f) _ _ _).
  - intros U V f g Hfg. exact (fam_total_resp_proper f g Hfg).
  - intros U [x a]. reflexivity.
  - intros U V W g f [x a]. reflexivity.
Defined.

(** Total-space projection commutes with every family morphism. *)
Definition FamProjectionN : FamTotalF => FamBaseF.
Proof.
  refine (@mkNat FamCat SetCat FamTotalF FamBaseF (λ U, sig_base_resp U) _).
  intros U V f a. reflexivity.
Defined.
