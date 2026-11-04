From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.CatCat
  Instance.Set.Core
  Instance.Set.Groupoid
  Instance.Set.Fam.Core
  Instance.Set.Fam.Fixed.

(** * Coherent Families as Equality-Groupoid Actions

    Actions are covariant set-valued functors. The equality groupoid is thin:
    its hom equality identifies parallel base-equality witnesses. This is
    precisely the witness independence already required by coherent families.
    Quasi-inverse functors and natural round-trip isomorphisms give their
    categorical equivalence, without equality of records or coherence proofs.
    Base and fiber carrier/equality levels are independent; auxiliary law
    universes supply the required bounds. *)

(** * 相干族作为相等群胚的作用

    作用是协变的集合值函子。相等群胚是薄的：其 Hom 相等识别平行的基底相等
    见证，恰好对应相干族的见证独立性。拟逆函子及往返自然同构给出范畴等价，
    不等同记录或相干性证明。基底与纤维的载体、相等层级独立，所需定律上界
    由辅助宇宙提供。 *)

Program Definition FamActionF {X : SetC} (A : FamS X)
  : Functor (EqGpd X) SetCat
  :=
  {|F0 x := A x
  ; F1 x y p := transpS A p
  |}.
Next Obligation.
  intros p q H. apply transpS_witness_independent.
Defined.
Next Obligation. intros a. apply transpS_id. Defined.
Next Obligation. intros a. apply transpS_comp. Defined.

(** Thinness strengthens the ordinary functor laws to coherence for arbitrary
    base witnesses, including arbitrary loops and composite witnesses. *)

(** 薄性将普通函子律加强为任意基底见证的相干律，包括任意环路及复合见证。 *)

Program Definition ActionFamS {X : SetC}
    (F : Functor (EqGpd X) SetCat)
  : FamS X
  :=
  {|fam x := F x
  ; transpS x y p := fmap F p
  |}.
Next Obligation.
  transitivity (fmap F (@Cats.Cat.Core.id (EqGpd X) x) v).
  - apply (@functor_fmap_proper _ _ F x x p
      (@Cats.Cat.Core.id (EqGpd X) x) tt).
  - exact (@functor_id _ _ F x v).
Defined.
Next Obligation.
  transitivity (fmap F (transitivity p q) v).
  - apply (@functor_fmap_proper _ _ F x z r (transitivity p q) tt).
  - exact (@functor_comp _ _ F x y z q p v).
Defined.

(** A fiberwise family map is a natural transformation of the corresponding
    actions; its transport law is exactly naturality. *)

(** 逐纤维族映射给出对应作用的自然变换，其运输定律恰为自然性。 *)

Program Definition FamMapActionN {X : SetC} {A B : FamS X} (φ : A →Fam B)
  : FamActionF A ⇒ FamActionF B
  :=
  {|nt x := fam_map φ x
  |}.
Next Obligation. intros a. apply fam_map_naturality. Defined.

(** Conversely, a natural transformation is a coherent fiberwise map. *)

(** 反之，自然变换给出相干的逐纤维映射。 *)

Program Definition action_nat_fam_map {X : SetC}
    {F G : Functor (EqGpd X) SetCat} (α : F ⇒ G)
  : ActionFamS F →Fam ActionFamS G
  :=
  {|fam_map x := α x
  |}.
Next Obligation. exact (nt_naturality α p a). Defined.

(** Families and their maps form a functor into the action category. *)

(** 族及族映射组成指向作用范畴的函子。 *)

Program Definition FamActionCatF (X : SetC)
  : Functor (FamSCat X) (Fct (EqGpd X) SetCat)
  :=
  {|F0 := FamActionF
  ; F1 A B := FamMapActionN
  |}.
Next Obligation. intros φ ψ H x a. exact (H x a). Defined.
Next Obligation. intros x a. reflexivity. Defined.
Next Obligation. intros x a. reflexivity. Defined.

(** Recover families functorially from actions and natural transformations. *)

(** 从作用和自然变换函子性地恢复族。 *)

Program Definition ActionFamCatF (X : SetC)
  : Functor (Fct (EqGpd X) SetCat) (FamSCat X)
  :=
  {|F0 := ActionFamS
  ; F1 F G := action_nat_fam_map
  |}.
Next Obligation. intros α β H x a. exact (H x a). Defined.
Next Obligation. intros x a. reflexivity. Defined.
Next Obligation. intros x a. reflexivity. Defined.

(** The family round trip keeps fibers and transports. Its comparison maps
    are identities on elements, without comparing coherence fields. *)

(** 族的往返保留纤维与运输；比较映射在元素上为恒等，不比较相干性字段。 *)

Program Definition fam_action_fam_elim {X : SetC} (A : FamS X)
  : ActionFamS (FamActionF A) →Fam A
  :=
  {|fam_map x := id_resp
  |}.
Next Obligation. reflexivity. Defined.

(** The inverse comparison also keeps every fiber element. *)

(** 逆向比较同样保留每个纤维元素。 *)

Program Definition fam_action_fam_intro {X : SetC} (A : FamS X)
  : A →Fam ActionFamS (FamActionF A)
  :=
  {|fam_map x := id_resp
  |}.
Next Obligation. reflexivity. Defined.

(** Both family comparison maps are mutually inverse under family equality. *)

(** 两个族比较映射在族映射相等下互逆。 *)

Definition fam_action_fam_iso {X : SetC} (A : FamS X)
  : @is_iso (FamSCat X) _ _ (fam_action_fam_elim A).
Proof.
  exists (fam_action_fam_intro A). split; intros x a; reflexivity.
Defined.

(** The family round-trip comparison is natural in family maps. *)

(** 族往返比较在族映射上自然。 *)

Program Definition FamActionFamN (X : SetC)
  : (ActionFamCatF X ∘F FamActionCatF X) ⇒ (@IdF (FamSCat X))
  :=
  {|nt := fam_action_fam_elim
  |}.
Next Obligation. intros x a. reflexivity. Defined.

(** Family to action to family is naturally isomorphic to the identity. *)

(** 从族到作用再回到族自然同构于恒等。 *)

Definition fam_action_fam_nat_iso (X : SetC)
  : (ActionFamCatF X ∘F FamActionCatF X) ≅N (@IdF (FamSCat X))
  := (FamActionFamN X; fam_action_fam_iso).

(** The action round trip retains object sets and arrow maps. Compare the
    functors by the identity natural transformation on their values. *)

(** 作用的往返保留对象集合与箭头映射，通过取值上的恒等自然变换比较函子。 *)

Program Definition ActionFamMapN {X : SetC}
    (F : Functor (EqGpd X) SetCat)
  : FamActionF (ActionFamS F) ⇒ F
  :=
  {|nt x := id_resp
  |}.
Next Obligation. intros a. reflexivity. Defined.

(** The identity components make the action comparison invertible. *)

(** 恒等分量使作用比较可逆。 *)

Definition action_fam_action_iso {X : SetC}
    (F : Functor (EqGpd X) SetCat)
  : @is_iso (Fct (EqGpd X) SetCat) _ _ (ActionFamMapN F).
Proof.
  apply NatIso_is_iso. intros x.
  exists id_resp. split; intros a; reflexivity.
Defined.

(** The action comparison is natural in natural transformations. *)

(** 作用比较在自然变换上自然。 *)

Program Definition ActionFamActionN (X : SetC)
  : (FamActionCatF X ∘F ActionFamCatF X) ⇒
      (@IdF (Fct (EqGpd X) SetCat))
  :=
  {|nt := ActionFamMapN
  |}.
Next Obligation. intros x a. reflexivity. Defined.

(** Action to family to action is naturally isomorphic to the identity. *)

(** 从作用到族再回到作用自然同构于恒等。 *)

Definition action_fam_action_nat_iso (X : SetC)
  : (FamActionCatF X ∘F ActionFamCatF X) ≅N
      (@IdF (Fct (EqGpd X) SetCat))
  := (ActionFamActionN X; action_fam_action_iso).

(** Coherent families are exactly covariant actions of the thin equality
    groupoid, as an equivalence of categories. *)

(** 相干族恰为薄相等群胚的协变作用，此对应构成范畴等价。 *)

Definition fam_action_equiv (X : SetC)
  : FamSCat X ≃C Fct (EqGpd X) SetCat
  := (FamActionCatF X; (ActionFamCatF X;
      (fam_action_fam_nat_iso X, action_fam_action_nat_iso X))).

(** Family reindexing is precomposition by the functor induced by the base
    map. The comparison keeps fiber elements and is natural in base arrows. *)

(** 族重索引对应沿基底映射诱导函子的预复合；比较保留纤维元素，并在基底箭头上
    自然。 *)

Program Definition FamActionReindexN {X Y : SetC}
    (f : X →r Y) (A : FamS Y)
  : FamActionF A[f]S ⇒ (FamActionF A ∘F EqGpdF f)
  :=
  {|nt x := id_resp
  |}.
Next Obligation. intros a. reflexivity. Defined.

(** The reindexing comparison is a natural isomorphism. This compares the
    two actions; it does not assert a separate indexed-equivalence structure. *)

(** 重索引比较是两个作用之间的自然同构，此处不另断言完整的索引等价结构。 *)

Definition fam_action_reindex_nat_iso {X Y : SetC}
    (f : X →r Y) (A : FamS Y)
  : FamActionF A[f]S ≅N (FamActionF A ∘F EqGpdF f).
Proof.
  exists (FamActionReindexN f A). intros x.
  exists id_resp. split; intros a; reflexivity.
Defined.
