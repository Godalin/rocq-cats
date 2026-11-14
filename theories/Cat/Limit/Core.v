From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core
  Cat.Terminal.

(** * Limits of Diagrams

    The candidate property retains a unique mediator for every cone. Chosen
    limits are separate, as for products and pullbacks. *)

(** * 图式的极限

    候选性质为每个锥保留唯一中介；选定极限与候选性质分开，与积和拉回的接口一致。 *)

Definition is_limit {J C : Cat} {D : Fct J C} {L : @Ob C} (κ : L ⇒Δ D)
  := ∀ X (μ : X ⇒Δ D), ∃ h : Hom X L, is_unique (λ h, κ ∘Cone h ≈N μ) h.

Notation "κ '⦂' 'Lim(' D ')'" := (@is_limit _ _ D _ κ)
  (at level 50, no associativity) : cat_scope.

(** A selected apex and cone with its full limiting universal property. *)

(** 选定顶点、锥及完整极限泛性质。 *)

Class HasLimit (C : Cat) {J : Cat} (D : Fct J C)
  :=
  { Lim : @Ob C
  ; limit_cone : Lim ⇒Δ D
  ; limit_universal : is_limit limit_cone }.

Arguments Lim {_ _} _ {_}.
Arguments limit_cone {_ _} _ {_}.
Arguments limit_universal {_ _} _ {_} _ _.
Notation "'lim' D" := (Lim D) (at level 35) : ob_scope.
Notation "'πlim[' D ']'" := (limit_cone D) : hom_scope.

(** The unique mediator from a cone to the selected limiting cone. *)

(** 从锥到选定极限锥的唯一中介。 *)

Definition limit_lift {J C : Cat} {D : Fct J C}
    `{HL : !HasLimit C D} {X} (κ : X ⇒Δ D)
  : Hom X (lim D)
  := (limit_universal D X κ).1.

Notation "'lim⟨' κ '⟩'" := (limit_lift κ) (at level 35) : hom_scope.

(** ** Lifting into a Chosen Limit

    Fix a diagram [D] with a chosen limit in [C]. Derive uniqueness,
    computation, respectfulness and composition for its universal lift. *)

(** ** 到选定极限的提升定律

    固定 [C] 中具有选定极限的图式 [D]，导出泛提升的唯一性、计算、保相等性和复合定律。 *)

Section ChosenLimit.
Context {J C : Cat} {D : Fct J C} `{HL : !HasLimit C D}.

(** The selected mediator factors the cone and is unique up to hom equality. *)

(** 选定中介分解锥，并在 Hom 相等下唯一。 *)

Theorem limit_lift_unique {X} (κ : X ⇒Δ D)
  : is_unique (λ h, πlim[D] ∘Cone h ≈N κ) (lim⟨κ⟩).
Proof. exact (limit_universal D X κ).2. Defined.

(** The limiting cone composed with its mediator recovers the input cone. *)

(** 极限锥与中介复合后恢复输入锥。 *)

Theorem limit_β {X} (κ : X ⇒Δ D)
  : πlim[D] ∘Cone lim⟨κ⟩ ≈N κ.
Proof. exact (@this _ _ _ _ _ (limit_lift_unique κ)). Qed.

(** The mediator of a cone obtained by precomposition recovers that map. *)

(** 通过预合成得到的锥，其中介恢复原映射。 *)

Theorem limit_η {X} (f : Hom X (lim D))
  : lim⟨πlim[D] ∘Cone f⟩ ≈ f.
Proof. symmetry. apply limit_lift_unique. reflexivity. Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance limit_lift_proper {X}
  : Proper (NatEq ==> @HomEq[X, lim D]) (@limit_lift J C D HL X).
Proof.
  intros κ μ H. apply limit_lift_unique. rewrite limit_β. exact H.
Qed.

(** Compatibility with composition for [limit_lift]. *)

(** [limit_lift] 与复合的相容性。 *)

Lemma limit_lift_comp {X Y} (κ : X ⇒Δ D) (f : Hom Y X)
  : lim⟨κ ∘Cone f⟩ ≈ lim⟨κ⟩ ∘ f.
Proof.
  symmetry. apply limit_lift_unique.
  rewrite <- cone_comp_assoc, limit_β. reflexivity.
Qed.

End ChosenLimit.

(** A limiting cone is exactly a terminal object of the cone category.
    Consequently object uniqueness reuses the general terminal-object theorem. *)

(** 极限锥正是锥范畴的终对象，因此对象唯一性复用一般终对象唯一性定理。 *)

Definition limit_terminal {J C : Cat} {D : Fct J C} {L : @Ob C}
    {κ : L ⇒Δ D} (Hκ : is_limit κ)
  : @is_terminal (ConeCat D) (L; κ).
Proof.
  intros [X μ]. destruct (Hκ X μ) as [f Hf].
  exists (f; @this _ _ _ _ _ Hf).
  refine {|this := I
         ; that := _
         |}. intros [g Hg] _.
  exact (@that _ _ _ _ _ Hf g Hg).
Defined.

(** The candidate terminal object property gives a limit of the empty diagram. *)

(** 候选终对象性质给出空图式的极限。 *)

Definition terminal_limit {J C : Cat} {D : Fct J C} {L : @Ob C}
    {κ : L ⇒Δ D} (Hκ : @is_terminal (ConeCat D) (L; κ))
  : is_limit κ.
Proof.
  intros X μ. destruct (Hκ (X; μ)) as [f Hf].
  exists f.1. refine {|this := f.2
                     ; that := _
                     |}.
  intros g Hg. exact (@that _ _ _ _ _ Hf (g; Hg) I).
Defined.

(** A cone is limiting exactly when it is terminal in its cone category. *)

(** 锥是极限，当且仅当它在锥范畴中为终对象。 *)

Theorem limit_iff_terminal {J C : Cat} {D : Fct J C} {L : @Ob C}
    (κ : L ⇒Δ D)
  : is_limit κ ↔ @is_terminal (ConeCat D) (L; κ).
Proof. split; [apply limit_terminal | apply terminal_limit]. Defined.

(** Limiting cones for one diagram have isomorphic apex objects. *)

(** 同一图式的极限锥具有同构顶点。 *)

Definition limit_unique {J C : Cat} {D : Fct J C} {L M : @Ob C}
    {κ : L ⇒Δ D} {μ : M ⇒Δ D} (Hκ : is_limit κ) (Hμ : is_limit μ)
  : L ≅[C] M.
Proof.
  pose (i := terminal_unique (limit_terminal Hκ) (limit_terminal Hμ)).
  exists (fmap (ConeApexF D) i.1).
  exact (functor_is_iso (ConeApexF D) i.1 i.2).
Defined.

(** Choose a limit for every diagram of the specified shape. *)

(** 为指定形状的每个图式选择极限。 *)

Class HasLimitsOfShape (C J : Cat)
  :=
  { hasLimit (D : Fct J C) :: HasLimit C D }.

(** ** The Limit Functor

    Assume chosen limits for all diagrams of shape [J] in [C]. Map natural
    transformations by universal lifts and assemble the resulting limit
    functor. *)

(** ** 极限函子

    假定 [C] 为所有形状为 [J] 的图式选定极限，用泛提升映射自然变换，并组装极限函子。 *)

Section LimitFunctor.
Context {J C : Cat} `{HL : !HasLimitsOfShape C J}.

(** The map between selected limits induced by a diagram transformation. *)

(** 图式自然变换诱导的选定极限间映射。 *)

Definition limit_map {D E : Fct J C} (α : D ⇒ E)
  : Hom (lim D) (lim E)
  := lim⟨ α ∘Nv πlim[D] ⟩.

(** The induced limit map commutes with the limiting cones. *)

(** 诱导的极限映射与极限锥交换。 *)

Lemma limit_map_comm {D E : Fct J C} (α : D ⇒ E)
  : πlim[E] ∘Cone limit_map α ≈N (α ∘Nv πlim[D]).
Proof. apply limit_β. Qed.

(** The induced limit map has the prescribed component at each projection. *)

(** 诱导的极限映射在每个投影下具有给定分量。 *)

Lemma limit_map_β {D E : Fct J C} (α : D ⇒ E) (j : @Ob J)
  : πlim[E] j ∘ limit_map α ≈ α j ∘ πlim[D] j.
Proof. exact (limit_map_comm α j). Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance limit_map_proper {D E : Fct J C}
  : Proper (NatEq ==> @HomEq[lim D, lim E]) (@limit_map D E).
Proof.
  intros α β H. apply limit_lift_proper. intros j. cbn. rewrite (H j). reflexivity.
Qed.

(** Compatibility with identities for [limit_map]. *)

(** [limit_map] 与恒等的相容性。 *)

Lemma limit_map_id {D : Fct J C}
  : limit_map (idN (F := D)) ≈ id.
Proof.
  unfold limit_map. rewrite <- (limit_η (@id (lim D))).
  apply limit_lift_proper. intros j. cbn. carw.
Qed.

(** Compatibility with composition for [limit_map]. *)

(** [limit_map] 与复合的相容性。 *)

Lemma limit_map_comp {D E K : Fct J C} (β : E ⇒ K) (α : D ⇒ E)
  : limit_map (β ∘Nv α) ≈ limit_map β ∘ limit_map α.
Proof.
  symmetry. apply limit_lift_unique. intros j.
  change (πlim[K] j ∘ (limit_map β ∘ limit_map α) ≈
    (β j ∘ α j) ∘ πlim[D] j).
  rewrite <- (comp_assoc (πlim[K] j) (limit_map β) (limit_map α)),
    (limit_map_β β j), (comp_assoc (β j) (πlim[E] j) (limit_map α)),
    (limit_map_β α j).
  symmetry. apply comp_assoc.
Qed.

(** Selected limits form a functor on the category of diagrams. *)

(** 选定极限构成图式范畴上的函子。 *)

Program Definition LimF
  : Fct (FctCat J C) C
  :=
  {|F0 D := lim D
  ; F1 D E α := limit_map α
  |}.
Next Obligation. apply limit_map_id. Qed.
Next Obligation. apply limit_map_comp. Qed.

(** Taking a universal mediator commutes with a diagram transformation. *)

(** 取泛中介与图式自然变换相容。 *)

Lemma limit_lift_map {D E : Fct J C} (α : D ⇒ E) {X} (κ : X ⇒Δ D)
  : lim⟨ α ∘Nv κ ⟩ ≈ limit_map α ∘ lim⟨ κ ⟩.
Proof.
  symmetry. apply limit_lift_unique. intros j.
  change (πlim[E] j ∘ (limit_map α ∘ lim⟨ κ ⟩) ≈ α j ∘ κ j).
  rewrite <- (comp_assoc (πlim[E] j) (limit_map α) (lim⟨ κ ⟩)),
    (limit_map_β α j).
  transitivity (α j ∘ (πlim[D] j ∘ lim⟨ κ ⟩)).
  - apply comp_assoc.
  - apply comp_l. exact (limit_β κ j).
Qed.

End LimitFunctor.
