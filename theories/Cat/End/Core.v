From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.
From Cats Require Export
  Cat.End.Wedge.
From Cats Require Import
  Cat.Terminal.

(** * Ends by Their Universal Wedges *)

(** * 以泛楔定义 end *)

(** An end is a wedge through which every wedge factors uniquely. All
    quantifiers and uniqueness witnesses are Type-valued; existence is a
    hypothesis, not a global completeness assertion. *)

(** end 是使每个楔都唯一分解的楔。量词与唯一性见证均为 Type 值；存在性是
    假设，并非全局完备性断言。 *)

Definition is_end {C D : Cat} {F : Fct ((C^op) ×C C) D} {E}
    (κ : Wedge F E)
  := ∀ W (μ : Wedge F W),
    ∃ h : Hom W E, is_unique (λ h, κ ∘Wedge h ≈W μ) h.

(** A chosen end stores one apex, its wedge and the candidate property. *)

(** 选定 end 存储一个顶点、其楔及候选泛性质。 *)

Class HasEnd (D : Cat) {C : Cat} (F : Fct ((C^op) ×C C) D)
  :=
  (** The chosen apex is an object of the supplied codomain. *)

  (** 选定顶点是给定值域中的对象。 *)

  { EndObj : @Ob D

  (** Its projections form one coherent wedge. *)

  (** 其投影组成一个相干的楔。 *)

  ; end_wedge : Wedge F EndObj

  (** Every other wedge retains its unique factoring map. *)

  (** 为每个其他楔保留唯一分解映射。 *)

  ; end_universal : is_end end_wedge
  }.

Arguments EndObj {_ _} _ {_}.
Arguments end_wedge {_ _} _ {_}.
Arguments end_universal {_ _} _ {_} _ _.

Notation "'end[' F ']'" := (EndObj F) : ob_scope.
Notation "'πend[' F ']'" := (end_wedge F) : hom_scope.

(** The universal property supplies a transparent mediator. *)

(** 泛性质提供透明中介。 *)

Definition end_lift {C D : Cat} {F : Fct ((C^op) ×C C) D}
    `{HE : !HasEnd D F} {W} (κ : Wedge F W)
  : Hom W (end[F])
  := (end_universal F W κ).1.

Notation "'end⟨' κ '⟩'" := (end_lift κ) : hom_scope.

(** ** Mediators into a Chosen End

    Fix a mixed-variance bifunctor with a selected end. Its universal
    property gives computation, uniqueness and composition of mediators. *)

(** ** 指向选定 end 的中介

    固定具有选定 end 的混合变元双函子，由其泛性质导出中介的计算、唯一性及复合。 *)

Section ChosenEnd.
Context {C D : Cat} {F : Fct ((C^op) ×C C) D} `{HE : !HasEnd D F}.

(** The selected mediator is the unique map with the prescribed legs. *)

(** 选定中介是具有指定各条腿的唯一映射。 *)

Theorem end_lift_unique {W} (κ : Wedge F W)
  : is_unique (λ h, πend[F] ∘Wedge h ≈W κ) (end⟨κ⟩).
Proof. exact (end_universal F W κ).2. Defined.

(** Every projection of the mediator recovers its input leg. *)

(** 中介的每个投影恢复输入腿。 *)

Theorem end_β {W} (κ : Wedge F W)
  : πend[F] ∘Wedge end⟨κ⟩ ≈W κ.
Proof. exact (@this _ _ _ _ _ (end_lift_unique κ)). Qed.

(** A map is recovered from its composites with all end projections. *)

(** 映射可从它与全部 end 投影的复合中恢复。 *)

Theorem end_η {W} (f : Hom W (end[F]))
  : end⟨πend[F] ∘Wedge f⟩ ≈ f.
Proof. symmetry. apply end_lift_unique. reflexivity. Qed.

(** Mediators respect pointwise equality of the input wedges. *)

(** 中介保持输入楔的逐点相等。 *)

Global Instance end_lift_proper {W}
  : Proper (WedgeEq ==> @HomEq[W, end[F]]) (@end_lift C D F HE W).
Proof. intros κ μ H. apply end_lift_unique. rewrite end_β. exact H. Qed.

(** Mediators commute with precomposition of the input wedge. *)

(** 中介与输入楔的预合成相容。 *)

Lemma end_lift_comp {W V} (κ : Wedge F W) (f : Hom V W)
  : end⟨κ ∘Wedge f⟩ ≈ end⟨κ⟩ ∘ f.
Proof.
  symmetry. apply end_lift_unique.
  rewrite <- wedge_comp_assoc, end_β. reflexivity.
Qed.

(** End projections jointly distinguish maps in the specified hom equality. *)

(** end 投影联合地在指定 Hom 相等下区分映射。 *)

Lemma end_hom_ext {W} (f g : Hom W (end[F]))
    (H : ∀ X, πend[F] X ∘ f ≈ πend[F] X ∘ g)
  : f ≈ g.
Proof. rewrite <- (end_η f), <- (end_η g). apply end_lift_proper. exact H. Qed.

End ChosenEnd.

(** A universal wedge is terminal in the wedge category. Retained commuting
    witnesses require no equality of proof fields. *)

(** 泛楔在楔范畴中是终对象，保留的交换性见证不要求证明字段相等。 *)

Definition end_terminal {C D : Cat} {F : Fct ((C^op) ×C C) D} {E}
    {κ : Wedge F E} (Hκ : is_end κ)
  : @is_terminal (WedgeCat F) (E; κ).
Proof.
  intros [W μ]. destruct (Hκ W μ) as [f Hf].
  exists (f; @this _ _ _ _ _ Hf).
  refine {|this := I
         ; that := _
         |}. intros [g Hg] _.
  exact (@that _ _ _ _ _ Hf g Hg).
Defined.

(** Terminality recovers the same Type-valued universal property. *)

(** 终对象性质恢复同一个 Type 值泛性质。 *)

Definition terminal_end {C D : Cat} {F : Fct ((C^op) ×C C) D} {E}
    {κ : Wedge F E} (Hκ : @is_terminal (WedgeCat F) (E; κ))
  : is_end κ.
Proof.
  intros W μ. destruct (Hκ (W; μ)) as [f Hf].
  exists f.1. refine {|this := f.2
                     ; that := _
                     |}.
  intros g Hg. exact (@that _ _ _ _ _ Hf (g; Hg) I).
Defined.

(** The characterization reuses the ordinary terminal-object theory. *)

(** 此刻画复用普通终对象理论。 *)

Theorem end_iff_terminal {C D : Cat} {F : Fct ((C^op) ×C C) D} {E}
    (κ : Wedge F E)
  : is_end κ ↔ @is_terminal (WedgeCat F) (E; κ).
Proof. split; [apply end_terminal | apply terminal_end]. Defined.

(** Two candidate ends have isomorphic apices, by terminal-object uniqueness. *)

(** 两个候选 end 的顶点由终对象唯一性得到同构。 *)

Definition end_unique {C D : Cat} {F : Fct ((C^op) ×C C) D} {E K}
    {κ : Wedge F E} {μ : Wedge F K} (Hκ : is_end κ) (Hμ : is_end μ)
  : E ≅[D] K.
Proof.
  pose (i := terminal_unique (end_terminal Hκ) (end_terminal Hμ)).
  exists (fmap (WedgeApexF F) i.1).
  exact (functor_is_iso (WedgeApexF F) i.1 i.2).
Defined.

(** The unique comparison respects every projection of the two candidates. *)

(** 唯一比较保持两个候选的每个投影。 *)

Lemma end_unique_β {C D : Cat} {F : Fct ((C^op) ×C C) D} {E K}
    {κ : Wedge F E} {μ : Wedge F K} (Hκ : is_end κ) (Hμ : is_end μ)
    (X : @Ob C)
  : μ X ∘ (end_unique Hκ Hμ).1 ≈ κ X.
Proof.
  exact ((terminal_unique (end_terminal Hκ) (end_terminal Hμ)).1.2 X).
Qed.

(** An ordinary natural transformation induces a map of the two selected
    ends. Only these two ends need to exist. *)

(** 普通自然变换诱导两个选定 end 之间的映射，只要求这两个 end 存在。 *)

Definition end_map {C D : Cat} {F G : Fct ((C^op) ×C C) D}
    `{HF : !HasEnd D F} `{HG : !HasEnd D G} (α : F ⇒ G)
  : Hom (end[F]) (end[G])
  := end⟨wedge_map α πend[F]⟩.

(** The induced map commutes with every diagonal component. *)

(** 诱导映射与每个对角分量交换。 *)

Lemma end_map_β {C D : Cat} {F G : Fct ((C^op) ×C C) D}
    `{HF : !HasEnd D F} `{HG : !HasEnd D G} (α : F ⇒ G) (X : @Ob C)
  : πend[G] X ∘ end_map α ≈ α (X, X) ∘ πend[F] X.
Proof. exact (end_β (wedge_map α πend[F]) X). Qed.

(** End maps respect natural-transformation equality. *)

(** end 映射保持自然变换相等。 *)

Global Instance end_map_proper {C D : Cat}
    {F G : Fct ((C^op) ×C C) D}
    `{HF : !HasEnd D F} `{HG : !HasEnd D G}
  : Proper (NatEq ==> @HomEq[end[F], end[G]]) (@end_map C D F G HF HG).
Proof.
  intros α β H. apply end_lift_proper. apply wedge_map_proper;
    [exact H | reflexivity].
Qed.

(** Identity transformations induce identity end maps. *)

(** 恒等自然变换诱导恒等 end 映射。 *)

Lemma end_map_id {C D : Cat} {F : Fct ((C^op) ×C C) D}
    `{HF : !HasEnd D F}
  : end_map (idN (F := F)) ≈ id.
Proof. apply end_hom_ext. intros X. rewrite end_map_β. cbn. carw. Qed.

(** Vertical composition induces composition of end maps. *)

(** 垂直复合诱导 end 映射的复合。 *)

Lemma end_map_comp {C D : Cat} {F G K : Fct ((C^op) ×C C) D}
    `{HF : !HasEnd D F} `{HG : !HasEnd D G} `{HK : !HasEnd D K}
    (β : G ⇒ K) (α : F ⇒ G)
  : end_map (β ∘Nv α) ≈ end_map β ∘ end_map α.
Proof.
  apply end_hom_ext. intros X.
  rewrite end_map_β, <- comp_assoc, end_map_β, comp_assoc, end_map_β.
  apply comp_assoc.
Qed.

(** A natural isomorphism induces an isomorphism of the two chosen ends.
    Its inverse is the map induced by the inverse transformation. *)

(** 自然同构诱导两个选定 end 的同构，其逆是逆自然变换诱导的映射。 *)

Definition end_map_is_iso {C D : Cat} {F G : Fct ((C^op) ×C C) D}
    `{HF : !HasEnd D F} `{HG : !HasEnd D G}
    (α : F ⇒ G) (Hα : α ⦂ F ≅N G)
  : is_iso (end_map α).
Proof.
  exists (end_map (α^-1N Hα)).
  split; unfold is_linv_of, is_rinv_of; rewrite <- end_map_comp.
  - transitivity (end_map (idN (F := F))).
    + apply end_map_proper. intros X. exact (fst (Hα X).2).
    + apply end_map_id.
  - transitivity (end_map (idN (F := G))).
    + apply end_map_proper. intros X. exact (snd (Hα X).2).
    + apply end_map_id.
Defined.

(** Universal lifting is compatible with a bifunctor transformation. *)

(** 泛提升与双函子自然变换相容。 *)

Lemma end_lift_map {C D : Cat} {F G : Fct ((C^op) ×C C) D}
    `{HF : !HasEnd D F} `{HG : !HasEnd D G} (α : F ⇒ G) {W}
    (κ : Wedge F W)
  : end⟨wedge_map α κ⟩ ≈ end_map α ∘ end⟨κ⟩.
Proof.
  apply end_hom_ext. intros X.
  rewrite <- comp_assoc, end_map_β, comp_assoc.
  transitivity (α (X, X) ∘ κ X).
  - exact (end_β (wedge_map α κ) X).
  - apply comp_l. symmetry. exact (end_β κ X).
Qed.
