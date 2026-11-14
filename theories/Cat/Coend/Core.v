From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.OppositeProduct
  Cat.Natural.
From Cats Require Export
  Cat.Coend.Wedge.
From Cats Require Import
  Cat.End.Core.

(** * Coends as Opposite Ends *)

(** * coend 作为反范畴中的 end *)

(** A universal cowedge is exactly a universal wedge of the opposite
    bifunctor. No second universal property is stored. *)

(** 泛余楔正是反双函子的泛楔，不另存第二份泛性质。 *)

Definition is_coend {C D : Cat} {F : Fct ((C^op) ×C C) D} {E}
    (κ : Cowedge F E)
  := is_end (op_wedge κ).

(** Read universality with arrows and cowedges in the original categories. *)

(** 用原范畴中的箭头和余楔读取泛性质。 *)

Definition coend_universal_iff {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {E} (κ : Cowedge F E)
  : is_coend κ ↔ ∀ W (μ : Cowedge F W),
      ∃ h : Hom E W, is_unique (λ h, h ∘Cowedge κ ≈CW μ) h.
Proof.
  split; intros H W μ.
  - exact (H W (op_wedge μ)).
  - exact (H W {|op_wedge := μ|}).
Defined.

(** A chosen coend stores only a chosen end in the opposite categories. *)

(** 选定 coend 仅存储反范畴中的一个选定 end。 *)

Class HasCoend (D : Cat) {C : Cat} (F : Fct ((C^op) ×C C) D)
  :=
  (** Inherit exactly the chosen opposite end and its witnesses. *)

  (** 恰好继承选定反 end 及其见证。 *)

  { hasOpEnd :: HasEnd (D^op) (BifunctorOpF F)
  }.

(** Enable a supplied opposite end as a coend. *)

(** 将给定反 end 启用为 coend。 *)

Program Definition OpEndCoend {C D : Cat}
    {F : Fct ((C^op) ×C C) D}
    `{HE : !HasEnd (D^op) (BifunctorOpF F)}
  : HasCoend D F
  :=
  {|hasOpEnd := HE
  |}.

(** The selected coend object is the same selected opposite-end object. *)

(** 选定 coend 对象就是同一个选定反 end 对象。 *)

Definition CoendObj {C D : Cat} (F : Fct ((C^op) ×C C) D)
    `{HC : !HasCoend D F}
  : @Ob D
  := end[BifunctorOpF F].

Arguments CoendObj {_ _} _ {_}.
Notation "'coend[' F ']'" := (CoendObj F) : ob_scope.

(** The chosen cowedge reads the stored opposite-end projections as injections. *)

(** 选定余楔将存储的反 end 投影读作注入。 *)

Definition coend_cowedge {C D : Cat} (F : Fct ((C^op) ×C C) D)
    `{HC : !HasCoend D F}
  : Cowedge F (coend[F])
  :=
  {|op_wedge := πend[BifunctorOpF F]
  |}.

Arguments coend_cowedge {_ _} _ {_}.
Notation "'ιcoend[' F ']'" := (coend_cowedge F) : hom_scope.

(** Universality reuses the same witness without rebuilding mediators. *)

(** 泛性质复用同一个见证，不重建中介。 *)

Definition coend_universal {C D : Cat} (F : Fct ((C^op) ×C C) D)
    `{HC : !HasCoend D F}
  : is_coend ιcoend[F]
  := end_universal (BifunctorOpF F).

(** Descending from a coend is lifting into the original opposite end. *)

(** 从 coend 下降就是向原来的反 end 提升。 *)

Definition coend_desc {C D : Cat} {F : Fct ((C^op) ×C C) D}
    `{HC : !HasCoend D F} {W} (κ : Cowedge F W)
  : Hom (coend[F]) W
  := end⟨op_wedge κ⟩.

Notation "'coend⟨' κ '⟩'" := (coend_desc κ) : hom_scope.

(** ** Descending from a Chosen Coend

    Fix a bifunctor with a selected coend. All descent laws below are the
    existing end laws in the opposite categories. *)

(** ** 从选定 coend 下降

    固定具有选定 coend 的双函子，以下下降定律均为反范畴中已有的 end 定律。 *)

Section ChosenCoend.
Context {C D : Cat} {F : Fct ((C^op) ×C C) D} `{HC : !HasCoend D F}.

(** The inherited mediator is unique with its prescribed injection equations. *)

(** 继承的中介在指定注入方程下唯一。 *)

Theorem coend_desc_unique {W} (κ : Cowedge F W)
  : is_unique (λ h, h ∘Cowedge ιcoend[F] ≈CW κ) (coend⟨κ⟩).
Proof. exact (end_lift_unique (op_wedge κ)). Defined.

(** Descending and then restricting to injections recovers the cowedge. *)

(** 下降后限制到注入恢复原余楔。 *)

Theorem coend_β {W} (κ : Cowedge F W)
  : coend⟨κ⟩ ∘Cowedge ιcoend[F] ≈CW κ.
Proof. exact (end_β (op_wedge κ)). Qed.

(** An outgoing map is recovered from its composites with all injections. *)

(** 从它与全部注入的复合可恢复出射映射。 *)

Theorem coend_η {W} (f : Hom (coend[F]) W)
  : coend⟨f ∘Cowedge ιcoend[F]⟩ ≈ f.
Proof. exact (@end_η (C^op) (D^op) (BifunctorOpF F) _ W f). Qed.

(** Descent respects pointwise cowedge equality. *)

(** 下降保持余楔逐点相等。 *)

Global Instance coend_desc_proper {W}
  : Proper (CowedgeEq ==> @HomEq[coend[F], W]) (@coend_desc C D F HC W).
Proof.
  intros κ μ H.
  exact (@end_lift_proper (C^op) (D^op) (BifunctorOpF F) _ W
    (op_wedge κ) (op_wedge μ) H).
Qed.

(** Descent commutes with postcomposition. *)

(** 下降与后合成相容。 *)

Lemma coend_desc_comp {W V} (f : Hom W V) (κ : Cowedge F W)
  : coend⟨f ∘Cowedge κ⟩ ≈ f ∘ coend⟨κ⟩.
Proof. exact (end_lift_comp (op_wedge κ) f). Qed.

(** The injections jointly distinguish outgoing maps. *)

(** 注入联合地区分出射映射。 *)

Lemma coend_hom_ext {W} (f g : Hom (coend[F]) W)
    (H : ∀ X, f ∘ ιcoend[F] X ≈ g ∘ ιcoend[F] X)
  : f ≈ g.
Proof. exact (@end_hom_ext (C^op) (D^op) (BifunctorOpF F) _ W f g H). Qed.

End ChosenCoend.

(** Object uniqueness is opposite-end uniqueness read in the original category. *)

(** 对象唯一性就是将反 end 唯一性读回原范畴。 *)

Definition coend_unique {C D : Cat} {F : Fct ((C^op) ×C C) D} {E K}
    {κ : Cowedge F E} {μ : Cowedge F K}
    (Hκ : is_coend κ) (Hμ : is_coend μ)
  : E ≅[D] K.
Proof.
  pose (i := end_unique Hμ Hκ).
  exists i.1, i.2.1. split;
    [exact (snd i.2.2) | exact (fst i.2.2)].
Defined.

(** The inherited comparison commutes with every injection. *)

(** 继承的比较与每个注入交换。 *)

Lemma coend_unique_β {C D : Cat} {F : Fct ((C^op) ×C C) D} {E K}
    {κ : Cowedge F E} {μ : Cowedge F K}
    (Hκ : is_coend κ) (Hμ : is_coend μ) (X : @Ob C)
  : (coend_unique Hκ Hμ).1 ∘ κ X ≈ μ X.
Proof. exact (end_unique_β Hμ Hκ X). Qed.

(** A bifunctor transformation induces the opposite end map. Only its two
    endpoint coends are required. *)

(** 双函子自然变换诱导反 end 映射，只要求两端的 coend。 *)

Definition coend_map {C D : Cat} {F G : Fct ((C^op) ×C C) D}
    `{HF : !HasCoend D F} `{HG : !HasCoend D G} (α : F ⇒ G)
  : Hom (coend[F]) (coend[G])
  := end_map (bifunctor_op_nt α).

(** The induced coend map has the prescribed injection components. *)

(** 诱导 coend 映射具有指定的注入分量。 *)

Lemma coend_map_β {C D : Cat} {F G : Fct ((C^op) ×C C) D}
    `{HF : !HasCoend D F} `{HG : !HasCoend D G} (α : F ⇒ G) (X : @Ob C)
  : coend_map α ∘ ιcoend[F] X ≈ ιcoend[G] X ∘ α (X, X).
Proof. exact (end_map_β (bifunctor_op_nt α) X). Qed.

(** Coend maps respect the same natural-transformation equality. *)

(** coend 映射保持同样的自然变换相等。 *)

Global Instance coend_map_proper {C D : Cat}
    {F G : Fct ((C^op) ×C C) D}
    `{HF : !HasCoend D F} `{HG : !HasCoend D G}
  : Proper (NatEq ==> @HomEq[coend[F], coend[G]])
      (@coend_map C D F G HF HG).
Proof.
  intros α β H.
  apply (@end_map_proper (C^op) (D^op)
    (BifunctorOpF G) (BifunctorOpF F)).
  exact (bifunctor_op_nt_proper α β H).
Qed.

(** The coend identity law is the opposite end identity law. *)

(** coend 恒等律就是反 end 恒等律。 *)

Lemma coend_map_id {C D : Cat} {F : Fct ((C^op) ×C C) D}
    `{HF : !HasCoend D F}
  : coend_map (idN (F := F)) ≈ id.
Proof.
  transitivity (@end_map (C^op) (D^op)
    (BifunctorOpF F) (BifunctorOpF F) _ _ idN).
  - apply (@end_map_proper (C^op) (D^op)). apply bifunctor_op_nt_id.
  - apply (@end_map_id (C^op) (D^op)).
Qed.

(** The coend composition law is the opposite end composition law. *)

(** coend 复合律就是反 end 复合律。 *)

Lemma coend_map_comp {C D : Cat} {F G K : Fct ((C^op) ×C C) D}
    `{HF : !HasCoend D F} `{HG : !HasCoend D G} `{HK : !HasCoend D K}
    (β : G ⇒ K) (α : F ⇒ G)
  : coend_map (β ∘Nv α) ≈ coend_map β ∘ coend_map α.
Proof.
  transitivity (@end_map (C^op) (D^op)
    (BifunctorOpF K) (BifunctorOpF F) _ _
    (bifunctor_op_nt α ∘Nv bifunctor_op_nt β)).
  - apply (@end_map_proper (C^op) (D^op)). apply bifunctor_op_nt_comp.
  - exact (end_map_comp (bifunctor_op_nt α) (bifunctor_op_nt β)).
Qed.

(** Natural isomorphisms induce coend isomorphisms through the same
    opposite-end theorem, retaining its computed inverse. *)

(** 自然同构通过同一个反 end 定理诱导 coend 同构，保留其计算得到的逆。 *)

Definition coend_map_is_iso {C D : Cat}
    {F G : Fct ((C^op) ×C C) D}
    `{HF : !HasCoend D F} `{HG : !HasCoend D G}
    (α : F ⇒ G) (Hα : α ⦂ F ≅N G)
  : is_iso (coend_map α).
Proof.
  pose (i := end_map_is_iso (bifunctor_op_nt α)
    (bifunctor_op_nt_NatIso α Hα)).
  exists i.1. split; [exact (snd i.2) | exact (fst i.2)].
Defined.

(** Descent commutes with precomposition by a bifunctor transformation. *)

(** 下降与双函子自然变换的预合成相容。 *)

Lemma coend_desc_map {C D : Cat} {F G : Fct ((C^op) ×C C) D}
    `{HF : !HasCoend D F} `{HG : !HasCoend D G} (α : F ⇒ G) {W}
    (κ : Cowedge G W)
  : coend⟨cowedge_precompose κ α⟩ ≈ coend⟨κ⟩ ∘ coend_map α.
Proof. exact (end_lift_map (bifunctor_op_nt α) (op_wedge κ)). Qed.
