From Cats Require Export
  Cat.Chain
  Instance.Set.Simplicial.Vertex.Core
  Instance.Set.Vertex.Relabel.

Local Open Scope nat_scope.

(** * Edges and Endpoint Transport

    Rebase an arrow along the specified object transports. The comparison
    of one-simplices uses these transports at their two endpoints. *)

(** * 边与端点运输

    沿指定对象运输调整箭头的端点；一维单形的比较使用两个端点上的这些运输。 *)

(** An endpoint comparison and its single edge square determine equality
    of one-simplices. No groupoid assumption is needed. *)

(** 端点比较及唯一边方块确定一维单形相等，不需要群胚假设。 *)

Definition vertex_edge_comparison@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C}
    (x y : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 1)
    (e0 : (lower x fin_first : X) ≈S lower y fin_first)
    (e1 : (lower x (fin_next fin_first) : X) ≈S lower y (fin_next fin_first))
    (H : T⟦e1⟧Ob ∘ fmap (lower x) (ordinal_step fin_first) ≈
      fmap (lower y) (ordinal_step fin_first) ∘ T⟦e0⟧Ob)
  : x ≈S y.
Proof.
  apply (snd (vertex_simplex_eq_steps x y)).
  exists (λ k, match k as j return
      (lower x j : X) ≈S lower y j with
    | inl tt => e0
    | inr (inl tt) => e1
    | inr (inr a) => match a with end
    end).
  intros [[] | []]. exact H.
Defined.

(** An edge equality gives the arrow square for any parallel endpoint
    witnesses, by independence of specified object transport. *)

(** 边相等对任意平行端点见证给出箭头方块，因为指定对象运输不依赖见证。 *)

Definition vertex_edge_square@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C}
    (x y : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 1)
    (e0 : (lower x fin_first : X) ≈S lower y fin_first)
    (e1 : (lower x (fin_next fin_first) : X) ≈S lower y (fin_next fin_first))
    (H : x ≈S y)
  : T⟦e1⟧Ob ∘ fmap (lower x) (ordinal_step fin_first) ≈
      fmap (lower y) (ordinal_step fin_first) ∘ T⟦e0⟧Ob.
Proof.
  destruct H as [[e H]].
  rewrite (vertex_transport_witness_independent T e0 (e fin_first)),
    (vertex_transport_witness_independent T e1 (e (fin_next fin_first))).
  exact (H _ _ (ordinal_step fin_first)).
Defined.

(** Equality to the rebased arrow supplies the edge square automatically. *)

(** 与调整端点后的箭头相等，自动给出边方块。 *)

Definition vertex_edge_rebased_eq@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C}
    (x y : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 1)
    (e0 : (lower x fin_first : X) ≈S lower y fin_first)
    (e1 : (lower x (fin_next fin_first) : X) ≈S lower y (fin_next fin_first))
    (H : fmap (lower x) (ordinal_step fin_first) ≈
      T⟦e0; fmap (lower y) (ordinal_step fin_first); e1⟧Ar)
  : x ≈S y.
Proof.
  apply (vertex_edge_comparison x y e0 e1).
  rewrite H. apply vertex_rebase_square.
Defined.

(** An arrow gives a one-simplex with exactly its specified endpoints. *)

(** 箭头给出端点恰为其指定端点的一维单形。 *)

Program Definition edge_simplex_resp@{u p +} {X : SetC} {C : Cat}
    (T : Functor (EqGpd X) C) (A B : X)
  : (@HomSet (VertexCat T) A B) →r
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 1
  :=
  {|func f := ⟨⟦ArrowChain f⟧Ch⟩ᵥ
  |}.
Next Obligation.
  intros f g H. apply (vertex_edge_comparison _ _
    (reflexivity (A : X)) (reflexivity (B : X))).
  rewrite !vertex_transport_id, comp_id_l, comp_id_r.
  change (id ∘ f ≈ id ∘ g). rewrite !comp_id_l. exact H.
Defined.

Notation "'△₁[' T ';' A ';' B ']'" := (edge_simplex_resp T A B)
  : hom_scope.

(** The arrow of the constructed simplex is the original arrow. *)

(** 构造单形中的箭头等于原箭头。 *)

Lemma edge_simplex_arrow@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {A B : X}
    (f : (@Hom (VertexCat T)) A B)
  : fmap (lower ((△₁[T; A; B] : _ →r
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 1) f))
      (ordinal_step fin_first) ≈ f.
Proof. change (id ∘ f ≈ f). apply comp_id_l. Defined.

(** Restriction along an ordered pair is the simplex of its image arrow,
    including repeated endpoints and arbitrary order witnesses. *)

(** 沿有序顶点对的限制是其像箭头的单形，包括重复端点及任意顺序见证。 *)

Lemma vertex_edge_restrict@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {n : nat}
    (x : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)
    (i j : Ordinal n) (h : (@Hom [Ord n]) i j)
  : △₁[T; lower x i; lower x j] (fmap (lower x) h) ≈S
      Nᵥ(T)[⟦ArrowChain h⟧Ch]Δ x.
Proof.
  apply (vertex_edge_comparison _ _
    (reflexivity (lower x i : X)) (reflexivity (lower x j : X))).
  rewrite !vertex_transport_id, comp_id_l, comp_id_r.
  transitivity (fmap (lower x) h).
  - apply edge_simplex_arrow.
  - change (fmap (lower x) h ≈
      fmap (lower x) (fmap (⟦ArrowChain h⟧Ch) (ordinal_step fin_first))).
    exact (@functor_fmap_proper _ _ (lower x) _ _ _ _ tt).
Defined.
