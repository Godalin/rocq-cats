From Cats Require Export
  Instance.Set.Simplicial.Vertex.

Local Open Scope nat_scope.

(** * Edges and Endpoint Transport

    Rebase an arrow along the specified object transports. The comparison
    of one-simplices uses these transports at their two endpoints. *)

(** * 边与端点运输

    沿指定对象运输调整箭头的端点；一维单形的比较使用两个端点上的这些运输。 *)

Section Rebase.
Context {X : SetC} {C : Cat} (T : Functor (EqGpd X) C).

(** Change both endpoints by precomposition and inverse postcomposition. *)

(** 通过预合成及与逆的后合成，调整两个端点。 *)

Program Definition vertex_rebase_resp {A B A' B' : X}
    (p : A ≈S A') (q : B ≈S B')
  : (@HomSet (VertexCat T) A' B') →r (@HomSet (VertexCat T) A B)
  :=
  {|func f := T⟦symmetry q⟧Ob ∘ f ∘ T⟦p⟧Ob
  |}.
Next Obligation. intros f g H. rewrite H. reflexivity. Defined.

(** The rebased arrow forms the required transport square. *)

(** 调整后的箭头满足所需运输方块。 *)

Lemma vertex_rebase_square {A B A' B' : X}
    (p : A ≈S A') (q : B ≈S B') (f : (@Hom (VertexCat T)) A' B')
  : T⟦q⟧Ob ∘ vertex_rebase_resp p q f ≈ f ∘ T⟦p⟧Ob.
Proof.
  change (T⟦q⟧Ob ∘ (T⟦symmetry q⟧Ob ∘ f ∘ T⟦p⟧Ob) ≈ f ∘ T⟦p⟧Ob).
  rewrite <- !comp_assoc, vertex_transport_inv, comp_id_l. reflexivity.
Defined.

(** Reflexive endpoint changes preserve the original arrow. *)

(** 自反端点调整保持原箭头。 *)

Lemma vertex_rebase_id {A B : X} (p : A ≈S A) (q : B ≈S B)
    (f : (@Hom (VertexCat T)) A B)
  : vertex_rebase_resp p q f ≈ f.
Proof.
  change (T⟦symmetry q⟧Ob ∘ f ∘ T⟦p⟧Ob ≈ f).
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

End Rebase.

Notation "T '⟦' p ';' f ';' q '⟧Ar'" := (vertex_rebase_resp T p q f)
  (at level 8, left associativity) : hom_scope.

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
