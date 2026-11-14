From Cats Require Export
  Instance.Set.Vertex.Core.

(** * Relabelling Diagrams by Specified Equality *)

(** * 沿指定相等重标记图式 *)

Section Relabel.
Context {X : SetC} {C : Cat} (T : Fct (EqGpd X) C).

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

(** Transport squares determine the rebased arrow; no inverse for the
    original arrow is required. *)

(** 运输方块确定调整后的箭头，不要求原箭头可逆。 *)

Lemma vertex_rebase_of_square {A B A' B' : X}
    (p : A ≈S A') (q : B ≈S B')
    (f : (@Hom (VertexCat T)) A B) (g : (@Hom (VertexCat T)) A' B')
    (H : T⟦q⟧Ob ∘ f ≈ g ∘ T⟦p⟧Ob)
  : f ≈ vertex_rebase_resp p q g.
Proof.
  change (f ≈ T⟦symmetry q⟧Ob ∘ g ∘ T⟦p⟧Ob).
  rewrite comp_assoc, <- H, <- comp_assoc, vertex_transport_inv, comp_id_l.
  reflexivity.
Defined.

(** Relabelling preserves composition by cancellation of the intermediate
    transport, independently of its equality witness. *)

(** 通过消去中间运输，重标记保持复合，并且不依赖相等见证。 *)

Lemma vertex_rebase_comp {A B D A' B' D' : X}
    (p : A ≈S A') (q : B ≈S B') (r : D ≈S D')
    (f : (@Hom (VertexCat T)) A' B') (g : (@Hom (VertexCat T)) B' D')
  : vertex_rebase_resp p r (g ∘ f) ≈
      vertex_rebase_resp q r g ∘ vertex_rebase_resp p q f.
Proof.
  change (T⟦symmetry r⟧Ob ∘ (g ∘ f) ∘ T⟦p⟧Ob ≈
    (T⟦symmetry r⟧Ob ∘ g ∘ T⟦q⟧Ob) ∘
      (T⟦symmetry q⟧Ob ∘ f ∘ T⟦p⟧Ob)).
  rewrite !comp_assoc, <- (comp_assoc T⟦q⟧Ob T⟦symmetry q⟧Ob),
    vertex_transport_inv, comp_id_l. reflexivity.
Defined.

(** A transport square compares arrows after relabelling both to the same
    endpoints. Parallel transport witnesses need not be equal. *)

(** 运输方块使调整到相同端点的箭头相等，不要求平行运输见证相等。 *)

Lemma vertex_rebase_eq {A B A' B' A'' B'' : X}
    (p : A ≈S A') (q : B ≈S B')
    (r : A ≈S A'') (s : B ≈S B'')
    (e : A' ≈S A'') (d : B' ≈S B'')
    (f : (@Hom (VertexCat T)) A' B')
    (g : (@Hom (VertexCat T)) A'' B'')
    (H : T⟦d⟧Ob ∘ f ≈ g ∘ T⟦e⟧Ob)
  : vertex_rebase_resp p q f ≈ vertex_rebase_resp r s g.
Proof.
  apply vertex_rebase_of_square.
  rewrite (vertex_transport_comp T q d s), comp_assoc,
    vertex_rebase_square, <- comp_assoc, H, comp_assoc.
  apply comp_proper; [reflexivity |].
  symmetry. apply vertex_transport_comp.
Defined.

(** Any diagram can be relabelled along specified vertex equalities.
    Coherence comes solely from object transport. *)

(** 任意图式可沿指定顶点相等重标记；相干性完全来自对象运输。 *)

Program Definition VertexRelabelF {J : Cat}
    (F : Fct J (VertexCat T)) (v : @Ob J → X)
    (e : ∀ j, v j ≈S F j)
  : Fct J (VertexCat T)
  :=
  {|F0 := v
  ; F1 i j f := vertex_rebase_resp (e i) (e j) (fmap F f)
  |}.
Next Obligation.
  intros f g H. rewrite (@functor_fmap_proper _ _ F X0 Y f g H).
  reflexivity.
Defined.
Next Obligation.
  change (T⟦symmetry (e X0)⟧Ob ∘ fmap F id ∘ T⟦e X0⟧Ob ≈ id).
  rewrite functor_id, comp_id_r. apply vertex_transport_inv.
Defined.
Next Obligation.
  transitivity (vertex_rebase_resp (e X0) (e Z) (fmap F f ∘ fmap F g)).
  - exact (@func_proper _ _ (vertex_rebase_resp (e X0) (e Z)) _ _
      (@functor_comp _ _ F X0 Y Z f g)).
  - exact (vertex_rebase_comp (e X0) (e Y) (e Z) (fmap F g) (fmap F f)).
Defined.

(** The relabelled diagram equals the original through the prescribed
    transport squares, without equality of functor records. *)

(** 重标记后的图式通过指定运输方块等于原图式，不比较函子记录的原生相等。 *)

Definition vertex_relabel_eq {J : Cat}
    (F : Fct J (VertexCat T)) (v : @Ob J → X)
    (e : ∀ j, v j ≈S F j)
  : VertexDiagramEq T (VertexRelabelF F v e) F.
Proof. exists e. intros i j f. apply vertex_rebase_square. Defined.

End Relabel.

Notation "T '⟦' p ';' f ';' q '⟧Ar'" := (vertex_rebase_resp T p q f)
  (at level 8, left associativity) : hom_scope.
