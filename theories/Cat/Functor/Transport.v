From Cats Require Export
  Cat.Functor.Core
  Cat.Natural
  Cat.Isomorphism.

(** * Changing a Functor's Object Representatives

    A chosen isomorphism at each object transports the arrow action by
    conjugation. The comparison is a natural isomorphism, without equality
    of object maps or law records. *)

(** * 改变函子的对象代表

    每个对象上的选定同构通过共轭运输态射作用。比较是自然同构，不要求对象
    映射或定律记录相等。 *)

Section Transport.
Context {C D : Cat} (F : Functor C D) (j : @Ob C → @Ob D)
    (e : ∀ X, j X ≅ F X).

(** Change representatives, keeping the supplied inverse maps transparent. *)

(** 改变代表，并保持给定逆映射透明。 *)

Program Definition TransportF
  : Functor C D
  :=
  {|F0 := j
  ; F1 X Y f := (e Y).2.1 ∘ fmap F f ∘ (e X).1
  |}.
Next Obligation. intros f g H. rewrite H. reflexivity. Defined.
Next Obligation.
  rewrite functor_id, comp_id_r. exact (fst (e X).2.2).
Defined.
Next Obligation.
  rewrite functor_comp, !comp_assoc.
  rewrite <- (comp_assoc (e Y).1), (snd (e Y).2.2), comp_id_l.
  reflexivity.
Defined.

(** The supplied forward maps form the comparison to the original functor. *)

(** 给定正向映射构成到原函子的比较。 *)

Program Definition TransportN
  : TransportF ⇒ F
  :=
  {|nt X := (e X).1
  |}.
Next Obligation.
  rewrite <- !comp_assoc, (snd (e Y).2.2), comp_id_l. reflexivity.
Defined.

(** No new inverse choice is introduced by the natural comparison. *)

(** 自然比较不引入新的逆选择。 *)

Definition TransportIso
  : TransportF ≅N F
  := (TransportN; λ X, (e X).2).

End Transport.

(** Naturality can be checked across natural boundary maps. Only the
    outgoing boundary must be invertible; the incoming one may be any
    natural transformation. This retains the supplied component family. *)

(** 可跨自然边界映射检查自然性。仅要求出边界可逆，入边界可为任意自然
    变换；结论保留给定分量族。 *)

Lemma nt_naturality_boundary {C D : Cat}
    {F G F' G' : Functor C D} (i : F' ⇒ F) (j : G' ≅N G)
    (β : F ⇒ G) (a : ∀ X, Hom (F' X) (G' X))
    (Ha : ∀ X, j.1 X ∘ a X ≈ β X ∘ i X)
    {X Y : @Ob C} (f : Hom X Y)
  : a Y ∘ fmap F' f ≈ fmap G' f ∘ a X.
Proof.
  apply (iso_cancel_l (j.1 Y; j.2 Y)).
  rewrite <- comp_assoc, Ha, comp_assoc, (nt_naturality i f).
  rewrite <- comp_assoc, (nt_naturality β f), comp_assoc, <- Ha.
  rewrite <- !comp_assoc, (nt_naturality j.1 f). reflexivity.
Qed.
