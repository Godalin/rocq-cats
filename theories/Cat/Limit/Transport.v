From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core
  Cat.Limit.Core.

(** * Transporting Limiting Cones *)

(** * 运输极限锥 *)

(** Pointwise equal cone legs have the same universal property; their
    naturality witnesses need not be equal. *)

(** 逐点相等的锥腿具有相同泛性质；不要求自然性见证相等。 *)

Definition limit_cone_equiv {J C : Cat} {D : Functor J C} {L : @Ob C}
    {κ μ : L ⇒Δ D} (Hκ : is_limit κ) (H : κ ≈N μ)
  : is_limit μ.
Proof.
  intros X ν. destruct (Hκ X ν) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - intros j. cbn. rewrite <- (H j). exact (@this _ _ _ _ _ Hh j).
  - intros g Hg. apply (@that _ _ _ _ _ Hh).
    intros j. cbn. rewrite (H j). exact (Hg j).
Defined.

(** An invertible diagram transformation carries a limiting cone to a
    limiting cone. Mediators retain their original computational arrows. *)

(** 可逆图式自然变换将极限锥送到极限锥；中介保留原来的可计算箭头。 *)

Definition limit_transport {J C : Cat} {D E : Functor J C}
    (α : D ⇒ E) (Hα : α ⦂ D ≅N E) {L : @Ob C}
    {κ : L ⇒Δ D} (Hκ : is_limit κ)
  : is_limit (α ∘Nv κ).
Proof.
  intros X μ.
  destruct (Hκ X ((α ^-1N Hα) ∘Nv μ)) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - intros j.
    change ((α j ∘ κ j) ∘ h ≈ μ j).
    rewrite comp_assoc, (@this _ _ _ _ _ Hh j).
    change (α j ∘ ((Hα j).1 ∘ μ j) ≈ μ j).
    rewrite <- comp_assoc, (snd (Hα j).2), comp_id_l. reflexivity.
  - intros g Hg. apply (@that _ _ _ _ _ Hh). intros j.
    change (κ j ∘ g ≈ (Hα j).1 ∘ μ j).
    rewrite <- (Hg j).
    change (κ j ∘ g ≈ (Hα j).1 ∘ ((α j ∘ κ j) ∘ g)).
    rewrite <- !comp_assoc, (fst (Hα j).2), comp_id_l. reflexivity.
Defined.

(** Transport a selected limit along an invertible diagram transformation,
    keeping its selected apex and mediator data. *)

(** 沿可逆图式自然变换运输选定极限，保留其选定顶点及中介数据。 *)

Program Definition TransportedLimit {J C : Cat} {D E : Functor J C}
    (α : D ⇒ E) (Hα : α ⦂ D ≅N E) `{HL : !HasLimit C D}
  : HasLimit C E
  :=
  {|Lim := lim D
  ; limit_cone := α ∘Nv πlim[D]
  |}.
Next Obligation.
  exact (limit_transport α Hα (limit_universal D)).
Defined.
