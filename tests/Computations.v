From Cats Require Import Cat.Core DTT.CwF.
From Cats Require Import Instance.Set.Core Instance.Set.Terminal Instance.Set.Fam.
From Cats Require Import Instance.Set.FamSection Instance.Set.CwF.

Module CodeConversion.

Program Definition Codes : SetC :=
  {| carrier := unit; carrier_equiv _ _ := unit |}.
Next Obligation. split; red; intros; exact tt. Defined.
Program Definition Values : SetC := {| carrier := bool; carrier_equiv := eq |}.

(** Conversion examines its equality witness, so opacity in the family or
    function equivalence operations would prevent this computation. *)
Program Definition Decode : FamS Codes :=
  {| fam _ := Values
   ; transpS x y p := match p with tt => id_resp end |}.
Next Obligation. destruct p. reflexivity. Defined.
Next Obligation. destruct p, q, r. reflexivity. Defined.

Program Definition A : UnitS →r Codes := {| func _ := tt |}.
Next Obligation. intros x y p. exact tt. Defined.
Program Definition t : SectionS Decode[A]S := {| section _ := false |}.
Next Obligation. reflexivity. Defined.

Definition T := CodeTyTmF Decode.
Example composition_conversion_computes :
  (ty_sub_comp T id_resp id_resp A ▸[T]
    t[id_resp]Tm[T][id_resp]Tm[T]) tt = false.
Proof. reflexivity. Qed.

End CodeConversion.
