From Cats Require Import Cat.Core Instance.Set.Core Instance.Set.Product.

(** * Exponentials of Setoids

    The exponential consists of respectful maps with pointwise equivalence. *)

Definition eval_resp {X Y : SetC} : ProdS (FunS X Y) X →r Y.
Proof.
  unshelve refine (@Build_FunS_resp (ProdS (FunS X Y) X) Y
    (λ p, (fst p) (snd p)) _).
  intros [f x] [g y] [Hfg Hxy].
  transitivity (g x). exact (Hfg x). apply func_proper. exact Hxy.
Defined.

Definition curry_resp {X Y Z : SetC} (f : ProdS Z X →r Y)
  : Z →r FunS X Y.
Proof.
  unshelve refine (@Build_FunS_resp Z (FunS X Y)
    (λ z, @Build_FunS_resp X Y (λ x, f (z, x)) _) _).
  - intros x x' Hx. apply func_proper. split; [reflexivity | exact Hx].
  - intros z z' Hz x. change (f (z, x) ≈S f (z', x)).
    apply func_proper. split; [exact Hz | reflexivity].
Defined.

Local Existing Instance SetCat_HasProduct.

Definition SetCat_HasExponential : @HasExponential SetCat SetCat_HasProduct.
Proof.
  refine (@Build_HasExponential SetCat SetCat_HasProduct
    (λ Y X, FunS X Y) (@curry_resp)
    (λ X Y, eval_resp (X := X) (Y := Y)) _ _).
  - intros X Y Z f g Hfg z x. exact (Hfg (z, x)).
  - intros X Y Z f. split.
    + rewrite cross_η. intros [z x]. reflexivity.
    + intros h Hh z x. rewrite cross_η in Hh. exact (Hh (z, x)).
Defined.
