From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Cartesian
  Cat.Natural
  Cat.Terminal
  Cat.Product.Core
  Cat.Equalizer
  Cat.Pullback
  Cat.Exponential.Core
  Cat.Limit.Core
  Cat.Limit.Preservation
  Cat.Limit.Terminal
  Cat.Limit.Product
  Cat.Limit.Equalizer
  Cat.Limit.Pullback.

(** * Exponentiation Preserves Existing Limits *)

(** * 指数保持已有极限 *)

Section ExponentialLimits.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Apply the right-adjoint theorem to a specified limiting cone. No choice
    of all limits or terminal object is required. *)

(** 将右伴随定理用于指定极限锥，不要求选择全部极限或终对象。 *)

Definition exponential_preserves_limit (A : @Ob C) {J : Cat}
    {D : Fct J C} {L : @Ob C} {κ : L ⇒Δ D} (Hκ : is_limit κ)
  : is_limit (MapCone (-^ A) κ)
  := right_adjoint_preserves_limit (ProdExpAdj A) Hκ.

(** Any terminal object remains terminal after exponentiation. *)

(** 任意终对象取指数后仍为终对象。 *)

Definition exponential_preserves_terminal (A : @Ob C) {T : @Ob C}
    (HT : is_terminal T)
  : is_terminal (T ^ A)
  := right_adjoint_preserves_terminal (ProdExpAdj A) HT.

(** Exponentiation preserves the full property of a candidate product. *)

(** 指数保持候选积的完整泛性质。 *)

Definition exponential_preserves_product (A : @Ob C) {X Y P : @Ob C}
    {p : Hom P X} {q : Hom P Y} (H : is_product X Y P p q)
  : is_product (X ^ A) (Y ^ A) (P ^ A)
      (fmap (-^ A) p) (fmap (-^ A) q)
  := right_adjoint_preserves_product (ProdExpAdj A) H.

(** Preserve an existing equalizer; a CCC need not have all equalizers. *)

(** 保持已有等化子；CCC 不必具有全部等化子。 *)

Definition exponential_preserves_equalizer (A : @Ob C) {X Y E : @Ob C}
    {f g : Hom X Y} {e : Hom E X} (H : is_equalizer f g E e)
  : is_equalizer (fmap (-^ A) f) (fmap (-^ A) g)
      (E ^ A) (fmap (-^ A) e)
  := right_adjoint_preserves_equalizer (ProdExpAdj A) H.

(** Preserve an existing pullback, under its candidate universal property. *)

(** 在候选泛性质的假设下保持已有拉回。 *)

Definition exponential_preserves_pullback (A : @Ob C)
    {X Y Z P : @Ob C} {f : Hom X Z} {g : Hom Y Z}
    {p : Hom P X} {q : Hom P Y} (H : is_pullback f g P p q)
  : is_pullback (fmap (-^ A) f) (fmap (-^ A) g) (P ^ A)
      (fmap (-^ A) p) (fmap (-^ A) q)
  := right_adjoint_preserves_pullback (ProdExpAdj A) H.

(** Finite-product preservation follows from the same adjunction. This
    selected proof remains explicitly enabled. *)

(** 有限积保持性来自同一个伴随；此选定证明仍须显式启用。 *)

Program Definition ExponentialF_IsCartF `{HT : !HasTerminal C}
    (A : @Ob C)
  : IsCartF (-^ A) HT HP
  :=
  {|functor_terminal := exponential_preserves_terminal A terminal_universal
  ; functor_product X Y := exponential_preserves_product A product_universal
  |}.

End ExponentialLimits.
