From Cats Require Import
  Algebra.Group.Core.

(** * Inherited Algebra Notation

    Importing only the group core exposes the whole algebra notation family
    without opening its scope. Explicit delimiters work before a local open;
    every interpretation reads the complete object's stored evidence. *)

(** * 继承的代数记号

    只导入群核心即可获得整条代数链的记号，但不会自动打开作用域。
    局部打开前可使用显式分隔符；每种解释都读取完整对象保存的见证。 *)

Fail Check (λ (G : Group) (x y : G), x ⋅ y).
Fail Check (λ (G : Group) (x : G), x⁻¹).
Fail Open Scope magma_scope.
Fail Open Scope monoid_scope.

Example delimited_product (M : Magma) (x y : M)
  : (x ⋅ y)%alg = @mul _ (hasMagma M) x y.
Proof. reflexivity. Qed.

Example default_numeral
  : 1 = S O.
Proof. reflexivity. Qed.

Module LocallyOpened.
Local Open Scope algebra_scope.

(** Multiplication and its sections already work at the weakest layer. *)

(** 乘法及其偏应用在最弱层已经可用。 *)

Example inherited_sections (M : Magma) (x y : M)
  : ((x ⋅−) y, (−⋅ y) x) = (x ⋅ y, x ⋅ y).
Proof. reflexivity. Qed.

(** Rewriting uses multiplication's instance and the inherited section
    instances, including composition of maps. No explicit [Proper] proof
    is supplied by these clients. *)

(** 重写直接使用乘法及继承的偏应用实例，包括映射复合；客户端不显式提供
    [Proper] 证明。 *)

Example inherited_product_rewriting (M : Magma) (x x' y y' : M)
    (Hx : x ≈S x') (Hy : y ≈S y')
  : x ⋅ y ≈S x' ⋅ y'.
Proof. rewrite Hx, Hy. reflexivity. Qed.

Example inherited_left_section_rewriting (M : Magma) (x y z : M)
    (H : x ≈S y)
  : ((x ⋅−) ∘r (z ⋅−)) ≈f ((y ⋅−) ∘r (z ⋅−)).
Proof. intro t. rewrite H. reflexivity. Qed.

Example inherited_right_section_rewriting (M : Magma) (x y z : M)
    (H : x ≈S y)
  : ((−⋅ x) ∘r (−⋅ z)) ≈f ((−⋅ y) ∘r (−⋅ z)).
Proof. intro t. rewrite H. reflexivity. Qed.

Example left_associative_grammar (M : Magma) (x y z : M)
  : x ⋅ y ⋅ z = (x ⋅ y) ⋅ z.
Proof. reflexivity. Qed.

(** The stronger layers add only the unit and inverse interpretations. *)

(** 更强的层只新增单位元和逆的解释。 *)

Example inherited_unit (M : Monoid)
  : (1 : M) = @mul_unit _ (hasMonoid M).
Proof. reflexivity. Qed.

(** Unit laws infer their selected structure from the expression. *)

(** 单位律从表达式推断其选定结构。 *)

Example inferred_unit_laws (M : Monoid) (x : M)
  : 1 ⋅ x ⋅ 1 ≈S x.
Proof. rewrite mul_unit_l, mul_unit_r. reflexivity. Qed.

Example inherited_inverse (G : Group) (x : G)
  : x⁻¹ = @inv _ (hasGroup G) x.
Proof. reflexivity. Qed.

Example inverse_precedence (G : Group) (x y : G)
  : x ⋅ y⁻¹ = @mul _ (hasMagma G) x (@inv _ (hasGroup G) y).
Proof. reflexivity. Qed.

Example explicit_natural_numeral
  : 1%nat = S O.
Proof. reflexivity. Qed.

End LocallyOpened.

Fail Check (λ (G : Group) (x y : G), x ⋅ y).
Fail Check (λ (G : Group) (x : G), x⁻¹).

(** All five forms remain available through the explicit delimiter. *)

(** 五类记号在作用域外仍均可通过显式分隔符使用。 *)

Example delimited_group_forms (G : Group) (x y : G)
  : ((x ⋅ y)%alg, ((x ⋅−) y)%alg, ((−⋅ y) x)%alg,
      (1 : G)%alg, (x⁻¹)%alg) =
      (@mul _ (hasMagma G) x y, @mul _ (hasMagma G) x y,
        @mul _ (hasMagma G) x y, @mul_unit _ (hasMonoid G),
        @inv _ (hasGroup G) x).
Proof. reflexivity. Qed.
