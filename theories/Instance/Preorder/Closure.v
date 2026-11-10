From Cats.Set.Closure Require Export Core.
From Cats Require Import
  Cat.Preorder
  Cat.Induced
  Cat.Adjunction
  Cat.Monad.Adjunction.

(** * Closure as a Preorder Reflection

    Closed objects form an induced full category of the preorder category.
    Closure is left adjoint to its inclusion. Hom equality identifies
    parallel comparisons, while their Type-valued witnesses remain available;
    no proof irrelevance or equality of functions is required. *)

(** * 作为预序反射的闭包

    闭对象组成预序范畴的诱导全子范畴，闭包是其包含函子的左伴随。Hom 相等
    识别平行比较，但 Type 值见证仍可使用；不需要证明无关性或函数相等。 *)

Local Open Scope cat_scope.
Local Open Scope monad_scope.

Section Reflection.
Context {X : Type} {R : crelation X} `{HR : !PreOrder R}.
Context (c : Closure R).

(** Objects retain a value and its closedness witness. Homs are exactly
    ambient comparisons; no equality of the stored closedness proofs enters
    the construction. *)

(** 对象保留值与闭性见证，Hom 原样取环境中的比较；构造不使用所存闭性证明
    之间的相等。 *)

Definition ClosedCat
  : Cat
  := @InducedCat (PreorderCat R) (∃ x, is_closed c x) (λ x, x.1).

(** The full inclusion forgets only the chosen closedness witness. *)

(** 全包含只忘去选定闭性见证。 *)

Definition ClosedInclusionF
  : Functor ClosedCat (PreorderCat R)
  := @InducedInclusionF (PreorderCat R)
      (∃ x, is_closed c x) (λ x, x.1).

(** Full faithfulness is inherited from the general induced-category
    construction, rather than proved again for this particular predicate. *)

(** 全忠实性继承自一般诱导范畴构造，不为此特定谓词重复证明。 *)

Definition closed_inclusion_fully_faithful
  : is_fully_faithful ClosedInclusionF
  := @induced_inclusion_fully_faithful (PreorderCat R)
      (∃ x, is_closed c x) (λ x, x.1).

(** The reflector chooses [c x] with its flattening witness. Its arrow map
    is precisely monotonicity of closure. *)

(** 反射函子选取 [c x] 及其压平见证，箭头映射恰好就是闭包的单调性。 *)

Program Definition ClosureF
  : Functor (PreorderCat R) ClosedCat
  :=
  {|F0 x := (c x; closure_closed c x)
  ; F1 x y h := closure_monotone c h
  |}.
Next Obligation. repeat intro; exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** The forward hom map restricts along inflation. Its endpoint is a
    closed object, but restriction does not need its closedness witness. *)

(** 正向 Hom 映射沿扩张限制。终点是闭对象，但限制不需要其闭性见证。 *)

Program Definition closure_adjunct_resp (x : X) (y : @Ob ClosedCat)
  : @HomSet ClosedCat (ClosureF x) y →r
      @HomSet (PreorderCat R) x (ClosedInclusionF y)
  :=
  {|func h := closure_restrict c h
  |}.
Next Obligation. repeat intro; exact tt. Defined.

(** The reverse hom map extends to a closed target using its stored witness.
    Both maps compute with the original comparison data. *)

(** 反向 Hom 映射使用所存见证延拓到闭目标；两个映射都用原始比较数据计算。 *)

Program Definition closure_unadjunct_resp (x : X) (y : @Ob ClosedCat)
  : @HomSet (PreorderCat R) x (ClosedInclusionF y) →r
      @HomSet ClosedCat (ClosureF x) y
  :=
  {|func h := closure_extend c y.2 h
  |}.
Next Obligation. repeat intro; exact tt. Defined.

(** The least-extension correspondence assembles the existing adjunction
    interface. Inverse and naturality laws use specified thin hom equality,
    not native equations between comparison witnesses. *)

(** 最小扩张对应组装已有伴随接口。互逆律与自然性使用指定的薄 Hom 相等，
    不要求比较见证之间的原生等式。 *)

Definition ClosureAdjunction
  : ClosureF ⊣ ClosedInclusionF.
Proof.
  refine (AdjunctionFromHom ClosureF ClosedInclusionF
    closure_adjunct_resp closure_unadjunct_resp _ _ _ _);
    repeat intro; exact tt.
Defined.

(** Reuse the general adjunction-to-monad construction. No second collection
    of unit, multiplication or monad-law proofs is chosen here. *)

(** 复用一般的伴随到 Monad 构造，不另选单位、乘法或 Monad 定律证明。 *)

Definition ClosureMonad
  : Monad (PreorderCat R)
  := AdjunctionMonad ClosureAdjunction.

(** Its multiplication is invertible in the specified hom equality. The
    inverse is inflation at the closed extension, so this is an idempotent
    monad without native equality of the iterated closure objects. *)

(** 乘法在指定 Hom 相等下可逆，逆为闭扩张处的扩张见证。因此所得 Monad
    幂等，无须反复闭包对象之间的原生相等。 *)

Definition closure_monad_mul_iso (x : X)
  : @is_iso (PreorderCat R) _ _ (μ[ClosureMonad] x).
Proof.
  exists (closure_inflate c (c x)). split; exact tt.
Defined.

End Reflection.
