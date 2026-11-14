From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Arrow.Core
  Cat.Diagram.Discrete
  Cat.Coend.Construction
  Instance.Set.Core
  Instance.Set.Colimit
  Instance.Set.Coequalizer.

(** * Coends in the Category of Setoids *)

(** * 广集范畴中的 coend *)

(** Reuse the existing generated indexed sums and coequalizers through the
    abstract opposite-end constructor. Sufficient bounds are [o,h ≤ u ≤ p]:
    arrow-indexed sums fit the carrier, and generated equality retains its
    intermediate representatives. The index category's hom-equality level [e]
    stays independent. Neither quotient types nor resizing axioms are used.
    The choice is explicitly enabled; this is not a claim that the entire
    category of setoids at these sizes is itself a small indexing category. *)

(** 通过抽象反 end 构造，复用已有的生成指标和及余等化子。充分大小界为
    [o,h ≤ u ≤ p]：按箭头索引的和容纳于载体，生成相等保留其中间代表。指标范畴
    的 Hom 相等层级 [e] 保持独立。不使用商类型或大小重设公理。该选择须显式启用，
    不声称这些大小的整个广集范畴本身就是小指标范畴。 *)

Definition SetCat_Coend@{o h e u p +} (C : Cat@{o h e _ _})
    (F : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}))
  : HasCoend SetCat F
  := @CoproductsCoequalizerCoend C SetCat F
      (SetCat_IndexedCoproductColimit (DiscreteF (CoendDiag F)))
      (SetCat_IndexedCoproductColimit (DiscreteF (CoendSources F)))
      SetCat_HasCoequalizer.
