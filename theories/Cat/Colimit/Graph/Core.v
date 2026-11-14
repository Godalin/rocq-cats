From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Coequalizer
  Cat.Limit.Graph.Core
  Cat.Limit.Reindex.
From Cats Require Export
  Cat.Coproduct.Indexed.

(** * Colimits Specified by Graph Generators

    Reversing paths reduces the construction to original graph limits in the
    opposite category. Only vertices and reversed generators index coproducts;
    there is no coproduct over every path. *)

(** * 由图生成元指定的余极限

    路径反转将构造归约到反范畴中的原图极限；余积仅由顶点与反向生成边索引，
    不需要对所有路径取余积。 *)

(** Use vertex and generator-source coproduct choices to obtain one
    free-diagram colimit from the original opposite graph construction. *)

(** 用顶点与生成边源对象余积选择，通过原反图构造得到单个自由图式余极限。 *)

Program Definition GraphCoproductsCoequalizerColimit {G : Graph} {C : Cat}
    (D : Fct (FreeCat G) C)
    `{HO : !HasColimit C (DiscreteF (λ x, D x))}
    `{HG : !HasColimit C
      (DiscreteF (λ a : GraphEdges (G^opG), D a.2.1))}
    `{HE : !HasCoequalizer C}
  : HasColimit C D
  :=
  {|hasOpLimit := @ReindexedLimit _ _ (C^op) (OpFreeF G)
      (op_free_full G) (op_free_essentially_surjective G) (D^opF)
      (@GraphProductsEqualizerLimit (G^opG) (C^op)
        (D^opF ∘F OpFreeF G)
        (@IndexedCoproductOpProduct C _ (λ x, D x) HO)
        (@IndexedCoproductOpProduct C _
          (λ a : GraphEdges (G^opG), D a.2.1) HG)
        (@hasOpEqualizer C HE))
  |}.

(** Select all free-shape colimits from vertex and generator coproducts. *)

(** 从顶点与生成边余积选择自由形状的全部余极限。 *)

Program Definition GraphCoproductsCoequalizerColimits {G : Graph} {C : Cat}
    `{HO : !HasColimitsOfShape C (DiscreteCat (@Vertex G))}
    `{HG : !HasColimitsOfShape C (DiscreteCat (GraphEdges (G^opG)))}
    `{HE : !HasCoequalizer C}
  : HasColimitsOfShape C (FreeCat G)
  :=
  {|hasOpLimits := @ReindexedLimits _ _ (C^op) (OpFreeF G)
      (op_free_full G) (op_free_essentially_surjective G)
      (@GraphProductsEqualizerLimits (G^opG) (C^op)
        (@DiscreteColimitsOpLimits C _ HO)
        (@DiscreteColimitsOpLimits C _ HG) (@hasOpEqualizer C HE))
  |}.
