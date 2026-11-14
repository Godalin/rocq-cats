From Cats Require Export
  Algebra.Group.Equation
  Algebra.Monoid.Commutative.

Local Open Scope monoid_scope.

(** * Completing Cocycle Equations

    Label the triangles of a tetrahedron by [p=c012], [q=c023],
    [r=c123] and [s=c013]. Its equation is [p ⋅ q ≈S r ⋅ s].
    Knowing three labels determines the fourth in a group. We reuse
    %\coqref{Cats.Algebra.Group.Equation.GroupMulLSolution}
    {%[GroupMulLSolution]%}% and its right-handed counterpart; no
    commutativity is needed for this single equation.

    These are the coefficients appearing in
    %\coqref{Cats.Cat.Diagram.Cocycle.two cocycle tetrahedron}
    {%[two_cocycle_tetrahedron]%}%. Here we isolate their equations before
    constructing a compatible family of simplicial faces.

    The diagram compares two routes from a singleton to the coefficient
    set: the endpoint equality is the equation on the four labels. The
    dashed arrow marks the multiplication factor whose label is sought,
    not a simplicial map or a horn filler. *)

(** * 补全 Cocycle 方程

    将四面体的三角形标为 [p=c012]、[q=c023]、[r=c123]、[s=c013]，
    方程就是 [p ⋅ q ≈S r ⋅ s]。在群中，已知三个标签即可确定第四个。
    这里复用 %\coqref{Cats.Algebra.Group.Equation.GroupMulLSolution}
    {%[GroupMulLSolution]%}% 及其右乘版本；单个方程不需要交换性。

    这就是 %\coqref{Cats.Cat.Diagram.Cocycle.two cocycle tetrahedron}
    {%[two_cocycle_tetrahedron]%}% 中出现的系数。这里先单独处理它们的
    方程，再考虑如何构造相容的单纯形面族。

    图中比较从单点集到系数集的两条路线，其终点相等就是四个标签的方程。
    虚线表示待求标签所在的乘法因子，并非单纯映射或角的填充。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
 & G \arrow[dr,dashed,"{x\mapsto p\cdot x}"] & \\
 \{*\} \arrow[ur,"q"] \arrow[dr,"s"'] && G \\
 & G \arrow[ur,"{x\mapsto r\cdot x}"'] &
\end{tikzcd}
\end{center}% *)

(** ** Four Possible Missing Labels

    Fix a setoid [G] with a chosen group. Each construction retains the
    selected label, its equation and uniqueness in the equality of [G].
    The order of the factors matters; inverse factors are not commuted. *)

(** ** 四种缺失标签

    固定带选定群结构的广集 [G]。每个构造保存选定标签、方程及 [G] 相等下的
    唯一性。因子次序有意义，不能随意交换逆因子的位置。 *)

Section Completion.
Context {G : SetC} `{HG : !Group G}.

(** Solve for [c012], the first factor on the left. *)

(** 求左侧第一因子 [c012]。 *)

Definition Cocycle012Solution (q r s : G)
  : ∃ p : G, is_unique (R := carrier_equiv G)
      (λ p, p ⋅ q ≈S r ⋅ s) p
  := GroupMulRSolution q (r ⋅ s).

(** Solve for [c023], the second factor on the left. *)

(** 求左侧第二因子 [c023]。 *)

Definition Cocycle023Solution (p r s : G)
  : ∃ q : G, is_unique (R := carrier_equiv G)
      (λ q, p ⋅ q ≈S r ⋅ s) q
  := GroupMulLSolution p (r ⋅ s).

(** Solve for [c123]. Symmetry turns the old solution equation into
    the tetrahedron's original orientation. *)

(** 求 [c123]；用对称性将已有解的方程转为四面体原来的方向。 *)

Definition Cocycle123Solution (p q s : G)
  : ∃ r : G, is_unique (R := carrier_equiv G)
      (λ r, p ⋅ q ≈S r ⋅ s) r.
Proof.
  exists (GroupMulRSolution s (p ⋅ q)).1.
  refine {|this := _
          ; that := _
          |}.
  - symmetry. exact (@this _ _ _ _ _ (GroupMulRSolution s (p ⋅ q)).2).
  - intros r H. apply (@that _ _ _ _ _ (GroupMulRSolution s (p ⋅ q)).2 r).
    symmetry. exact H.
Defined.

(** Solve for [c013], keeping the same oriented equation. *)

(** 求 [c013]，仍保留同一方向的方程。 *)

Definition Cocycle013Solution (p q r : G)
  : ∃ s : G, is_unique (R := carrier_equiv G)
      (λ s, p ⋅ q ≈S r ⋅ s) s.
Proof.
  exists (GroupMulLSolution r (p ⋅ q)).1.
  refine {|this := _
          ; that := _
          |}.
  - symmetry. exact (@this _ _ _ _ _ (GroupMulLSolution r (p ⋅ q)).2).
  - intros s H. apply (@that _ _ _ _ _ (GroupMulLSolution r (p ⋅ q)).2 s).
    symmetry. exact H.
Defined.

(** Changing the three known labels preserves the selected first label. *)

(** 三个已知标签的相等保持选定的第一个标签。 *)

Global Instance cocycle012_solution_proper
  : Proper (carrier_equiv G ==> carrier_equiv G ==> carrier_equiv G ==>
      carrier_equiv G) (λ q r s, (Cocycle012Solution q r s).1).
Proof.
  intros q q' Hq r r' Hr s s' Hs. cbn.
  apply monoid_mul_proper.
  - apply monoid_mul_proper; assumption.
  - apply group_inv_proper. exact Hq.
Defined.

(** The second selected label also respects all three inputs. *)

(** 第二个选定标签也保持全部三个输入的相等。 *)

Global Instance cocycle023_solution_proper
  : Proper (carrier_equiv G ==> carrier_equiv G ==> carrier_equiv G ==>
      carrier_equiv G) (λ p r s, (Cocycle023Solution p r s).1).
Proof.
  intros p p' Hp r r' Hr s s' Hs. cbn.
  apply monoid_mul_proper.
  - apply group_inv_proper. exact Hp.
  - apply monoid_mul_proper; assumption.
Defined.

(** Respectfulness compares labels, without comparing uniqueness witnesses. *)

(** 保相等性只比较标签，不比较唯一性见证。 *)

Global Instance cocycle123_solution_proper
  : Proper (carrier_equiv G ==> carrier_equiv G ==> carrier_equiv G ==>
      carrier_equiv G) (λ p q s, (Cocycle123Solution p q s).1).
Proof.
  intros p p' Hp q q' Hq s s' Hs. cbn.
  apply monoid_mul_proper.
  - apply monoid_mul_proper; assumption.
  - apply group_inv_proper. exact Hs.
Defined.

(** The last selected label has the same pointwise preservation law. *)

(** 最后一个选定标签满足同样的逐点保相等律。 *)

Global Instance cocycle013_solution_proper
  : Proper (carrier_equiv G ==> carrier_equiv G ==> carrier_equiv G ==>
      carrier_equiv G) (λ p q r, (Cocycle013Solution p q r).1).
Proof.
  intros p p' Hp q q' Hq r r' Hr. cbn.
  apply monoid_mul_proper.
  - apply group_inv_proper. exact Hr.
  - apply monoid_mul_proper; assumption.
Defined.

End Completion.

(** ** Five Vertices and a Redundant Equation

    Now also assume that the chosen multiplication is commutative.
    Name the ten triangle labels on ordered vertices [0,1,2,3,4] by
    [a=c012], [b=c013], [c=c014], [d=c023], [e=c024], [f=c034],
    [g=c123], [h=c124], [i=c134], [j=c234]. There are five tetrahedra:
    [g⋅i≈j⋅h], [d⋅f≈j⋅e], [b⋅f≈i⋅c], [a⋅e≈h⋅c], [a⋅d≈g⋅b].

    Any four equations imply the fifth. Each proof compares longer products,
    substitutes the four known equations, and cancels one common factor.
    Commutativity is used to move that factor past another label. Thus the
    result explains one consistency check beyond solving a single equation.
    It does not supply faces, their overlap maps or a simplicial horn filler.

    For example, omit the equation on [0,1,2,3]. In the diagram, [H0] through
    [H3] are the four given equations, numbered by the omitted vertex.
    Every solid arrow denotes an equality of products; reassociation is
    implicit where needed. The two solid routes imply the dashed equality.
    Cancelling [f] gives [a⋅d≈g⋅b]. The bottom middle arrow is the only
    exchange of factors. *)

(** ** 五个顶点与冗余方程

    现在额外假设选定乘法交换。将有序顶点 [0,1,2,3,4] 上的十个三角形标签
    依次记为 [a=c012]、[b=c013]、[c=c014]、[d=c023]、[e=c024]、
    [f=c034]、[g=c123]、[h=c124]、[i=c134]、[j=c234]。五个四面体
    分别要求 [g⋅i≈j⋅h]、[d⋅f≈j⋅e]、[b⋅f≈i⋅c]、[a⋅e≈h⋅c]、
    [a⋅d≈g⋅b]。

    任意四条方程推出第五条。每个证明先比较较长的乘积，代入四条已知方程，
    再消去一个公共因子；交换律用于让该因子越过另一标签。因此这里给出
    单个方程求解之外的一项相容性检查，尚不提供各个面、重叠映射或单纯角填充。

    例如缺少 [0,1,2,3] 上的方程。图中 [H0] 到 [H3] 是四条已知方程，
    按省略的顶点编号。每条实线表示乘积的相等，必要的重结合隐含在其中。
    两条实线路线推出虚线相等，再消去 [f] 就得到 [a⋅d≈g⋅b]。
    下方中间箭头是唯一交换因子的位置。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
 (ad)f \arrow[r,dashed] \arrow[d,"{\mathrm{assoc}}"'] &
 (gb)f \arrow[r,"{\mathrm{assoc}}"] &
 g(bf) \arrow[r,"H_2"] & (gi)c \arrow[d,"H_0"] \\
 a(df) \arrow[r,"H_1"'] & a(je) \arrow[r,"{\mathrm{comm}}"'] &
 j(ae) \arrow[r,"H_3"'] & (jh)c
\end{tikzcd}
\end{center}% *)

Section FiveVertices.
Context {G : SetC} `{HG : !Group G} `{HC : !IsCommutativeMonoid G}.
Context (a b c d e f g h i j : G).

(** Recover the equation on vertices [1,2,3,4] by cancelling [c014]. *)

(** 消去 [c014]，恢复顶点 [1,2,3,4] 上的方程。 *)

Lemma cocycle_tetrahedron_1234
    (H1 : d ⋅ f ≈S j ⋅ e) (H2 : b ⋅ f ≈S i ⋅ c)
    (H3 : a ⋅ e ≈S h ⋅ c) (H4 : a ⋅ d ≈S g ⋅ b)
  : g ⋅ i ≈S j ⋅ h.
Proof.
  apply (group_mul_cancel_r c).
  rewrite monoid_assoc, <- H2, <- monoid_assoc, <- H4,
    monoid_assoc, H1, <- (monoid_assoc a j e),
    (monoid_mul_comm a j), monoid_assoc, H3, <- monoid_assoc.
  reflexivity.
Defined.

(** Recover [0,2,3,4] by cancelling [c012]. *)

(** 消去 [c012]，恢复 [0,2,3,4] 上的方程。 *)

Lemma cocycle_tetrahedron_0234
    (H0 : g ⋅ i ≈S j ⋅ h) (H2 : b ⋅ f ≈S i ⋅ c)
    (H3 : a ⋅ e ≈S h ⋅ c) (H4 : a ⋅ d ≈S g ⋅ b)
  : d ⋅ f ≈S j ⋅ e.
Proof.
  apply (group_mul_cancel_l a).
  rewrite <- monoid_assoc, H4, monoid_assoc, H2,
    <- monoid_assoc, H0, monoid_assoc, <- H3,
    <- (monoid_assoc j a e), (monoid_mul_comm j a), monoid_assoc.
  reflexivity.
Defined.

(** Recover [0,1,3,4] by cancelling [c123]. *)

(** 消去 [c123]，恢复 [0,1,3,4] 上的方程。 *)

Lemma cocycle_tetrahedron_0134
    (H0 : g ⋅ i ≈S j ⋅ h) (H1 : d ⋅ f ≈S j ⋅ e)
    (H3 : a ⋅ e ≈S h ⋅ c) (H4 : a ⋅ d ≈S g ⋅ b)
  : b ⋅ f ≈S i ⋅ c.
Proof.
  apply (group_mul_cancel_l g).
  rewrite <- monoid_assoc, <- H4, monoid_assoc, H1,
    <- (monoid_assoc a j e), (monoid_mul_comm a j), monoid_assoc,
    H3, <- monoid_assoc, <- H0, monoid_assoc.
  reflexivity.
Defined.

(** Recover [0,1,2,4] by cancelling [c234]. *)

(** 消去 [c234]，恢复 [0,1,2,4] 上的方程。 *)

Lemma cocycle_tetrahedron_0124
    (H0 : g ⋅ i ≈S j ⋅ h) (H1 : d ⋅ f ≈S j ⋅ e)
    (H2 : b ⋅ f ≈S i ⋅ c) (H4 : a ⋅ d ≈S g ⋅ b)
  : a ⋅ e ≈S h ⋅ c.
Proof.
  apply (group_mul_cancel_l j).
  rewrite <- (monoid_assoc j a e), (monoid_mul_comm j a), monoid_assoc,
    <- H1, <- monoid_assoc, H4, monoid_assoc, H2,
    <- monoid_assoc, H0, monoid_assoc.
  reflexivity.
Defined.

(** Recover [0,1,2,3] by cancelling [c034]. *)

(** 消去 [c034]，恢复 [0,1,2,3] 上的方程。 *)

Lemma cocycle_tetrahedron_0123
    (H0 : g ⋅ i ≈S j ⋅ h) (H1 : d ⋅ f ≈S j ⋅ e)
    (H2 : b ⋅ f ≈S i ⋅ c) (H3 : a ⋅ e ≈S h ⋅ c)
  : a ⋅ d ≈S g ⋅ b.
Proof.
  apply (group_mul_cancel_r f).
  rewrite monoid_assoc, H1, <- (monoid_assoc a j e),
    (monoid_mul_comm a j), monoid_assoc, H3,
    <- monoid_assoc, <- H0, monoid_assoc, <- H2, <- monoid_assoc.
  reflexivity.
Defined.

End FiveVertices.
