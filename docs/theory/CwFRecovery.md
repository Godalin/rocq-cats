# Recovering context extension from representation

Fix a family-valued presheaf T, a context Γ and a type A over it. At Δ, the
pair presheaf consists of a substitution into Γ together with a term of the
substituted A. A context extension represents this presheaf. Conversely, a
representing object and its universal pair supply a projection, generic term
and pairing operation satisfying the extension laws.
[Context representation](../../theories/DTT/Context/Representation.v)

## Independent universe levels

A native hom-setoid representation needs compatible sizes. The universal-pair
formulation permits independent sizes and yields a representation after the
appropriate lifts. The proofs retain the selected mediators and compare them
with the specified setoid equality.
[Lifted representation](../../theories/DTT/Context/LiftedRepresentation.v)

## Recovering display structure

Start with a type presheaf and selected display projections. Sections give
terms, and cartesian squares induce their substitution. Comprehension over
the category of elements supplies this display structure for the selected
types. To apply a comprehension with a different base, supply a comparison
of projections and transport the chosen data. Choosing type codes from an
arbitrary total category is additional input.
[Display data](../../theories/DTT/Display/Core.v) · [Section terms](../../theories/DTT/Display/Section.v) · [Representation](../../theories/DTT/Display/Representation.v) · [Comprehension](../../theories/DTT/Display/Comprehension.v)

Starting with T and chosen context extensions also gives a canonical
interpretation in the display presentation. Compare the induced section
terms and their pairing operations under reindexing.
[Interpretation](../../theories/DTT/Display/Interpretation.v) · [Context elements](../../theories/DTT/Context/Elements.v) · [Pair comparison](../../theories/DTT/Context/PairComparison.v)

## Comprehension over chosen type elements

[Elements](../../theories/Instance/Set/Elements.v) constructs `ElementsCat P`
for a fixed `P : Fct (C^op) SetCat`. Objects are pairs `(Γ,A)`; an arrow
from `(Γ,A)` to `(Δ,B)` retains `σ : Hom Γ Δ` and `A ≈S fmap P σ B`.
Arrow equality compares the base arrows, keeping the Type-valued element
witnesses as data. Every arrow is cartesian for `ElementsBaseF P`: its
element equality supplies the factor's equality, while the prescribed base
factor determines its hom-equality class. Canonical restriction therefore
provides chosen cartesian lifts, with no new global model selection.

A functor `T : Fct (ElementsCat P) C`, a natural projection
`π : T ⇒ ElementsBaseF P`, and `is_comprehension π` suffice as input.
`ElementsComprehension` supplies the canonical lifts to assemble the existing
comprehension interface. No independently chosen cleavage is required.
[Display/Comprehension](../../theories/DTT/Display/Comprehension.v) then defines
`Comprehension_HasDisplay P K`: display objects and projections come from K;
conversion and substitution lifts are the images of vertical equality arrows
and canonical element restrictions. Functor identity, composition and
respectfulness derive all conversion/lift coherence laws. The given
comprehension property supplies the display pullbacks. With an independent
`HasTerminal C`, `ComprehensionCwF P K` reuses the existing display recovery.

Conversely, `DisplayElementsComprehension` extends a supplied display
structure along every element arrow: first convert its source type, then
apply the display lift. The existing pullback-transport theorem supplies the
comprehension property along the conversion isomorphism. The display round
trip preserves projection, conversion and lifts in the specified hom equality.
The comprehension round trip has a transparent natural isomorphism
`comprehension_display_iso` between its total-space functor and the original
`ExtF K`; `comprehension_display_projection` preserves the projection.
No equality of functor records, proof fields or chosen cleavages is asserted.
`display_iff_elements_comprehension` records mutual constructibility with P
fixed, rather than a category equivalence for arbitrary comprehension.

This criterion explicitly assumes the type-element presentation. Its vertical
endomorphisms have identity base and hence are equal to identity in the
specified hom equality; an arbitrary total category need not have this
property. For comprehension on a general `E → C`, the next step must supply
an interpretation of the chosen type elements in E, with coherent base
comparison and cartesian preservation. Such interpretation and any stronger
comparison hypotheses are not inferred from fullness or from arbitrary
vertical isomorphisms.

## Restriction across a natural base comparison

The general prerequisite lives in
[Comprehension](../../theories/Cat/Comprehension.v). Given projections
`P : Fct E B`, `Q : Fct D B`, an interpretation `S : Fct D E`, a natural
isomorphism `β : (P ∘F S) ≅N Q`, and `π : T ⇒ P`, it forms
`ComprehensionRestrictionN S β π := β.1 ∘Nv (π ∘Nr S)`.
Whiskering and vertical composition supply naturality; no object or functor
record equality is needed.

`comprehension_restrict_universal` assumes `is_comprehension π` and explicitly
requires `S` to send each Q-cartesian arrow to a P-cartesian arrow. The source
property supplies a pullback; naturality of β identifies its base boundary.
[Pullback](../../theories/Cat/Pullback.v) transports this square using the existing
`pullback_base_iso` and the new `pullback_postcompose_mono`. Postcomposition
needs only a monic outgoing boundary; changing the other base object needs
an invertible incoming boundary. `pullback_base_boundary` packages both steps.
The cone transport and `iso_mono` cancellation remain transparent even when
the original mediator computes from a Type-valued cone witness.

`RestrictedComprehension` adds exactly a supplied `HasCartLift Q`. Source
chosen lifts, fullness and essential surjectivity are unnecessary. This is
an independent general prerequisite: it does not construct a type presheaf
or an interpretation from arbitrary comprehension. Specializing to
`D := ElementsCat A`, `Q := ElementsBaseF A` still requires the interpretation,
base comparison and cartesian preservation; element theory then supplies the
target lifts. The next section supplies the specialized display/CwF construction.

## Interpreted type elements

[Display/Interpretation](../../theories/DTT/Display/Interpretation.v) specializes
the general restriction to a fixed type presheaf P. Its explicit inputs are
an interpretation `S : Fct (ElementsCat P) E`, source projections
`R,T : Fct E C`, a natural isomorphism
`β : (R ∘F S) ≅N ElementsBaseF P`, a projection `π : T ⇒ R` satisfying
`is_comprehension π`, and cartesianness of every interpreted element arrow.
The latter is exactly cartesian preservation here, since all element arrows
are cartesian. No source cleavage or fullness assumption is needed.

`InterpretedElementsComprehension` uses the canonical element lifts with
`RestrictedComprehension`. `InterpretedElements_HasDisplay` and, with an
independent terminal choice, `InterpretedCwF` reuse the existing recovery.
The display of `(Γ,A)` is `T (S (Γ,A))`; its projection is
`β.1 (Γ,A) ∘ π (S (Γ,A))`. Conversion and restriction act by interpreting
the corresponding element arrow and applying T. These formulas retain the
given comparison rather than replacing it by native object equality.

`interpreted_display_iso` compares the recovered total-space functor with
`T ∘F S` by the existing transparent natural isomorphism.
`interpreted_display_projection` preserves projection across β. The result
does not infer P, S, β or cartesian preservation from arbitrary comprehension,
and makes no claim of equivalence with the whole source category E.
Computational witnesses remain transparent; concrete reductions also depend
on the supplied interpretation, inverse and universal-property witnesses.

The general pairing laws in
[Context/Extension](../../theories/DTT/Context/Extension.v) use the context-extension
universal property directly. `context_pair_comp` composes the generic-term
comparison with substitution coherence; `context_pair_inj` reflects the supplied
hom equality through the two generic-term equations. Neither law needs the
native Hom representation in a common `SetCat`. Their mathematical statements,
arguments and opacity remain unchanged; only their universe constraints weaken.
Eight fixed regressions explicitly put original
type/term carrier and equality levels above both context hom levels, and check
both orders for these laws and the context-display/comprehension clients.

The separate native representation isomorphisms retain their common-size
boundaries. No representation API or chosen computational data is changed.
Canonical context interpretation can reuse these general laws together with
the explicit interpretation hypotheses described above.

## Canonical context interpretation

[Context/Elements](../../theories/DTT/Context/Elements.v) starts with a supplied
family-valued presheaf T and chosen context extensions. `ContextElementsF`
interprets its type elements in `ContextTypeCat T`: the base map is the
element map's base, and the extension map is the existing coherent display
action. The identity-component base natural isomorphism compares functors;
the existing display pullbacks prove cartesian preservation. The accepted
conditional theorem then gives comprehension and displays, with an independent
terminal choice for `ContextElementsCwF`. Projection, conversion and restriction
agree with the original data in the specified hom equality; a transparent
natural isomorphism compares the recovered and interpreted total functors.

The original term and recovered section setoids retain separate sizes.
`context_elements_term_resp` and its inverse transport only the right-inverse
witness at the projection boundary; their round trips use the existing
term–section correspondence. Both comparisons commute with conversion
and substitution. The inverse laws reuse the general `iso_square_inv` after
lifting the fibers, then lower its equality witness. No additional semantic
input or terminal choice is needed for these laws; six further strict checks
fix the original input levels in both orders.
`context_elements_term_iso` raises both carriers and equality
witnesses independently before packaging these maps in a common `SetCat`.
A native isomorphism in one `SetCat` requires common carrier and equality
bounds. The lifted comparison works in both strict orders without resizing.
Sixteen fixed checks explicitly place the original type/term carrier and
equality levels above both context Hom levels, while recovered sections stay
below the auxiliary law bound. The pointwise stage proves fiberwise comparison
and its coherence in both directions, without asserting equality of CwF records or
equivalence with the entire context-type category.

[Context/Comparison](../../theories/DTT/Context/Comparison.v) now assembles
these pointwise comparisons into a natural isomorphism of the primary
type-and-term functors. Both sides are postcomposed with the explicit
[FamLiftF](../../theories/Instance/Set/Fam/Lift.v); only fiber carriers and
equality witnesses are raised, while the type base stays fixed.
`ContextElementsFiberMap` and `ContextElementsFiberInvMap` use the accepted
conversion laws as fixed-base family maps. The fixed-base embedding sends
their explicit inverse to the family category, substitution coherence gives
`ContextElementsTyTmN`, and the general natural-inverse construction gives
`ContextElementsTyTmInvN`. All component maps and chosen inverses remain
transparent. This compares the primary functors up to natural isomorphism;
it does not identify CwF records or prove an equivalence with the entire
context-type category. Chosen context extensions suffice for this comparison;
the separate terminal choice is still required to assemble complete CwFs.

Twelve permanent strict configurations fix the original type bases above
both common raised fiber bounds, in both hom orders. Separate temporary
controls place the bases below the raised bounds, reject four downward
carrier/equality bounds, and test the missing-input and explicit-choice
boundaries. Boolean Code/El clients check native component/inverse
computations, nontrivial conversion and substitution, distinguishable
Type-valued base-equality witnesses, naturality and the specified inverse
laws. Independent exact-source copies and assumption reports remain outside
the library.

[Context/Section](../../theories/DTT/Context/Section.v) supplies the general
pairing bridge used by the canonical comparison below. For any term of
`A[σ]Ty[T]`, `context_lift_term_section` identifies the substitution lift
composed with its section with the universal pair `⟨σ; t⟩[T,A]` in hom
equality. `context_lift_section_term` gives the corresponding equation for
an arbitrary section after extracting its term. The term need not lie in
the image of substitution. Both laws reuse existing lift/pair compatibility
and section inverse laws, with explicit chosen context extensions and no
terminal choice. They impose no native common term/Hom universe bound.
Four permanent strict checks fix the larger original input levels in both
orders. The canonical specialization below reuses these prerequisites and
aligns the recovered projection explicitly when comparing generic terms.

The canonical specialization in
[Context/Elements](../../theories/DTT/Context/Elements.v) now compares pairing
and generic terms as well. Let R be the recovered type-and-term functor,
with its explicitly chosen recovered context extensions. The forward and
backward term maps preserve pairing in hom equality, including terms outside
the image of substitution and arbitrary recovered sections. The actual
recovered context projection is compared with the original one by
`context_elements_context_proj`; this includes the display-to-context
projection boundary.

For any supplied witness H of that projection equality, the generic term
is first converted along `ty_sub_equiv T H A`. `context_elements_var`
compares it with the forward image of the original generic term, and
`context_elements_var_inv` gives the backward equation in the original term
setoid. The proofs use the general section bridge, display factorization,
pairing injectivity and the accepted inverse conversion law. They do not
identify H with a different witness, compare law records, or use the native
term/section isomorphism's common size bound. No terminal choice is needed
for these laws; a complete CwF still requires its independent terminal input.
This establishes these pointwise canonical compatibility laws without
introducing a new interface for structured CwF morphisms.

Ten permanent strict configurations fix the actual original type/term bounds
above both context hom levels in both orders. Temporary Code/El clients retain
distinct true/false Type-valued projection and induced type-equality witnesses,
check native forward/backward pairing and generic computations, and prove the
pairing equations for a term outside a non-surjective substitution's image.
Exact source copies and assumption output remain outside the library.

`context_elements_context_conv` and `context_elements_context_lift` also
compare the actual recovered context operations with the original conversion
and substitution lift. They compose `display_context_conv` /
`display_context_lift` from the independently accepted general display theorem
with `context_elements_conv` / `context_elements_lift`. No generic-term or
pullback universal property is reproved. Each supplied Type-valued type-equality
witness is retained as input, and the result is specified hom equality; the
chosen structure and law records are not identified. These transparent laws
need chosen context extensions, with no terminal choice or native common
term/Hom size bound. Twelve fixed regressions retain independent original
input sizes and recovered-term bounds in both hom orders, placing the original
types/terms both below and above the auxiliary bound of the base laws.

`context_elements_lift_cone` transports an original pullback cone across the
recovered projection equality. `context_elements_context_factor` compares the
recovered and original universal mediators for any independently supplied
witnesses of the two cone equations. The original cone always supplies a
recovered one through the transport helper; requiring a supplied witness does
not impose a new semantic condition. The proof reuses original factor
uniqueness after aligning the recovered projection and lift by the accepted
canonical comparisons. Computational mediators stay transparent, and no cone
or pullback-law witnesses are identified. Eight fixed configurations keep the
original type/term sizes independent of both Hom levels and the base-law
auxiliary bound in both strict orders. Neither terminal objects nor globally
chosen pullbacks are needed.

[Context/PairComparison](../../theories/DTT/Context/PairComparison.v) applies the
forward and backward term maps to substitution-term pairs. Both respectful
maps retain the base substitution by conversion. Their respectfulness follows
from the accepted conversion coherence, and their two inverse laws follow
fiberwise. Both maps commute with pair reindexing, including the composition
conversion on its term coordinate. Original and recovered conversion witnesses
are aligned by coherent transport, not identified by native equality. This
compares the dependent-sum data used by the extension representation; it does
not identify CwF records or impose a common native term-carrier bound. The
lifted natural isomorphism above remains the comparison of primary functors.
Twelve fixed configurations place the original type/term bounds above both
Hom levels and the base-law auxiliary bound, in both strict Hom orders.

[Context/PairNatural](../../theories/DTT/Context/PairNatural.v) assembles the
accepted pair maps into `ContextElementsPairN`, its natural isomorphism and
`ContextElementsPairInvN`. For fixed Γ and A, naturality is in the varying
source context Δ. Both pair presheaves are explicitly raised to
independent common carrier/equality bounds. Components retain the accepted
forward and backward maps, including their unchanged native base coordinate.
The lifted representations above give a common Hom-presheaf endpoint, with
natural-transformation equations
`Pair_R ∘Nv Compare ≈N Pair_T` and
`Compare ∘Nv Unpair_T ≈N Unpair_R`.
The first is the accepted canonical pairing law; the second inverts its two
representation isomorphisms by `iso_square_inv` in the functor category.
There is no additional naturality or universal-property hypothesis, no native
identification of law witnesses and no terminal-context requirement. Twenty
fixed configurations retain both native Hom orders and both strict target
carrier/equality orders; smaller targets are rejected. These are comparisons
of pair presheaves and their representations, not of CwF records or the full
source category. The primary functor comparison remains the earlier lifted
family-valued natural isomorphism.
