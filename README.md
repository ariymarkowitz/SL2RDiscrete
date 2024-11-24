A Magma package to recognise finitely generated discrete subgroups of SL(2, R) and PSL(2, R).

## Types

`GrpSL2RGen`

A finite generating set for a subgroup of SL(2, R). R is represented by an algebraic number field together with a place (real embedding). This type has the following attributes:

- `field` - The base field.
- `matalg` - The matrix algebra.
- `place` - The place (real embedding) of the field.
- `seq`- Sequence of generators of the group.

The following attributes are initially unset, and are set by `RecognizeDiscreteTorsionFree(gen::GrpSL2RGen)`.
- `has_neg` - True if `psl` is false and the group contains -I.
- `neg_word` - -I as a word in the generators.
- `type` - The type of group. This attribute is one of the following:
  - "un" - Unknown type (only used for intermediate reduction steps).
  - "df" - Discrete and free.
  - "dc" - Discrete with co-compact action.
  - "ab" - Contains an indiscrete abelian subgroup.
  - "el" - Contains an elliptic element.
- `witness` - The witness proving that the group is a particular type. For "un", this is a Nielsen-equivalent generating set. For "df" and "dc", this is a reduced generating set (not including -I). For "sm" and "ab", this is a pair of elements generating an indiscrete group. For "el", this is an elliptic element.
- `witness_word` - A word corresponding to each element of the witness.

The following attributes are only defined if SL2Gen is determined to be discrete and torsion-free.
- `FPgrp` - A finitely-presented group isomorphic to this group.
- `matgrp` - A matrix group (with reduced generating set) isomorphic to this group.
- `iso` - Isometry from `matgrp` to `FPgrp`.

## Intrinsics

### Discrete and free groups

`SL2Gens(seq::SeqEnum[AlgMatElt[FldNum]], place::PlcNumElt : psl := false) -> GrpSL2RGen`

Create a generating set for a subgroup of SL(2, R). If `psl` is set, then the generators will be considered to be representatives of elements of PSL(2, R).

`RecognizeDiscreteTorsionFree(gen::GrpSL2RGen)`

Decide a generating set of SL(2, R) is discrete and torsion-free. This adds data to `gen` that records the results of the recognition algorithm.

`IsDiscreteTorsionFree(gen::GrpSL2RGen) -> BoolElt`

Return true if the generating set is discrete and torsion-free.

`IsDiscreteFree(gen::GrpSL2RGen) -> BoolElt`

Return true if the generating set is discrete and free.

`IsDiscreteCocompact(gen::GrpSL2RGen) -> BoolElt`

Return true if the generating set is discrete with cocompact action.

`IsElementOf(g::AlgMatElt, gen::GrpSL2RGen) -> BoolElt, GrpFPElt`

Decide whether g is an element of the group, returning the word in the reduced set evaluating to g.

`MapToFundamentalDomain(z::Tup, gen::GrpSL2RGen) -> AlgMatElt, GrpFPElt`

Return g (and corresponding word w) such that gz is in the fundamental domain.
Two points in the same orbit will be mapped to the same orbit representative.

`ReducedGenerators(gen::GrpSL2RGen) -> SeqEnum[AlgMatElt]`

Return a reduced generating set for a discrete torsion-free group.

`BaseField(gen::GrpSL2RGen) -> FldNum`

Return the base field of the group.

`HasNegativeOne(gen::GrpSL2RGen) -> FldNum, GrpFPElt`

Return true if the subgroup of SL(2, R) has -I.

`Rank(gen::GrpSL2RGen) -> RngIntElt`

The rank of a discrete torsion-free group.

## Discrete groups

`TorsionFreeSubgroup(gen::GrpSL2RGen) -> GrpSL2RGen, SetEnum[AlgMatElt], RngIntElt`

Find a generating set for a torsion-free congruence subgroup.

`IsDiscrete(gen::GrpSL2RGen) -> BoolElt, GrpSL2RGen, SetEnum[AlgMatElt], RngIntElt`

Decide whether a subgroup of SL(2, R) or PSL(2, R) is discrete, returning a finite index subgroup and set of coset representatives if so.

`IsElementOf(g::AlgMatElt, tf_gp::GrpSL2RGen, cosets::SetEnum[AlgMatElt]) -> BoolElt, GrpFPElt, AlgMatElt`

Decide whether g is an element of a subgroup of SL(2, R) or PSL(2, R), given a torsion-free discrete subgroup and a set of coset representatives. If it is, then return (w, s) where s is a coset representative and w is a word in the reduced set such that w*s evaluates to g.