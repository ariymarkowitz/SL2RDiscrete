apply_mobius := function(z, g)
  x := z[1]; y := z[2];
  a := g[1, 1]; b := g[2, 1]; c := g[1, 2]; d := g[2, 2];
  den := (c*x + d)^2 + (c*y)^2;
  return <((a*x + b)*(c*x + d) + a*c*y^2)/den, ((c*x+d)*a*y - (a*x+b)*c*y)/den>;
end function;

dist_proxy := function(z)
  a := z[1]; b := z[2];
  return (a^2 + (b-1)^2)/(a^2 + (b+1)^2);
end function;

/* Apply a mobius transformation to i, returning a vector */
to_point := function(g)
  a := g[1, 1]; b := g[2, 1]; c := g[1, 2]; d := g[2, 2];
  den := c^2 + d^2;
  return <(b*d + a*c)/den, (a*d - b*c)/den>;
end function;

/* Get tanh^2(d(i, gi)/2), where d is hyperbolic distance in the upper half-plane. */
length_proxy := function(g)
  a := g[1, 1]; b := g[2, 1]; c := g[1, 2]; d := g[2, 2];
  return ((a-d)^2 + (b+c)^2)/((a+d)^2 + (b-c)^2);
end function;

/* Get the sign of a real algebraic number. */
sign_alg := function(x, place)
  if IsZero(x) then return 0; end if;
  val := Evaluate(x, place);
  // Magma seems to make sure there is enough precision, but let's verify.
  error if IsZero(val), "Evaluations have too low precision";
  return Sign(val);
end function;

/* Compare two real algebraic numbers. */
comp_alg := function(x, y, place)
  return sign_alg(x - y, place);
end function;

/* Assign an tuple to each complex point for comparing angles. */
ord_point := function(z, place)
  x := z[1]; y := z[2];
  if IsZero(x) then
    return < comp_alg(y, 1, place) gt 0 select 2 else 0, 0 >;
  end if;
  return < sign_alg(x, place) lt 0 select 3 else 1, (x^2 + y^2 - 1)/x >;
end function;

/* Compare a pair of real algebraic numbers. */
comp_alg_pair := function(a, b, place)
  if a[1] ne b[1] then return comp_alg(a[1], b[1], place); end if;
  return comp_alg(a[2], b[2], place);
end function;

/* Get the symmetric sequence of generators and inverses */
symmetrize := function(gens)
  gens_sym := &cat[[x, x^-1] : x in gens];
  if Nresults() eq 1 then return gens_sym; end if;
  S := Sym(#gens_sym);
  invert_perm := S!(&cat[[2*i, 2*i-1] : i in [1 .. #gens]]);
  return gens_sym, invert_perm;
end function;

/* Return the permutation sending each edge type to the next edge type in its rightmost path. */
bounding_path_perm := function(gens_sym, invert_perm, place)
  S := Parent(invert_perm);
  bounding_paths := Id(S);
  ordinals := [ord_point(to_point(g), place) : g in gens_sym];
  Sort(~ordinals, func<a, b | comp_alg_pair(a, b, place)>, ~bounding_paths);
  rotate := S!([2..#gens_sym] cat [1]);
  return rotate^bounding_paths * invert_perm;
end function;

is_hyperbolic := function(g, place)
  return comp_alg(Trace(g)^2, 4, place) gt 0;
end function;

is_elliptic := function(g, place)
  return comp_alg(Trace(g)^2, 4, place) lt 0;
end function;

/**
 * Decide whether a pair of elements of SL(2, R) are nontrivial and project to a cyclic subgroup of PSL(2, R).
 * If so, returns the integers m and n such that c^m = ±a, c^n = ±b for some generator c.
 */
abelian_is_cyclic := function(g, h)
  error if &or[IsOne(x) : x in [g, h, -g, -h]], "Arguments must be nontrivial in PSL(2, R)";
  error if g*h ne h*g, "Arguments must commute";
  G := MatrixGroup<2, BaseRing(g) | g, h>;
  if NumberOfGenerators(G) le 1 then
    return true, 1, 1;
  end if;
  if IsCompletelyReducible(G) then
    // G is semisimple over an extension of K. We find a representation as an abelian group.
    Pc, f1, f1i := RecogniseAbelian(G);
    Ab, f2 := AbelianGroup(Pc);

    N := pPrimaryComponent(Ab, 2);
    H, f3 := Ab/N;
    if NumberOfGenerators(H) ne 1 then return false, _, _; end if;

    proj := f1*f2*f3;
    return true, Eltseq(proj(g))[1], Eltseq(proj(h))[1];
  else
    // G is unipotent (up to sign), so isomorphic to the additive group via the top-right entry of the upper
    // triangularisation.

    m, T := JordanForm(g);
    assert m[1,2] eq 1;
    r := (T*h*T^-1)[1,2];

    Q := RationalField();
    if r in Q then
      r := Q!r; // Just in case
      return true, Denominator(r), Numerator(r);
    else
      return false, _, _;
    end if;
  end if;
end function;

/* Get the set of initial segments of a sequence. */
initial_segments := function(seq)
  return [seq[1..i] : i in [1..#seq]];
end function;

/* Get a list of all short rightmost words. */
short_words := function(gens_pm, invert_perm, place)
  bounding_perm := bounding_path_perm(gens_pm, invert_perm, place);
  return &cat [initial_segments(Setseq(Cycle(bounding_perm, i))) : i in [1..#gens_pm]];
end function;

/* Evaluate a word (as a list of ids) with a generating set. */
evaluate_word := function(word_ids, seq)
 return &*[seq[i] : i in word_ids];
end function;

declare type GrpSL2Gen;
declare attributes GrpSL2Gen:
  field, // Base field
  matalg, // Matrix Algebra
  place, // Real embedding
  seq, // Generators
  psl, // Whether the generators should be considered a subgroup of PSL
  has_neg, // True if psl is false and the group has -I
  neg_word, // -I as a word in the generators
  /**
   * "un" - Unknown type (only used for intermediate reduction steps)
   * "df" - Discrete and free
   * "dc" - Discrete with co-compact action
   * "ab" - Contains an indiscrete abelian subgroup
   * "el" - Contains an elliptic element
   */
  type,
  /**
   * Proof of the type of the group:
   * "un" - Nielsen-equivalent generating set
   * "df" and "dc" - Reduced generating set (does not include -I)
   * "sm" and "ab" - Pair of elements generating an indiscrete group
   * "el" - Elliptic element
   */
  witness,
  witness_word, // A word corresponding to each element of the witness

  // These attributes are only defined if SL2Gen is determined to be discrete and torsion-free.
  FPgrp, // Finite presetation
  matgrp, // Matrix group (with reduced generating set)
  iso; // Isometry to finitely presented group

intrinsic Print(gen::GrpSL2Gen)
{ Print the generating set. }
list := &*[Sprint(x) * (i lt #gen`seq select "\n\n" else "") : i -> x in gen`seq];
printf "Generators of subgroup of %oSL(2,R):\n%o", gen`psl select "P" else "", list;
end intrinsic;

intrinsic SL2Gens(seq::SeqEnum[AlgMatElt[FldNum]], place::PlcNumElt : psl := false) -> GrpSL2Gen
{ Create a generating set for a subgroup of SL(2, R). }
  gen := New(GrpSL2Gen);
  require IsReal(place): "Place must be real";
  require Degree(Universe(seq)) eq 2: "Matrix algebra must be degree 2";
  require &and[Determinant(g) eq 1 : g in seq]: "Matrices must have determinant 1";
  require BaseRing(Universe(seq)) eq NumberField(place): "Generators and place must have the same base field";
  gen`seq := seq;
  gen`matalg := Universe(seq);
  gen`field := BaseRing(gen`matalg);
  gen`place := place;
  gen`psl := psl;
  gen`has_neg := false;

  gen`type := "un";
  gen`witness := seq;
  gen`witness_word := Setseq(Generators(FreeGroup(#seq)));
  return gen;
end intrinsic;

// Apply one step of the reduction algorithm.
reduce_step := procedure(gen)
  if gen`type ne "un" then return; end if;

  // Remove duplicate, elliptic, I or -I generators.
  for i -> g in gen`witness do
    if IsOne(g) or IsOne(-g) then
      if IsOne(-g) and not gen`psl and not gen`has_neg then
        gen`has_neg := true;
        gen`neg_word := gen`witness_word[i];
      end if;
      Remove(~gen`witness, i);
      Remove(~gen`witness_word, i);
      return;
    elif is_elliptic(g, gen`place) then
      gen`type := "el";
      gen`witness := g;
      gen`witness_word := gen`witness_word[i];
      return;
    end if;
  end for;

  // A single non-elliptic element generates a free group.
  if #gen`witness le 1 then
    gen`type := "df";
    gen`FPgrp := FreeGroup(#gen`witness_word);
    if gen`has_neg then
      gen`FPgrp := DirectProduct(gen`FPgrp, CyclicGroup(GrpFP, 2));
    end if;
    return;
  end if;

  // Compare the 2 generators of smallest length.
  sorted_ids := Sort([1..#gen`witness], func<i, j | comp_alg(length_proxy(gen`witness[i]), length_proxy(gen`witness[j]), gen`place)>);
  a_id := sorted_ids[1];
  b_id := sorted_ids[2];
  a := gen`witness[a_id];
  b := gen`witness[b_id];
  wa := gen`witness_word[a_id];
  wb := gen`witness_word[b_id];

  // Reduce generators if an abelian pair is found.
  if a*b eq b*a then
    is_discrete, m, n := abelian_is_cyclic(a, b);
    if not is_discrete then
      gen`type := "ab";
      gen`witness := [a, b];
      gen`witness_word := [wa, wb];
      return;
    end if;

    // Check whether a and b generate -1.
    if not gen`psl and not gen`has_neg and IsOne(-a^n * b^-m) then
      gen`has_neg := true;
      gen`neg_word := wa^n * wb^-m;
    end if;

    c, x, y := ExtendedGreatestCommonDivisor(m, n);
    assert c eq 1;
    gen`witness := [x : k -> x in gen`witness | k notin [a_id, b_id]] cat [a^x * b^y];
    gen`witness_word := [x : k -> x in gen`witness_word | k notin [a_id, b_id]] cat [gen`witness_word[a_id]^x * gen`witness_word[b_id]^y];
    return;
  end if;

  gens_sym, invert_perm := symmetrize(gen`witness);
  words_sym := symmetrize(gen`witness_word);
  short_word_ids := [word : word in short_words(gens_sym, invert_perm, gen`place) | #word gt 1];

  b_len := length_proxy(b);
  max_reduction := 0; // The replacement that reduces the length the most
  replacement := false;
  for i -> word in short_word_ids do
    elt := evaluate_word(word, gens_sym);
    if is_elliptic(elt, gen`place) then
      gen`type := "el";
      gen`witness := elt;
      gen`witness_word := evaluate_word(word, words_sym);
      return;
    end if;
    if not IsOne(elt) and not IsOne(-elt) and comp_alg(b_len + length_proxy(elt), 1, gen`place) lt 0 then
      // If Phi(b)*Phi(elt)<1, Phi(a)*Phi(elt)<1.
      // Since a and b do not commute, either b and elt do not commute or
      // a and elt do not commute.
      bad_id := a*elt in {elt*a, -elt*a} select b_id else a_id;

      gen`type := "sm";
      gen`witness := [gen`witness[bad_id], elt];
      gen`witness_word := [gen`witness_word[bad_id], evaluate_word(short_word_ids[bad_id], words_sym)];
      return;
    end if;
    // Find a replacement candidate.
    for term_id in word do
      if term_id^invert_perm in word then continue; end if;
      reduction := length_proxy(gens_sym[term_id]) - length_proxy(elt);
      if comp_alg(reduction, max_reduction, gen`place) gt 0 then
        max_reduction := reduction;
        replacement := <word, Ceiling(term_id/2)>;
      end if;
    end for;
  end for;

  if max_reduction eq 0 then
    // The group is discrete and torsion-free.
    F := FreeGroup(#gen`witness);
    perm := bounding_path_perm(gens_sym, invert_perm, gen`place);
    decomp := CycleDecomposition(perm);
    if #decomp eq 1 then
      relation := decomp[1];
      x := evaluate_word(relation, gens_sym);
      if (not gen`psl and not gen`has_neg and IsOne(-x)) then
        gen`has_neg := true;
        gen`neg_word := evaluate_word(relation, words_sym);
      end if;
      if IsOne(x) then
        // The group has cocompact action.
        // We don't need to check for -I: There is a lift of the group from PSL to SL,
        // but every relation containing the identity contains each generator an even number of times,
        // so no relation in the group in PSL can evaluate to -I in a cover in SL.
        // See [J. Button, "Lifting Möbius Groups", New York J. Math].
        gen`type := "dc";
        gen`FPgrp := quo<F | evaluate_word(relation, symmetrize(Setseq(Generators(F))))>;
        return;
      end if;
    end if;
    // The group is free.
    gen`type := "df";
    gen`FPgrp := F;
    if gen`has_neg then
      gen`FPgrp := DirectProduct(gen`FPgrp, CyclicGroup(GrpFP, 2));
    end if;
    return;
  end if;

  word := replacement[1];
  term_id := replacement[2];
  gen`witness[term_id] := evaluate_word(word, gens_sym);
  gen`witness_word[term_id] := evaluate_word(word, words_sym);
end procedure;

intrinsic RecognizeDiscreteTorsionFree(gen::GrpSL2Gen)
{ Decide a generating set of SL(2, R) is discrete and torsion-free. }
  repeat
    reduce_step(gen);
  until gen`type ne "un";

  // Construct isomorphism between presentation and matrix group.
  if IsDiscreteTorsionFree(gen) then
    gen`matgrp := MatrixGroup<2, gen`field | ReducedGenerators(gen)>;

    to_mat := hom<gen`FPgrp -> gen`matgrp | [gen`matgrp!g : g in ReducedGenerators(gen)]>;
    to_fp_fn := function(g)
      b, w := IsElementOf(Matrix(g), gen);
      assert b;
      return w;
    end function;

    gen`iso := iso<gen`matgrp -> gen`FPgrp | g :-> to_fp_fn(g), w :-> to_mat(w)>;
  end if;
end intrinsic;

intrinsic IsDiscreteTorsionFree(gen::GrpSL2Gen) -> BoolElt
{ Return true if the generating set is discrete and torsion-free. }
  error if gen`type eq "un", "The group type is unknown; prepare it using `RecognizeDiscreteTorsionFree`";
  return gen`type eq "dc" or gen`type eq "df";
end intrinsic;

intrinsic IsDiscreteFree(gen::GrpSL2Gen) -> BoolElt
{ Return true if the generating set is discrete and free. }
  error if gen`type eq "un", "The group type is unknown; prepare it using `RecognizeDiscreteTorsionFree`";
  return gen`type eq "df";
end intrinsic;

intrinsic IsDiscreteCocompact(gen::GrpSL2Gen) -> BoolElt
{ Return true if the generating set is discrete with cocompact action. }
  error if gen`type eq "un", "The group type is unknown; prepare it using `RecognizeDiscreteTorsionFree`";
  return gen`type eq "dc";
end intrinsic;

intrinsic IsElementOf(g::AlgMatElt, gen::GrpSL2Gen) -> BoolElt, GrpFPElt
{ Decide whether g is an element of the group, returning the word in the reduced set evaluating to g. }
  error if gen`type eq "un", "The group must be prepared using `RecognizeDiscreteTorsionFree`";
  error if not IsDiscreteTorsionFree(gen), "The group is not discrete and torsion-free";

  gen_sym, inv := symmetrize(gen`witness);
  G := gen`FPgrp;
  fp_sym := symmetrize(Setseq(Generators(G)));
  g_word := Id(G);
  repeat
    finish := true;
    for word in short_words(gen_sym, inv, gen`place) do
      elt := evaluate_word(word, gen_sym);
      h := g*elt;
      if comp_alg(length_proxy(h), length_proxy(g), gen`place) lt 0 then
        g := h;
        g_word *:= evaluate_word(word, fp_sym);
        finish := false;
        break;
      end if;
    end for;
  until finish eq true;
  if IsOne(g) or (gen`psl and IsOne(-g)) then
    return true, g_word^-1;
  elif gen`has_neg and IsOne(-g) then
    return true, g_word^-1*G.(NumberOfGenerators(G));
  else
    return false, _;
  end if;
end intrinsic;

intrinsic MapToFundamentalDomain(z::Tup, gen::GrpSL2Gen) -> AlgMatElt, GrpFPElt
{ Return g (and corresponding word w) such that gz is in the fundamental domain.
Two points in the same orbit will be mapped to the same orbit representative. }
  error if gen`type eq "un", "The group must be prepared using `RecognizeDiscreteTorsionFree`";
  error if not IsDiscreteTorsionFree(gen), "The group is not discrete and torsion-free";

  gen_sym, inv := symmetrize(gen`witness);
  G := gen`FPgrp;
  fp_sym := symmetrize(Setseq(Generators(G)));
  g := One(gen`matalg);
  g_word := Id(G);
  w := z;
  repeat
    finish := true;
    for word in short_words(gen_sym, inv, gen`place) do
      elt := evaluate_word(word, gen_sym);
      w2 := apply_mobius(w, elt);
      cmp := comp_alg(dist_proxy(w2), dist_proxy(w), gen`place);
      if cmp lt 0 or (cmp eq 0 and comp_alg_pair(w2, w, gen`place) lt 0) then
        g *:= elt;
        g_word *:= evaluate_word(word, fp_sym);
        w := w2;
        finish := false;
        break;
      end if;
    end for;
  until finish;
  return g, g_word;
end intrinsic;

intrinsic Generators(gen::GrpSL2Gen) -> SeqEnum[AlgMatElt]
{ Return the original generating set. }
  return gen`seq;
end intrinsic;

intrinsic ReducedGenerators(gen::GrpSL2Gen) -> SeqEnum[AlgMatElt]
{ Return a reduced generating set for a discrete torsion-free group. }
  error if gen`type eq "un", "The group must be prepared using `RecognizeDiscreteTorsionFree`";
  error if not IsDiscreteTorsionFree(gen), "The group is not discrete and torsion-free";
  if (gen`has_neg) then
    return gen`witness cat [-One(BaseField(gen))];
  else
    return gen`witness;
  end if;
end intrinsic;

intrinsic BaseField(gen::GrpSL2Gen) -> FldNum
{ Return the base field of the group. }
  return gen`field;
end intrinsic;

intrinsic HasNegativeOne(gen::GrpSL2Gen) -> FldNum, GrpFPElt
{ Return true if the subgroup of group SL(2, R) and has -I }
  error if gen`type eq "un", "The group must be prepared using `RecognizeDiscreteTorsionFree`";
  error if gen`psl, "The group must be a subgroup of SL(2, R)";
  if gen`has_neg then
    return true, gen`neg_word;
  else
    return false;
  end if;
end intrinsic;

intrinsic Rank(gen::GrpSL2Gen) -> RngIntElt
{ The rank of a discrete torsion-free group. }
  error if gen`type eq "un", "The group must be prepared using `RecognizeDiscreteTorsionFree`";
  error if not IsDiscreteTorsionFree(gen), "The group is not discrete and torsion-free";
  return gen`has_neg select #gen`witness + 1 else #gen`witness;
end intrinsic

/* DISCRETENESS TEST */

intrinsic TorsionFreeSubgroup(gen::GrpSL2Gen) -> GrpSL2Gen, SetEnum[AlgMatElt], RngIntElt
{ Find a generating set for a torsion-free congruence subgroup. }
  F := gen`field;
  K<w> := SimpleExtension(sub<gen`field | [x : x in Eltseq(m), m in Generators(gen)]>);

  // Make sure w is an algebraic integer.
  s := LCM([Denominator(x) : x in Eltseq(MinimalPolynomial(w))]);
  K<w> := sub<K | s*w>;

  denominators := [Denominator(K!x) : x in Eltseq(m), m in Generators(gen)];
  denominators := [x : x in denominators | x ne 1];

  O := Integers(K);
  b1, n1 := NormEquation(Integers(K), 1);
  b2, n2 := NormEquation(Integers(K), 2);
  n := (b1 select n1 else []) cat (b2 select n2 else []);
  U, Umap := TorsionUnitGroup(K);
  ints := [x*Umap(u) : x in n, u in U | x ne 1];

  p := 2;
  while true do
    p := NextPrime(p);
    if (Integers()!Norm(w) mod p) ne 0 and &and[d mod p ne 0 : d in denominators] and &and[Abs(Norm(x - 2)) le 2 : x in ints] then
      break;
    end if;
  end while;

  Fp := FiniteField(p);
  P := PolynomialRing(Fp);
  f := Factorization(P!DefiningPolynomial(K))[1][1];
  Fq<a> := ext<Fp | f>;

  G := sub<GL(2, gen`field) | Generators(gen)>;

  rquot := hom<F -> Fq | x :-> Evaluate(P!Eltseq(K!x), a)>;
  H, mquot := ChangeRing(G, Fq, rquot);

  word := InverseWordMap(H);
  srepr := hom<Image(word) -> G | [G!x : x in Generators(gen)]>;
  hrepr := word * srepr;
  grepr := map<G -> G | x :-> hrepr(mquot(x))>;

  S := {hrepr(h) : h in H};
  new_seq := {Matrix(s*x*grepr((s*x)^-1)) : s in S, x in Generators(G)};
  
  return SL2Gens(Setseq(new_seq), gen`place), {Matrix(s) : s in S}, p;
end intrinsic;

intrinsic IsDiscrete(gen::GrpSL2Gen) -> BoolElt, GrpSL2Gen, SetEnum[AlgMatElt], RngIntElt
{ Decide whether a subgroup of SL(2, R) or PSL(2, R) is discrete, returning a finite index subgroup and set of coset representatives if so }
  H, S, p := TorsionFreeSubgroup(gen);
  RecognizeDiscreteTorsionFree(H);
  if IsDiscreteTorsionFree(H) then
    return true, H, S, p;
  else
    return false, H, S, p;
  end if;
end intrinsic;

intrinsic IsElementOf(g::AlgMatElt, tf_gp::GrpSL2Gen, cosets::SetEnum[AlgMatElt]) -> BoolElt, AlgMatElt, GrpFPElt
{ Decide whether g is an element of a subgroup of SL(2, R) or PSL(2, R),
  given a torsion-free discrete subgroup and a set of coset representatives.
  If it is, then return (s, w) where s is a coset representative and w is a word in the reduced set
  such that s*w evaluates to g. }
  for s in cosets do
    b, word := IsElementOf(s*g, tf_gp);
    if b then
      return true, AlgMatElt, GrpFPElt;
    end if;
  end for;
  return false, _, _;
end intrinsic;
