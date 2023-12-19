/* Apply a mobius transformation to i, returning a vector */
to_point := function(g)
  a := g[1, 1]; b := g[2, 1]; c := g[1, 2]; d := g[2, 2];
  den := c^2 + d^2;
  return <(b*d + a*c)/den, (a*d - b*c)/den>;
end function;

/* Get tanh^2(d(i, gi)), where d is hyperbolic distance in the upper half-plane. */
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
    return < comp_alg(y, 1, place) gt 0 select 1 else 0, Infinity() >;
  end if;
  return < sign_alg(x, place) lt 0 select 1 else 0, (x^2 + y^2 - 1)/x >;
end function;

/* Compare the tuple corresponding to two complex points. */
comp_ord := function(a, b, place)
  if a[1] ne b[1] then return a[1] - b[1]; end if;
  if a[2] cmpeq b[2] then return 0; end if;
  if a[2] cmpeq Infinity() then return -1; end if;
  return comp_alg(a[2], b[2], place);
end function;

/* Get the symmetric sequence of generators and inverses */
sym_gens := function(gens)
  gens_pm := gens cat [x^-1 : x in gens];
  if Nresults() eq 1 then return gens_pm; end if;
  S := Sym(#gens_pm);
  invert_perm := S!([#gens + 1 .. 2*#gens] cat [1 .. #gens]);
  return gens_pm, invert_perm;
end function;

/* Return the permutation sending each edge type to the next edge type in its rightmost path. */
bounding_path_perm := function(gens_pm, invert_perm, place)
  S := Parent(invert_perm);
  bounding_paths := Id(S);
  ordinals := [ord_point(to_point(g), place) : g in gens_pm];
  Sort(~ordinals, func<a, b | comp_ord(a, b, place)>, ~bounding_paths);
  rotate := S!([2..#gens_pm] cat [1]);
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
    return true, g, 1, 1;
  end if;
  if IsCompletelyReducible(G) then
    // G is semisimple over an extension of K. We find a representation as an abelian group.
    Pc, f1, f1i := RecogniseAbelian(G);
    Ab, f2 := AbelianGroup(Pc);

    N := pPrimaryComponent(Ab, 2);
    H, f3 := Ab/N;
    if NumberOfGenerators(H) ne 1 then return false, _, _; end if;

    proj := f1*f2*f3
    return true, Eltseq(proj(A))[1], Eltseq(proj(B))[1];
  else
    // G is unipotent, so isomorphic to the additive group via the top-right entry of the upper
    // triangularisation.
    b, A := IsUnipotent(G);
    assert b;
    G2 := G^A;
    r := (G2.1)[1,2]/(G2.2)[1,2];
    Q := RationalField();
    if r in Q then
      return true, Numerator(s), Denominator(s);
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
 return &*Reverse([seq[i] : i in word_ids]);
end function;

declare type GrpSL2Gen;
declare attributes GrpSL2Gen:
  field, // Base field
  matalg, // Matrix Algebra
  place, // Real embedding
  seq, // Generators
  psl, // Whether the generators should be considered a subgroup of PSL
  /**
   * "un" - Unknown type (only used for intermediate reduction steps)
   * "df" - Discrete and free
   * "dc" - Discrete with co-compact action
   * "sm" - Contains a subgroup with small action
   * "ab" - Contains an indiscrete abelian subgroup
   * "el" - Contains an elliptic element
   * "ne" - Contains -1
   */
  type,
  /**
   * Proof of the type of the group:
   * "un" - Nielsen-equivalent generating set
   * "df" and "dc" - Reduced generating set
   * "sm" and "ab" - Pair of elements generating an indiscrete group
   * "el" - Elliptic element
   * "ne" - -1
   */
  witness,
  witness_word, // A word corresponding to each element of the witness

  // These attributes are only defined if SL2Gen is determined to be discrete and torsion-free.
  asFPGroup, // Finite presetation
  isometry; // Isometry to finitely presented group

intrinsic SL2Gens(gens::SeqEnum[AlgMatElt[FldNum]], place::PlcNumElt, psl := false) -> GrpSL2Gen
{ Create a generating set for a subgroup of SL(2, R) }
  gen := New(GrpSL2Gen);
  require IsReal(place): "Place must be real";
  require Degree(Universe(genseq)) eq 2: "Matrix algebra must be degree 2";
  require &and[Determinant(gen) eq 1 : gen in genseq]: "Matrices must have determinant 1";
  require BaseRing(Universe(genseq)) eq NumberField(place): "Generators and place must have the same base field";
  gen`matalg := Universe(genseq);
  gen`field := BaseRing(gens`matalg);
  gen`place := place;
  gen`psl := psl;

  gen`type := "un";
  gen`witness := gens;
  gen`witness_word := Generators(FreeGroup(#genseq));
  return gen;
end intrinsic;

// Apply one step of the reduction algorithm.
reduce_step := procedure(~gen)
  if gen`type ne "un" then return; end if;

  // Remove duplicate or elliptic generators
  for i -> g in gen`witness do
    if IsOne(g) or (gen`psl and IsOne(-g)) then
      Remove(~gen`witness, i);
      Remove(~gen`witness_word, i);
      return;
    elif is_elliptic(x, place) then
      gen`type := "el";
      gen`witness := g;
      gen`witness_word := gen`witness_word[i];
      return;
    end if;
  end for;

  // A single non-elliptic element generates a free group.
  if #gens le 1 then
    gen`type := "df";
    gen`asFPGroup := FreeGroup(#gen`witness_word);
  end if;

  // Compare the 2 generators of smallest length.
  sorted_ids := Sort([1..#gen`witness], func<i, j | comp_alg(length_proxy(gen`witness[i]), length_proxy(gen`witness[j]), gen`place)>);
  i := sorted_ids[1];
  j := sorted_ids[2];
  a := gen`witness[i];
  b := gen`witness[j];
  wa := gen`witness_word[i];
  wb := gen`witness_word[j];

  // Reduce generators if an abelian pair is found
  if a*b eq b*a then
    is_discrete, m, n := abelian_is_cyclic(a, b);
    if not is_discrete then
      gen`type := "ab";
      gen`witness := [a, b];
      gen`witness_word := [wa, wb];
    end if;

    // Check whether a and b generate -1
    if not gen`psl and IsOne(-a^n * b^-m) then
      gen`type := "ne";
      gen`witness := -One(gen`matalg);
      gen`witness_word := wa^n * wb^-m;
    end if;

    c, x, y := ExtendedGreatestCommonDivisor(m, n);
    assert c eq 1;
    gen`witness := [x : k -> x in gen`witness | k notin [i, j]] cat [a^x * b^y];
    gen`witness_word := [x : k -> x in gen`witness_word | k notin [i, j]] cat [gen`witness_word[i]^x * gen`witness_word[j]^y];
    return;
  end if;

  gens_pm, invert_perm := sym_gens(gen`witness);
  words_pm := sym_gens(gen`witness_word);
  short_word_ids := [word : word in short_words(gens_pm, invert_perm, gen`place) | #word gt 1];

  b_len := length_proxy(b);
  max_reduction := 0; // The replacement that reduces the length the most
  replacement := false;
  for i -> word in short_word_ids do
    elt := evaluate_word(i, gens_pm);
    if is_elliptic(elt, place) then return 2, elt; end if;
    if not IsOne(elt) and comp_alg(b_len + length_proxy(elt), 1, gen`place) lt 0 then
      // If Phi(b)*Phi(elt)<1, Phi(a)*Phi(elt)<1.
      // Since a and b do not commute, either b and elt do not commute or
      // a and elt do not commute.
      bad_id := a*elt eq elt*a select j else i;
      gen`type := "sm";
      gen`witness := [gen`witness[bad_id], elt];
      gen`witness_word := [gen`witness_word[bad_id], evaluate_word(short_word_ids[word_id], words_pm)];
      return;
    end if;
    // Find a replacement candidate.
    for term_id in word do
      if term_id^invert_perm notin word then continue; end if;
      reduction := length_proxy(elt) - length_proxy(term);
      if comp_alg(reduction, max_reduction, gen`place) gt 0 then
        max_reduction := reduction;
        replacement := <i, Min(replacement[1], replacement[1]^invert_perm)>;
      end if;
    end for;
  end for;

  if max_reduction eq 0 then
    // The group is discrete and torsion-free.
    F := FreeGroup(#gens`witness);
    perm := bounding_path_perm(gens_pm, invert_perm, gen`place);
    decomp := CycleDecomposition(perm);
    if #decomp eq 1:
      relation := decomp[1];
      x := evaluate_word(relation, sym_gens(F));
      if (IsOne(x) or (g`psl and IsOne(-x))) then
        // The group has cocompact action.
        gen`type := "dc";
        gen`asFPGroup := quo<F | evaluate_word(relation, sym_gens(F))>;
      end if;
    end if;
    // The group is free.
    gen`type := "df";
    gen`asFPGroup := F;
    return;
  end if;

  word_id := replacement[0];
  term_id := replacement[1];
  gens`witness[term_id] := short_elts[word_id];
  gens`witness_word[term_id] := evaluate_word(short_word_ids[word_id], words_pm);
end function;

intrinsic RecogniseDiscreteTorsionFree(~gens: GrpSL2Gen)
{ Decide a generating set of SL(2, R) is discrete and torsion-free }
  repeat
    reduce_step(gens);
  until gens`type ne "un";
end intrinsic;
