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
    return < comp_alg(y, 1, place) gt 0 select 1 else 0, -Infinity() >;
  end if;
  return < sign_alg(x, place) lt 0 select 1 else 0, (x^2 + y^2 - 1)/x >;
end function;

/* Compare the tuple corresponding to two complex points. */
comp_ord := function(a, b, place)
  if a[1] ne b[1] then return a[1] - b[1]; end if;
  if a[2] cmpeq b[2] then return 0; end if;
  if a[2] cmpeq Infinity() or b[2] cmpeq -Infinity() then return 1; end if;
  if a[2] cmpeq -Infinity() or b[2] cmpeq Infinity() then return -1; end if;
  return comp_alg(a[2], b[2], place);
end function;

/* Get the symmetric sequence of generators and inverses */
sym_gens := function(gens)
  gens_pm := gens cat [x^-1 : x in gens];
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

/* Decide whether a pair of commuting non-elliptic elements of SL2 generates a discrete group. */
abelian_is_discrete := function(g, h, place)
  error if g*h ne h*g, "Arguments must commute";
  error if is_elliptic(g, place) or is_elliptic(h, place), "Arguments must not be elliptic";
  G := MatrixGroup<2, BaseRing(g) | g, h>;
  if NumberOfGenerators(G) eq 1 then
    return true, g;
  end if;
  if IsCompletelyReducible(G) then
    Pc, _, f1 := RecogniseAbelian(G);
    Ab, f2 := AbelianGroup(Pc);
    H := TorsionFreeSubgroup(Ab);

    if NumberOfGenerators(H) eq 1 then
      return true, Matrix((f1*f2^-1)(H.1));
    else
      return false, _;
    end if;
  else
    b, A := IsUnipotent(G);
    assert b;
    G2 := G^A;
    r := (G2.1)[1,2]/(G2.2)[1,2];
    Q := RationalField();
    if r in Q then
      B := Parent(A)![1, (G2.1)[2,2]/Numerator(Q!r), 0, 1];
      return true, Matrix(B^(A^-1));
    else
      return false, _;
    end if;
  end if;
end function;

/* Get the set of initial segments of a sequence. */
initial_segments := function(seq)
  return [seq[1..i] : i in [1..#seq]];
end function;

/* Get a list of all short rightmost words */
short_words := function(gens_pm, invert_perm, place)
  bounding_perm := bounding_path_perm(gens_pm, invert_perm, place);
  return &cat [initial_segments(Setseq(Cycle(bounding_perm, i))) : i in [1..#gens_pm]];
end function;

/**
 * Apply one step of the reduction algorithm.
 * Returns one of the following:
 * - 0, `new_gens` where `new_gens` is a generating set Nielsen-equivalent to `gens`;
 * - 1, `gens` if `gens` is reduced;
 * - 2, `a` if `a` is elliptic;
 * - 3, `<a, b>` if `a` and `b` are not elliptic and generate an indiscrete group.
 */
reduce_step := function(gens, place)
  for i -> x in gens do
    if x^-1 in gens then // Remove inverses of generators.
      return 0, Remove(gens, i);
    elif is_elliptic(x, place) then // Test for elliptic elements.
      return 2, x;
    end if;
  end for;

  // A single non-elliptic element generates a free group.
  if #gens le 1 then return 1, gens; end if;

  // Compare the 2 generators of smallest length.
  sorted_ids := Sort([1..#gens], func<i, j | comp_alg(length_proxy(gens[i]), length_proxy(gens[j]), place)>);
  a := gens[sorted_ids[1]];
  b := gens[sorted_ids[2]];

  if a*b eq b*a then
    is_discrete, c := abelian_is_discrete(a, b, place);
    if not is_discrete then return 3, <a, b>; end if;

    result := [x : i -> x in gens | i ne sorted_ids[1] and i ne sorted_ids[2]];
    Append(~result, c);
    return 0, result;
  end if;

  gens_pm, invert_perm := sym_gens(gens);
  short_word_ids := [word : word in short_words(gens_pm, invert_perm, place) | #word gt 1];

  short_elts := [&*Reverse(gens_pm[i]) : i in short_word_ids];

  b_len := length_proxy(b);
  for elt in short_elts do
    if is_elliptic(elt, place) then return 2, elt; end if;
    if not IsOne(elt) and comp_alg(b_len + length_proxy(elt), 1, place) lt 0 then
      // If Phi(b)*Phi(elt)<1, Phi(a)*Phi(elt)<1.
      // Since a and b do not commute, either b and elt do not commute or
      // a and elt do not commute.
      return 3, a*elt eq elt*a select <a, elt> else <b, elt>;
    end if;
  end for;

  for i -> word in short_word_ids do
    for term_id in word do
      elt := short_elts[i];
      term := gens_pm[term_id];
      if term_id^invert_perm notin word and comp_alg(length_proxy(elt), length_proxy(term), place) lt 0 then
        result := gens;
        result[Min(term_id, term_id^invert_perm)] := short_elts[i];
        return 0, result;
      end if;
    end for;
  end for;

  return 1, gens;
end function;

function reduce(gens, place)
  repeat
    type, gens := reduce_step(gens, place);
  until type ne 0;
  return type, gens;
end function;
