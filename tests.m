Attach("sl2r.m");

Q := Rationals();
P<x> := PolynomialRing(Q);
K<w> := NumberField(x^2 - 3);
M := MatrixAlgebra(K, 2);
P := RealPlaces(K)[1];

function random_sl2(F, n, l)
  M := MatrixAlgebra(F, 2);
  R := Integers(F);
  result := One(M);
  for i in [1..l] do
    m := M![1, Random(F, n), 0, 1];
    if Random(1) eq 1 then
      m := Transpose(m);
    end if;
    if Random(1) eq 1 then
      m := -m;
    end if;
    result *:= m;
  end for;
  return result;
end function;

function random_gens(F, n, l, gens)
  return [random_sl2(F, n, l) : i in [1..gens]];
end function;

function time_ngens(genslist)
  worst := 0;
  full := Cputime();
  for i -> gens in genslist do
    t := Cputime();
    RecognizeDiscreteTorsionFree(gens);
    t := Cputime(t);
    worst := Maximum(t, worst);
  end for;
  full := Cputime(full);
  print "Test complete";
  return <full/#genslist, worst>;
end function;

params := [<7, 2>, <15, 5>, <20, 10>, <27, 20>];
tests := [[SL2Gens(random_gens(K, 10, p[1], p[2]), P) : i in [1..1000]] : p in params];

results := [time_ngens(test) : test in tests];
