Q := Rationals();
P<x> := PolynomialRing(Q);
K<w> := NumberField(x^3 - x^2 - 2*x + 1);

M := MatrixAlgebra(K, 2);
P := RealPlaces(K)[1];

assert is_hyperbolic(M![w, 0, 0, 1/w], P);
assert is_elliptic(M![0, w, -(1/w), 0], P);

A := M![1, w, 0, 1];
B := M![1, 3/5*w, 0, 1];
b, m, n := abelian_is_cyclic(A, B);
assert b;
_, x, y := ExtendedGreatestCommonDivisor(m, n);
assert Eltseq(A^x * B^y) eq [1, 1/5*w, 0, 1];

A := M![w^4, 0, 0, w^-4];
B := M![w^6, 0, 0, w^-6];
b, m, n := abelian_is_cyclic(A, B);
assert b;
_, x, y := ExtendedGreatestCommonDivisor(m, n);
assert Eltseq(A^x * B^y) eq [w^2, 0, 0, w^-2];

A := M![1, w, 0, 1];
B := M![1, 1, 0, 1];
assert not abelian_is_cyclic(A, B);

// Reduction steps 1

A := M![1, 2, 0, 1];
B := M![1, 0, 2, 1];
Xpm, inv := symmetrize([A, B]);
assert Xpm eq [A, A^-1, B, B^-1];
assert Eltseq(inv) eq [2, 1, 4, 3];
assert Eltseq(bounding_path_perm(Xpm, inv, P)) eq [4, 2, 3, 1];
assert short_words(Xpm, inv, P) eq [[1], [1, 4], [2], [3], [4], [4, 1]];

gen := SL2Gens([A, B], P);
reduce_step(gen);
assert gen`type eq "df" and gen`witness eq [A, B];

gen := SL2Gens([A, B*A^-1], P);
reduce_step(gen);
assert gen`type eq "un" and gen`witness eq [A, B];

gen := SL2Gens([B*A*B^-1, B], P);
reduce_step(gen);
assert gen`type eq "un" and gen`witness eq [A^-1, B];
F := Universe(gen`witness_word);
assert gen`witness_word eq [F.2^-1 * F.1^-1 * F.2, F.2];

// Reduction 1

gen := SL2Gens([A*B^2, B^-2*A^-1*B], P);
RecognizeDiscreteTorsionFree(gen);
assert gen`type eq "df" and ReducedGenerators(gen) in {[A, B], [A^-1, B], [A, B^-1], [A^-1, B^-1]};

S := gen`witness;
F := gen`FPgrp;

b, word := IsElementOf(S[1]^2*S[2]^-1*S[1]*S[2]^2, gen);
assert b and word eq F.1^2 * F.2^-1 * F.1 * F.2^2;

assert not IsElementOf(M![2, 0, 0, 1/2], gen);
assert not IsElementOf(-One(M), gen);

assert gen`iso(((gen`iso)^-1)(F.1*F.2)) eq F.1*F.2;

// Reduction steps 2

A := M![1, 1, 1, 2];
B := M![2, 1, 1, 1];
Xpm, inv := symmetrize([A, B]);
assert Xpm eq [A, A^-1, B, B^-1];
assert Eltseq(inv) eq [2, 1, 4, 3];
assert Eltseq(bounding_path_perm(Xpm, inv, P)) eq [4, 3, 1, 2];
assert short_words(Xpm, inv, P) eq [[1], [1, 4], [1, 4, 2], [1, 4, 2, 3], [2], [2, 3], [2, 3, 1], [2, 3, 1, 4], [3], [3, 1], [3, 1, 4], [3, 1, 4, 2], [4], [4, 2], [4, 2, 3], [4, 2, 3, 1]];

gen := SL2Gens([A, B], P);
reduce_step(gen);
assert gen`type eq "df" and gen`witness eq [A, B];

gen := SL2Gens([A, B*A^-1], P);
reduce_step(gen);
assert gen`type eq "un" and gen`witness in {[A, B], [A, B^-1]};

gen := SL2Gens([B*A*B^-1, B], P);
reduce_step(gen);
assert gen`type eq "un" and gen`witness eq [A^-1, B];
F := Universe(gen`witness_word);
assert gen`witness_word eq [F.2^-1 * F.1^-1 * F.2, F.2];

// Reduction 2

gen := SL2Gens([A*B^2, B^-2*A^-1*B], P);
RecognizeDiscreteTorsionFree(gen);
assert gen`type eq "df" and ReducedGenerators(gen) in {[A, B], [A^-1, B], [A, B^-1], [A^-1, B^-1]};
assert IsDiscreteFree(gen);

A := M![1, w, 0, 1];
B := M![1, 1, 0, 1];
gen := SL2Gens([A, B], P);
RecognizeDiscreteTorsionFree(gen);
assert gen`type eq "ab";
assert not IsDiscreteTorsionFree(gen);

A := M![1, 2, -1, -1];
B := M![1, 0, 2, 1];
gen := SL2Gens([A*B^2, B^-2*A^-1*B], P);
RecognizeDiscreteTorsionFree(gen);
assert gen`type eq "el";
assert not IsDiscreteTorsionFree(gen);

A := M![1, 2, 0, 1];
B := M![2, 2, 0, 1/2];
gen := SL2Gens([A*B^2, B^-2*A^-1*B], P);
RecognizeDiscreteTorsionFree(gen);
assert gen`type eq "sm";
assert not IsDiscreteTorsionFree(gen);

// Cocompact reduction

Q := Rationals();
P<x> := PolynomialRing(Q);
K<w> := NumberField(x^2 - 3);
M := MatrixAlgebra(K, 2);
P := RealPlaces(K)[1];

A := M![2 - 2*w, 3, -3, 2+2*w];
B := M![2, w, w, 2];
C := M![2+w, 0, 0, 2-w];
D := M![2, -3-2*w, 3-2*w, 2];
gen := SL2Gens([A, B, C, D], P);
RecognizeDiscreteTorsionFree(gen);
assert gen`type eq "dc";
G := gen`FPgrp;
assert Relations(G) eq [ G.1 * G.4^-1 * G.2^-1 * G.1^-1 * G.2 * G.3^-1 * G.4 * G.3 = Id(G) ];

gen := SL2Gens([A*B, B*D, D^-1*B^-2*A^-1*C, B*D^2], P : psl);
RecognizeDiscreteTorsionFree(gen);
assert gen`type eq "dc";
G := gen`FPgrp;
assert Relations(G) eq [ G.1 * G.4 * G.2^-1 * G.1^-1 * G.2 * G.3 * G.4^-1 * G.3^-1 = Id(G) ];

S := ReducedGenerators(gen);
b, word := IsElementOf(S[4] * S[3], gen);
H := AutomaticGroup(G);
assert b and H!word eq H.4 * H.3;
assert H!(gen`iso(((gen`iso)^-1)(G.1*G.2))) eq H.1*H.2;

assert IsElementOf(-One(M), gen);

// Negative elements

A := M![-1/2, 0, 0, -2];
B := M![1/8, 0, 0, 8];
gen := SL2Gens([A, B], P);
RecognizeDiscreteTorsionFree(gen);
assert IsDiscreteTorsionFree(gen);
assert HasNegativeOne(gen);
assert Rank(gen) eq 2;
assert ReducedGenerators(gen)[Rank(gen)] eq -One(M);

A := M![1, 1, 1, 2];
B := M![2, 1, 1, 1];
gen := SL2Gens([A*B^2, B^-2*A^-1*B, -A^3*B], P);
RecognizeDiscreteTorsionFree(gen);
assert IsDiscreteTorsionFree(gen);
assert HasNegativeOne(gen);
assert Rank(gen) eq 3;
assert ReducedGenerators(gen)[Rank(gen)] eq -One(M);
