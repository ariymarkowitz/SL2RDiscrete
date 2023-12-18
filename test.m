Q := Rationals();
P<x> := PolynomialRing(Q);
K<w> := NumberField(x^3 - x^2 - 2*x + 1);

M := MatrixAlgebra(K, 2);
P := RealPlaces(K)[1];

assert is_hyperbolic(M![w, 0, 0, 1/w], P);
assert is_elliptic(M![0, w, -(1/w), 0], P);

A := M![1, w, 0, 1];
B := M![1, 3/5*w, 0, 1];
b, C := abelian_is_discrete(A, B, P);
assert b;
assert Eltseq(C) eq [1, 1/5, 0, 1];

A := M![1, w, 0, 1];
B := M![1, 1, 0, 1];
assert not abelian_is_discrete(A, B, P);

A := M![1, 2, 0, 1];
B := M![1, 0, 2, 1];
Xpm, inv := get_gens_pm([A, B]);
assert Xpm eq [A, B, A^-1, B^-1];
assert Eltseq(inv) eq [3, 4, 1, 2];
assert Eltseq(bounding_path_perm(Xpm, inv, P)) eq [4, 2, 3, 1];
assert short_words(Xpm, inv, P) eq [[1], [1, 4], [2], [3], [4], [4, 1]];

type, result := reduce_step([A, B], P);
assert type eq 1 and result eq [A, B];

type, result := reduce_step([A, B*A^-1], P);
assert type eq 0 and result in {[A, B], [A, B^-1]};

type, result := reduce_step([B*A*B^-1, B], P);
assert type eq 0 and result in {[A*B^-1, B], [B*A, B]};

type, result := reduce([A*B^2, B^-2*A^-1*B], P);
assert type eq 1 and result in {[A, B], [A^-1, B], [A, B^-1], [A^-1, B^-1]};

A := M![1, 1, 1, 2];
B := M![2, 1, 1, 1];
Xpm, inv := get_gens_pm([A, B]);
assert Xpm eq [A, B, A^-1, B^-1];
assert Eltseq(inv) eq [3, 4, 1, 2];
assert Eltseq(bounding_path_perm(Xpm, inv, P)) eq [4, 1, 2, 3];
assert short_words(Xpm, inv, P) eq [[1], [1, 4], [1, 4, 3], [1, 4, 3, 2], [2], [2, 1], [2, 1, 4], [2, 1, 4, 3], [3], [3, 2], [3, 2, 1], [3, 2, 1, 4], [4], [4, 3], [4, 3, 2], [4, 3, 2, 1]];

type, result := reduce_step([A, B], P);
assert type eq 1 and result eq [A, B];

type, result := reduce_step([A, B*A^-1], P);
assert type eq 0 and result in {[A, B], [A, B^-1]};

type, result := reduce_step([B*A*B^-1, B], P);
assert type eq 0 and result in {[A*B^-1, B], [B*A, B]};

type, result := reduce([A*B^2, B^-2*A^-1*B], P);
assert type eq 1 and result in {[A, B], [A^-1, B], [A, B^-1], [A^-1, B^-1]};

A := M![1, w, 0, 1];
B := M![1, 1, 0, 1];
type, result := reduce([A*B^2, B^-2*A^-1*B], P);
assert type eq 3;

A := M![1, 2, -1, -1];
B := M![1, 0, 2, 1];
type, result := reduce([A*B^2, B^-2*A^-1*B], P);
assert type eq 2;
