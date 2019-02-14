__inflate := function (M, alpha)
  m := Nrows (M);
  e := Degree (Codomain (alpha));
  d := m * e;
  N := MatrixAlgebra (BaseRing (Codomain (alpha)), d)!0;
  for i in [1..m] do
    for j in [1..m] do
      InsertBlock (~N, M[i][j] @ alpha, 1+(i-1)*e, 1+(j-1)*e);
    end for;
  end for;
return N;
end function;

__condense := function (N, beta)
  d := Nrows (N);
  e := Degree (Domain (beta));
  m := d div e;
  M := MatrixAlgebra (Codomain (beta), m)!0;
  for i in [1..m] do
    for j in [1..m] do
      xij := ExtractBlock (N, 1+(i-1)*e, 1+(j-1)*e, e, e);
      M[i][j] := xij @ beta;
    end for;
  end for;
return M;
end function;

/*
  The following function seems to be embedded in various intrinsics
  for matrix algebras and *-algebras. It seems a good idea to isolate
  it, although we don't necessarily want to make it an intrinsic itself.
  
  INPUT:  simple matrix k-algebra A acting irreducibly on its k-space
  OUTPUT:  a full matrix K-algebra, B, where K is an extension of k, 
           together with inverse k-algebra isomorphisms f and g. 
*/
__IsomorphismWithStandardSimple := function (A)

     k := BaseRing (A);
     d := Degree (A);
     M := RModule (A);
          assert IsIrreducible (M);
     isit, zA, e := IsAbsolutelyIrreducible (M);
     ZA := sub < A | zA >;
     m := d div e;
     
     // trivial case
     if isit then
          assert Dimension (A) eq d^2;
          B := A;
          f := hom < A -> B | x :-> x >;
          g := hom < B -> A | y :-> y >;
          return A, f, g;
     end if;
     
     // write ZA in block diagonal form
     MZA := RModule (ZA);
     IMZA := IndecomposableSummands (MZA);
           assert #IMZA eq m;
     V := VectorSpace (k, d);
     IV := [ sub < V | [ V!(MZA!(N.i)) : i in [1..Ngens (N)] ] > : N in IMZA ];
           assert forall { U : U in IV | Dimension (U) eq e };
     C := Matrix (&cat [ Basis (IV[i]) : i in [1..m] ]);
     blocks := < Identity (MatrixAlgebra (k, e)) >;
     for i in [2..#IMZA] do
          isit, bl := IsIsomorphic (IMZA[1], IMZA[i]);
               assert isit;
          Append (~blocks, bl);
     end for;
     
     // form isomorphism with matrix algebra over extension field
     D := DiagonalJoin (blocks);
     E := D * C;
     z := E * zA * E^-1;
     Z := sub < MatrixAlgebra (k, e) | ExtractBlock (z, 1, 1, e, e) >;
     K, ZtoK, KtoZ := AlgebraToField (Z);
     B := MatrixAlgebra (K, m);
     f := hom < A -> B | x :->  __condense (E * x * E^-1, ZtoK) >;
     g := hom < B -> A | y :->  E^-1 * __inflate (y, KtoZ) * E >;
return B, f, g;
end function;


// just for testing purposes
TEST := function (k, m, e)
  MA := MatrixAlgebra (k, m*e);
  repeat
       x := Random (MatrixAlgebra (k, e));
       mx := MinimalPolynomial (x);
  until IsIrreducible (mx);
  z := DiagonalJoin (< x : i in [1..m] >);
  C := Centralizer (MA, sub < MA | z >);
  g := Random (GL (m*e, k));
  A := sub < MA | [ g * C.i * g^-1 : i in [1..Ngens (C)] ] >;
return A;
end function;