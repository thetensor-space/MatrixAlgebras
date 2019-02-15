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
  for matrix algebras and *-algebras. It seems a good idea to isolate it.
  
  INPUT:  simple matrix k-algebra A acting irreducibly on its k-space
  OUTPUT:  a full matrix K-algebra, B, where K is an extension of k, 
           together with inverse k-algebra isomorphisms f and g. 
*/
intrinsic SimpleAlgebraToFullMatrixAlgebra (A::AlgMat) -> AlgMat, Map, Map

  { Compute inverse k-algebra isomorphisms between the simple k-algebra A, k a finite field,
    and the (full) K-algebra B to which it is isomorphic, where K is an extension of k. }

     k := BaseRing (A);
     
     require IsFinite (k) : "A must be an algebra over a finite field";
     
     d := Degree (A);
     M := RModule (A);
          
     require IsIrreducible (M) : "A must act irreducibly on its underlying row space";
    
     isit, zA, e := IsAbsolutelyIrreducible (M);
     
     // trivial case
     if isit then
          assert Dimension (A) eq d^2;
          B := A;
          f := hom < A -> B | x :-> x >;
          g := hom < B -> A | y :-> y >;
          return A, f, g;
     end if;
     
     m := d div e;
     ZA := sub < A | zA >;
               // sanity check
               assert Dimension (A) eq m^2 * e;
     
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
               // sanity check
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
     AtoB := hom < A -> B | x :->  __condense (E * x * E^-1, ZtoK) >;
     BtoA := hom < B -> A | y :->  E^-1 * __inflate (y, KtoZ) * E >;
     
return B, AtoB, BtoA;

end intrinsic;


