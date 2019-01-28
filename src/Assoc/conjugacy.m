/* functions to decide conjugacy of associative matrix algebras */

import "../Jordan.m" : __JordanNormalForm;
import "cyclic.m" : __IsomorphismBetweenFields;

//   given arbitrary <T1> and k[<T2>], determine whether or not <T1> can be
//   conjugated into k[<T2>] and, if so, find a C that does the trick.
__IsConjugateCyclic := function (T1, R)
     T2 := R.1;
     MA := Generic (R);
     d := Degree (MA);
     J1, C1, info1 := __JordanNormalForm (T1);
     J2, C2, info2 := __JordanNormalForm (T2);
     I1 := [ < Degree (info1[i][1]) , info1[i][2] > : i in [1..#info1] ];
     I2 := [ < Degree (info2[i][1]) , info2[i][2] > : i in [1..#info2] ];
     if I1 ne I2 then 
         return false, _; 
     end if;    
     // conjugate the primary components 
     pos := 1;
     blocks := < >;
     for i in [1..#info1] do     
	      di := Degree (info1[i][1]);
          parti := info1[i][2];    
          // find the basic field isomorphism 
          Ti1 := ExtractBlock (J1, pos, pos, di, di);
          Ti2 := ExtractBlock (J2, pos, pos, di, di);
          Di := __IsomorphismBetweenFields (Ti1, Ti2);    
          // propogate basic iso to the other blocks in primary component
          ni := &+ parti;
          Ci := DiagonalJoin (< Di : i in [1..ni] >);
          Append (~blocks, Ci);         
          pos +:= di * ni; 
     end for;   
     C := DiagonalJoin (blocks);
     assert Nrows (C) eq d;    
     C := C2^-1 * C * C1;
     if not C * T1 * C^-1 in R then
         return false, _;
     end if;
return true, C;
end function;

             
__IsConjugate_IRRED := function (S1, S2)
     M1 := RModule (S1);
     M2 := RModule (S2);
     isit1, T1, e1 := IsAbsolutelyIrreducible (M1);
     isit2, T2, e2 := IsAbsolutelyIrreducible (M2);
     if (isit1 ne isit2) then
          return false, _, _;
     elif (isit1 and isit2) then
          assert S1 eq S2;
          return true, Identity (Generic (S1)), [Degree (S1), 1, 1];
     else   // centres are extension fields
          Z2 := sub < Generic (S2) | T2 >;
          isit, C := __IsConjugateCyclic (T1, Z2); 
          if not isit then
               return false, _, _;
          end if;
          return true, C, [Degree (S1) div e1, 1, e1];
     end if;
end function;


__PreprocessSimple := function (S)
     k := BaseRing (S);
     M := RModule (S);
     V := VectorSpace (k, Degree (S));
     SUMS := IndecomposableSummands (M);
     m := #SUMS;
     VS := [ sub < V | [ Vector (M!(N.i)) : i in [1..Ngens (N)] ] > : N in SUMS ];
     dims := { Dimension (U) : U in VS };  assert #dims eq 1; 
     assert exists (d){ a : a in dims };
     C := Matrix (&cat [ Basis (U) : U in VS ]);
     T := sub < Generic (S) | [ C * S.i * C^-1 : i in [1..Ngens (S)] ] >;
     // T is now in block diagonal form
     X := sub < MatrixAlgebra (k, d) | [ ExtractBlock (T.i, 1, 1, d, d) : 
                        i in [1..Ngens (T)] ] >;
     //propagate D to the other summands
     MX := RModule (X);
     isit, Z, e := IsAbsolutelyIrreducible (MX);
     if isit then e := 1; end if;
     type := [ d div e , m , e ];
     blocks := < Identity (MatrixAlgebra (k, d)) >;
     for i in [2..m] do
          Y := sub < MatrixAlgebra (k, d) | [ ExtractBlock (T.j, 1+(i-1)*d, 1+(i-1)*d, d, d) : 
                        j in [1..Ngens (T)] ] >;
          MY := RModule (Y);
          isit, E := IsIsomorphic (MX, MY);   assert isit;
          Append (~blocks, E);
     end for;
     E := DiagonalJoin (blocks);     
return E * C, type;
end function;


__PreprocessSemisimple := function (S)
     k := BaseRing (S);
     V := VectorSpace (k, Degree (S));
     IDS := IndecomposableSummands (S);
     m := #IDS;     
     B := [ ];
     degrees := [ ];
     for i in [1..m] do
          J := IDS[i];
          VJ := sub < V | [ V.i * J.j : i in [1..Degree (S)] , j in [1..Ngens (J)] ] >;
          B cat:= Basis (VJ);
          Append (~degrees, Dimension (VJ));
     end for;
     B := Matrix (B);
     BIDS := [ sub < Generic (IDS[i]) | 
                [ B * (IDS[i]).j * B^-1 : j in [1..Ngens (IDS[i])] ] > : i in [1..m] ];
     pos := 1;
     blocks := < >;
     types := [ ];
     for i in [1..m] do
          J := BIDS[i];
          SJ := sub < MatrixAlgebra (k, degrees[i]) |
           [ ExtractBlock (J.j, pos, pos, degrees[i], degrees[i]) : j in [1..Ngens (J)] ] >;
          BJ, tJ := __PreprocessSimple (SJ);
          Append (~blocks, BJ);
          Append (~types, tJ);
          pos +:= degrees[i];
     end for;     
     C := DiagonalJoin (blocks);
     NICE_IDEALS := [ sub < Generic (BIDS[i]) | 
                [ C * (BIDS[i]).j * C^-1 : j in [1..Ngens (BIDS[i])] ] > : i in [1..m] ];
return NICE_IDEALS, C*B, types;
end function;


/* 
  Decide whether two matrix algebras are conjugate in the group of invertible
  transformations of their ambient row space.
  
  At present this function can only be used for algebras that are either
  cyclic or semisimple.
*/
intrinsic IsConjugate (A1::AlgMat, A2::AlgMat) -> BoolElt , GrpMatElt

  { True iff A1 and A2 are conjugate in the ambient group of invertible matrices.}
  
     // easy tests first
     if Dimension (A1) ne Dimension (A2) then
          return false, _;
     end if;
  
     // handle the cyclic case first
     isit1, T1 := IsCyclic (A1);
     if isit1 then
          isit2, T2 := IsCyclic (A2);
          if not isit2 then 
               return false, _;
          else
               isit, C := __IsConjugateCyclic (T1, A2);
               if not isit then
                    return false, _;
               else
                    g := GL (Degree (A1), BaseRing (A1))!(C^-1); 
                    assert A1 ^ g eq A2;
                    return true, g;  
               end if; 
          end if;  
     end if;
  
     k := BaseRing (A1);
     d := Degree (A1);
  
     J1, B1 := WedderburnDecomposition (A1);
     J2, B2 := WedderburnDecomposition (A2);
     if Dimension (J1) ne Dimension (J2) then
          return false, _;
     end if; 
     require Dimension (J1) eq 0 : "algebras must be semisimple"; 
     
     IDS1, C1, types1 := __PreprocessSemisimple (A1);
     IDS2, C2, types2 := __PreprocessSemisimple (A2);
     if types1 ne types2 then   // remember, these are sorted
          return false, _;
     end if;
     // else, if they have the same types, they have to be conjugate!
     
     // conjugate one ideal at a time
     m := #IDS1;
     blocks := < >;
     pos := 1;
     for i in [1..m] do
          t := types1[i];
          n := t[1] * t[3];
          J1 := IDS1[i];
          J2 := IDS2[i];
          S1 := sub < MatrixAlgebra (k, n) |
           [ ExtractBlock (J1.j, pos, pos, n, n) : j in [1..Ngens (J1)] ] >;
          S2 := sub < MatrixAlgebra (k, n) |
           [ ExtractBlock (J2.j, pos, pos, n, n) : j in [1..Ngens (J2)] ] >; 
          isit, D := __IsConjugate_IRRED (S1, S2);    assert isit;
          B := DiagonalJoin (< D : j in [1..t[2]] >);
          Append (~blocks, B);
          pos +:= &* t;
     end for;
     B := DiagonalJoin (blocks);
     
     g := GL (Degree (A1), k)!(C2^-1 * B * C1)^-1; 
     assert A1 ^ g eq A2;  

return true, g;

end intrinsic;
  


// A reformulation of the conjugacy test in the language of modules
intrinsic IsSimilar (M::ModRng, N::ModRng) -> BoolElt, Map
  {Decides if the given modules are similar.}
	A := Action (M);
	B := Action (N);
return IsConjugate (A, B);
end intrinsic;
