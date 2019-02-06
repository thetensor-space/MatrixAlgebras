/* functions to decide conjugacy of associative matrix algebras */

import "../Jordan.m" : __JordanNormalForm;
import "cyclic.m" : __IsomorphismBetweenFields;
import "../utility.m" : __IsBlockDiagonalMatrix;

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



__SimpleType := function (S, MP);
     V := VectorSpace (BaseRing (S), Degree (S));
     U := sub < V | [ V.i * S.j : i in [1..Degree (S)] , j in [1..Ngens (S)] ] >;
     B := Basis (U);
     U := VectorSpaceWithBasis (B);
     n := Dimension (U);
     gens := [ RestrictAction (S.i, U) : i in [1..Ngens (S)] ];
     SU := sub < MatrixAlgebra (BaseRing (S), n) | gens >;
     C, t := __PreprocessSimple (SU);
     I := [ -Dimension (U meet MP[i]) : i in [1..#MP] ];
     tt := [* t , I *];
return tt;
end function;


__MySort := function (pair1, pair2)
     if (pair1[1] eq pair2[1]) then
         if (pair1[2] eq pair2[2]) then
              return 0;
         elif (pair1[2] lt pair2[2]) then
              return -1;
         else 
              return 1;
         end if;
    elif (pair1[1] lt pair2[1]) then
         return -1;
    else
         return 1;
    end if;
end function;

__PreprocessSemisimple := function (S : PART := [])
     k := BaseRing (S);
     V := VectorSpace (k, Degree (S));
     MODPART := [* *];
     pos := 1;
     for i in [1..#PART] do
           m := PART[i];
           Vi := sub < V | [ V.j : j in [pos..m-1+pos] ] >;
           Append (~MODPART, Vi);
           pos +:= m;
     end for;
     // sort the ideals of S according to type and action on module of partition
     IDS := IndecomposableSummands (S);
     Sort (~IDS, func<x,y|__MySort(__SimpleType(x, MODPART),__SimpleType(y, MODPART))>);
     // collect the necessary information to determine conjugacy     
     m := #IDS;     
     B := [ ];
     degrees := [ ];
     INTS := [ ];
     for i in [1..m] do
          J := IDS[i];
          VJ := sub < V | [ V.i * J.j : i in [1..Degree (S)] , j in [1..Ngens (J)] ] >;
          Append (~INTS, [ Dimension (VJ meet MODPART[i]) : i in [1..#MODPART] ]);
          B cat:= Basis (VJ);
          Append (~degrees, Dimension (VJ));
     end for;
     B := Matrix (B);
     BIDS := [ sub < Generic (IDS[i]) | 
                [ B * (IDS[i]).j * B^-1 : j in [1..Ngens (IDS[i])] ] > : i in [1..m] ];
     pos := 1;
     blocks := < >;
     types := [ ];
     positions := [ ];
     for i in [1..m] do
          J := BIDS[i];
          SJ := sub < MatrixAlgebra (k, degrees[i]) |
           [ ExtractBlock (J.j, pos, pos, degrees[i], degrees[i]) : j in [1..Ngens (J)] ] >;
          BJ, tJ := __PreprocessSimple (SJ);
          Append (~blocks, BJ);
          Append (~types, tJ);
          Append (~positions, pos);
          pos +:= degrees[i];
     end for;  
     C := DiagonalJoin (blocks);
     NICE_IDEALS := [ sub < Generic (BIDS[i]) | 
                [ C * (BIDS[i]).j * C^-1 : j in [1..Ngens (BIDS[i])] ] > : i in [1..m] ];
return NICE_IDEALS, C*B, types, positions, INTS;
end function;


/* 
  Decide whether two matrix algebras are conjugate in the group of invertible
  transformations of their ambient row space.
  
  At present this function can only be used for algebras that are either
  cyclic or semisimple.
*/
intrinsic IsConjugate (A1::AlgMat, A2::AlgMat : PARTITION := []) -> BoolElt , GrpMatElt

  { True iff A1 and A2 are conjugate in the ambient group of invertible matrices.}
  
     // easy tests first
     if Degree (A1) ne Degree (A2) then
          vprint MatrixAlgebras, 1 : "A1 and A2 have different degrees";
          return false, _;
     end if;
     
     if Dimension (A1) ne Dimension (A2) then
          vprint MatrixAlgebras, 1 : "A1 and A2 have different dimensions";
          return false, _;
     end if;
     
     k := BaseRing (A1);
     d := Degree (A1);
     
     if #PARTITION eq 0 then
          PARTITION := [ d ];
     end if;
  
     require (d eq &+ PARTITION) : "the specified partition is incompatible with the degree of L";
  
     require forall { i : i in [1..Ngens (A1)] | __IsBlockDiagonalMatrix (Matrix (A1.i), PARTITION) } :
        "the specified partition is incompatible with the block structure of A1";
     
     require forall { i : i in [1..Ngens (A2)] | __IsBlockDiagonalMatrix (Matrix (A2.i), PARTITION) } :
        "the specified partition is incompatible with the block structure of A2";
  
     // handle the cyclic case first
     isit1, T1 := IsCyclic (A1);
     if isit1 then
          isit2, T2 := IsCyclic (A2);
          if not isit2 then 
               return false, _;
          else
               B2 := sub < Generic (A2) | T2 >; 
               isit, C := __IsConjugateCyclic (T1, B2);
               if not isit then
                    return false, _;
               else
                    g := GL (Degree (A1), BaseRing (A1))!(C^-1); 
                    assert A1 ^ g eq A2;
                    return true, g;  
               end if; 
          end if;  
     end if;
  
     J1, B1 := WedderburnDecomposition (A1);
     J2, B2 := WedderburnDecomposition (A2);
     if Dimension (J1) ne Dimension (J2) then
          return false, _;
     end if; 
     require Dimension (J1) eq 0 : "algebras must be semisimple"; 
     
     IDS1, C1, type1, pos1, INTS1 := __PreprocessSemisimple (A1 : PART := PARTITION);
     IDS2, C2, type2, pos2, INTS2 := __PreprocessSemisimple (A2 : PART := PARTITION);
     if type1 ne type2 then   // remember, these are sorted
          vprint MatrixAlgebras, 1 : "A1 has semisimple type", type1, "while A2 has type", type2;
          return false, _;
     end if;
     if INTS1 ne INTS2 then
          vprint MatrixAlgebras, 1 : 
"A1 and A2 are conjugate, but not by a matrix respecting the given partition ", type2;
          return false, _;
     end if;
     vprint MatrixAlgebras, 1 : "A1 and A2 both have semisimple type", type1;
     
     // conjugate one ideal at a time
     m := #IDS1;
     blocks := < >;
     for i in [1..m] do
          t := type1[i];
          n := t[1] * t[3];
          J1 := IDS1[i];
          J2 := IDS2[i];
          S1 := sub < MatrixAlgebra (k, n) |
           [ ExtractBlock (J1.j, pos1[i], pos1[i], n, n) : j in [1..Ngens (J1)] ] >;
          S2 := sub < MatrixAlgebra (k, n) |
           [ ExtractBlock (J2.j, pos2[i], pos2[i], n, n) : j in [1..Ngens (J2)] ] >; 
          isit, D := __IsConjugate_IRRED (S1, S2);    assert isit;
          B := DiagonalJoin (< D : j in [1..t[2]] >);
          Append (~blocks, B);
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
