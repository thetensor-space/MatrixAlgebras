// not sure where this should go, but I could not find it in Magma
intrinsic ElementaryMatrix (K::FldFin, m::RngIntElt, n::RngIntElt, 
                  i::RngIntElt, j::RngIntElt) -> ModMatFldElt
  { The (i,j) elementary m x n matrix over the field K }
  Eij := KMatrixSpace (K, m, n)!0;
  Eij[i][j] := 1;
return Eij;
end intrinsic;

REDUCE_TO_BASIS := function (X)
    // X contains a basis of the matrix space it spans
    k := BaseRing (Parent (X[1]));
    m := Nrows (X[1]);
    n := Ncols (X[1]);
    ms := KMatrixSpace (k, m , n);
    U := sub < ms | [ ms!(X[i]) : i in [1..#X] ] >;
    d := Dimension (U);
    if d eq #X then
         return [1..d];
    else
         J := [ Min ({ i : i in [1..#X] | X[i] ne 0 }) ];
         j := J[1];
         W := sub < ms | [ ms!(X[j]) : j in J ] >;
         while Dimension (W) lt d do
              j +:= 1;
              x := ms!(X[j]);
              if not x in W then
                   Append (~J, j);
                   W := sub < ms | [ ms!(X[j]) : j in J ] >;
              end if;
         end while;
         return J;
    end if;
end function;

MY_SORT := function (str1, str2)
     if str1 eq str2 then
         return 0;
     elif str1 lt str2 then
         return -1;
     else 
         return 1;
     end if;
end function;

/* 
  Given a matrix X acting naturally on V and an invariant subspace W of V,
  compute the matrix for the restriction of X to W (rel to given basis)
*/
RESTRICT := function (X, U)
     assert Ngens (U) eq Dimension (U);
     assert U*X subset U;
     XU := Matrix ([ Coordinates (U, U.i * X) : i in [1..Ngens (U)] ]);
return XU;
end function;
