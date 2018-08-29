// the following function needs to be changed in the distributed version.
intrinsic MyUnitGroup (A::AlgMat) -> GrpMat
  { The group of units of the matrix algebra A. }
  isit, U := UnitGroup (A);
  assert isit;
return U;
end intrinsic;

// not sure where this should go, but I could not find it in Magma
intrinsic ElementaryMatrix (K::FldFin, m::RngIntElt, n::RngIntElt, 
                  i::RngIntElt, j::RngIntElt) -> ModMatFldElt
  { The (i,j) elementary m x n matrix over the field K }
  Eij := KMatrixSpace (K, m, n)!0;
  Eij[i][j] := 1;
return Eij;
end intrinsic;

MySort := function (str1, str2)
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
intrinsic RestrictAction (X::Mtrx, U::ModTupFld) -> Mtrx
  { Compute the restriction of X to an invariant subspace U. }
  require U*X subset U : "X does not stabilize U";
     XU := Matrix ([ Coordinates (U, U.i * X) : i in [1..Ngens (U)] ]);
return XU;
end intrinsic;
