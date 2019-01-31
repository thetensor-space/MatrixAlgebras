/* general functions that work for any type of algebra (assoc, Lie, etc) */
__AnnihilatesModule := function (J, U)
return forall { i : i in [1..Ngens (J)] | forall { t : t in [1..Ngens (U)] |
          U.t * J.i eq 0 } };
end function;

__IsBlockDiagonalMatrix := function (X, partition)
  n := Nrows (X);
  assert n eq Ncols (X);
  assert n eq &+ partition;
  pos := 1;
  isit := true;
  for i in [1..#partition] do
       m := partition[i];
       isit and:= forall { s : s in [pos..pos+m-1] |
                    forall { t : t in [pos+m..n] | 
                        (X[s][t] eq 0) and (X[t][s] eq 0)
                           }
                         };
       pos +:= m;
  end for;
return isit;
end function;


/* Image under conjugacy of invertible matrices on algebras and their elements */

intrinsic '^' (x::AlgMatElt, g::GrpMatElt) -> AlgMatElt
  {x^g}
return Generic (Parent (x))!(g^-1 * x * g);
end intrinsic;


intrinsic '^' (A::AlgMat, g::GrpMatElt) -> AlgMat
  {A^g}
  B := sub < Generic (A) | [ A.i ^ g : i in [1..Ngens (A)] ] >;
return B;
end intrinsic;


intrinsic '^' (x::AlgMatLieElt, g::GrpMatElt) -> AlgMatLieElt
  {x^g}
return Generic (Parent (x))!(Matrix (x) ^ g);
end intrinsic;


intrinsic '^' (L::AlgMatLie, g::GrpMatElt) -> AlgMatLie
  {A^g}
  M := sub < Generic (L) | [ L.i ^ g : i in [1..Ngens (L)] ] >;
return M;
end intrinsic;


        /*
         * The remainder of the file is a home for intrinsics that
         * are used in this package but that seem likely to be 
         * useful in various contexts beyond it.
         */


// I could not find this in Magma but it seems general enough to warrant an intrinsic
intrinsic ElementaryMatrix (K::FldFin, m::RngIntElt, n::RngIntElt, 
                  i::RngIntElt, j::RngIntElt) -> ModMatFldElt
  { The (i,j) elementary m x n matrix over the field K }
  Eij := KMatrixSpace (K, m, n)!0;
  Eij[i][j] := 1;
return Eij;
end intrinsic;


// Compute matrix of restriction of X to invariant subspace U 
intrinsic RestrictAction (X::Mtrx, U::ModTupFld) -> Mtrx
  { Compute the restriction of X to an invariant subspace U. }
  require U*X subset U : "X does not stabilize U";
     XU := Matrix ([ Coordinates (U, U.i * X) : i in [1..Ngens (U)] ]);
return XU;
end intrinsic;


__AD := function (L, x)
return Matrix ([ Coordinates (L, x*y) : y in Basis (L) ]);
end function;


intrinsic IsAdNilpotent (L::AlgLie, x::AlgLieElt) -> BoolElt, RngIntElt
  { Decide whether x in L is ad-nilpotent.}
  ad_x := __AD (L, x);
return IsNilpotent (ad_x);
end intrinsic;

intrinsic Exponentiate (z::AlgMatElt) -> GrpMatElt
  { Exponentiate the nilpotent matrix z.}
  require IsNilpotent (z) : "given element is not nilpotent";
	u := z^0;
	i := 1;
	v := z;
	while not (v eq 0) do
		u +:= v / Factorial (i);
		i +:= 1;
		v *:= z;
	end while;
return GL (Degree (Parent (z)), BaseRing (Parent (z)))!u;
end intrinsic;

intrinsic Exponentiate (z::AlgMatLieElt) -> GrpMatElt
  { Exponentiate the nilpotent matrix z.}
  z0 := MatrixAlgebra (BaseRing (Parent (z)), Degree (Parent (z)))!z;
return Exponentiate (z0);
end intrinsic;

