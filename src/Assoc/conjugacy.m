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
     isit1, T1 := IsAbsolutelyIrreducible (M1);
     isit2, T2 := IsAbsolutelyIrreducible (M2);
     if (isit1 ne isit2) then
          return false, _;
     elif (isit1 and isit2) then
          assert S1 eq S2;
          return true, Identity (Generic (S1));
     else   // centres are extension fields
          Z2 := sub < Generic (S2) | T2 >;
          return __IsConjugateCyclic (T1, Z2); 
     end if;
end function;


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
  
     J1, B1 := WedderburnDecomposition (A1);
     J2, B2 := WedderburnDecomposition (A2);
     if Dimension (J1) ne Dimension (J2) then
          return false, _;
     end if; 
     require Dimension (J1) eq 0 : "algebras must be semisimple"; 
  
     M1 := RModule (A1);
     M2 := RModule (A2);
     require IsIrreducible (M1) and IsIrreducible (M2) : "coming soon at a terminal near you";
  
     isit, C := __IsConjugate_IRRED (A1, A2);
     if not isit then
          return false, _;
     else
          g := GL (Degree (A1), BaseRing (A1))!(C^-1); 
          assert A1 ^ g eq A2;  
          return true, g; 
     end if;

end intrinsic;
  



// A reformulation of the conjugacy test in the language of modules
intrinsic IsSimilar (M::ModRng, N::ModRng) -> BoolElt, Map
  {Decides if the given modules are similar.}
	A := Action(M);
	cyc, genA := IsCyclic(A);
	if not cyc then
		return false, _;
	end if;
	B := Action(N);
	cyc, genB := IsCyclic(B);
	if not cyc then 
		return false, _;
	end if;
	cycB := sub<Generic(B)| [genB] >;
	return __IsConjugateCyclic(genA, cycB);
//	if test then
//		f := hom<M->N | x:->N!(Vector(x)*X), y:->M!(Vector(y)*X^(-1)) >;
//		return true, f;
//	end if;
	return false, _;
end intrinsic;
