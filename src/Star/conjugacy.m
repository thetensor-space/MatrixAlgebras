/* functions to decide conjugacy of matrix *-algebras */

// REFER BACK TO "conjugacy.m" in Assoc, and mimic the general structure

             
/*
  GIVEN:   S1 and S2 known to simple *-algebras acting irreducibly on V.
  RETURN:  g in GL(V) with S1^g = S2 and (s^*)^g = (s^g)^# for all g in S1.
  
  Give *-algebras S1 and S2, find g with S1^g = S2 AND (s1^g)* = (s1*)^g
  (1) find g0 with S1^g0 = S2 as associative algebras
  (2) form iso S2 --> full matrix algebra over extension fields
  (3) induce *1g from S1^g and *2 from S2
  (4) compute forms F1g corresponding to *1g and F2 corresponding to *2
  (5) transform F1g to F2 using H in GL(ext field)
  (7) pull H back h normalizing S2 (and S1^g).
  (8) then g*h does the trick 
*/
__IsConjugate_IRRED := function (S1, S2)

  // conjugate S1 to S2 as matrix algebras 
  isit, g := IsConjugate (S1, S2); 
  if not isit then 
       return false, _;
  end if;
  S1g := S1^g;    // this inherits the * from S1
  
  // move to the full matrix algebra over the correct field
  T, S2toT, TtoS2 := SimpleAlgebraToFullMatrixAlgebra (S2);

  // put the two different involutions
  star1g := hom < T -> T | x :-> ((x @ TtoS2) @ S1g`Star) @ S2toT >;
  star2 := hom < T -> T | x :-> ((x @ TtoS2) @ S2`Star) @ S2toT >;
  T1g := T;    
  T1g`Star := star1g;
  assert RecogniseClassicalSSA (T1g);
  T2 := T;     
  T2`Star := star2;
  assert RecogniseClassicalSSA (T2);
  param := SimpleParameters  (T1g);
  
  // if these *-algebras have different parameters then they are not conjugate
  if param ne SimpleParameters (T2) then
       return false, _;
  end if;
  
  // retrieve the classical forms defining the involutions
  
  // just bilinear form for now
  M1g := RModule (T1g);
  dM1g := RModule (sub < T | [ Transpose (T1g.i @ T1g`Star) : i in [1..Ngens (T1g)] ] >);
  isit, X1g := IsIsomorphic (M1g, dM1g);     assert isit;
  
  
  /*
  assert (S2 ^ h eq S2);
  
  assert forall { i : i in [1..Ngens (S1)] | 
                                    (S1.i @ S1`Star) ^ g eq (S1.i ^g) @ S2`Star };
  */
  
return X1g;
     
end function;


