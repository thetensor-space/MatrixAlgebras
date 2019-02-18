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
  assert forall { i : i in [1..Ngens (S1)] |
                             (S1.i @ S1`Star) ^ g eq (S1.i ^ g) @ S1g`Star };

  // move to the full matrix algebra over the correct field
  T, S2toT, TtoS2 := SimpleAlgebraToFullMatrixAlgebra (S2);

  // put the two different involutions
  star1g := hom < T -> T | x :-> ((x @ TtoS2) @ S1g`Star) @ S2toT >;
  star2 := hom < T -> T | x :-> ((x @ TtoS2) @ S2`Star) @ S2toT >;
  T1g := sub < Generic (T) | [ T.i : i in [1..Ngens (T)] ] >;    
  T1g`Star := star1g;
  T2 := sub < Generic (T) | [ T.i : i in [1..Ngens (T)] ] >;   
  T2`Star := star2;
  
  // retrieve the classical forms defining the involutions ... also need exchange case
  
  // just bilinear forms for now ... also need unitary case
  /* 
    ALSO: in the redesign for *-algebras, use data structures 
    that make this information easy to access.
  */ 
  M1g := RModule (T1g);
  dM1g := RModule (sub < T | [ Transpose (T1g.i @ T1g`Star) : i in [1..Ngens (T1g)] ] >);
  isit, X1g := IsIsomorphic (M1g, dM1g);     assert isit;
  
  M2 := RModule (T2);
  dM2 := RModule (sub < T | [ Transpose (T2.i @ T2`Star) : i in [1..Ngens (T2)] ] >);
  isit, X2 := IsIsomorphic (M2, dM2);     assert isit;
  
  // compare the forms X1g and X2
  if X1g + Transpose (X1g) eq 0 then
       if X2 + Transpose (X2) eq 0 then
            C1 := TransformForm (X1g, "symplectic");
            C2 := TransformForm (X2, "symplectic");
            H := C1 * C2^-1;
                   // sanity check: H takes one form to the other
                   assert H^-1 * X1g * Transpose (H^-1) eq X2;
            HH := GL (Degree (T), BaseRing (T))!H;
                   // sanity check HH respects to *'s on T1g and T2
                   assert forall { i : i in [1..Ngens (T1g)] | 
                                   (T1g.i @ T1g`Star) ^ HH eq (T1g.i ^ HH) @ T2`Star };

       else
            assert X2 eq Transpose (X2);
            return false, _;
       end if;
  else
       assert X1g eq Transpose (X1g);
       if X2 eq Transpose (X2) then
       
       else
            assert X2 + Transpose (X2) eq 0;
            return false, _;
       end if;
  end if;
  
  h := Parent (g)!(H @ TtoS2);
  
         // sanity check : h normalizes S2 and respects the *'s on S1g and S2
         assert S2^h eq S2;
         assert forall { i : i in [1..Ngens (S1g)] |
                             (S1g.i @ S1g`Star) ^ h eq (S1g.i ^ h) @ S2`Star };
                             
  g := g * h;
  
  // final sanity check: g conjugates S1 to S2 and respects the *'s on these algebras
  assert S1^g eq S2;
  assert forall { i : i in [1..Ngens (S1)] | (S1.i @ S1`Star) ^ g eq (S1.i ^ g) @ S2`Star };
  
return g;
     
end function;


