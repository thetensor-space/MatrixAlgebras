/* functions to decide conjugacy of matrix *-algebras */

// REFER BACK TO "conjugacy.m" in Assoc, and mimic the general structure

             
/*
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
     
end function;


