/* some functions to test the IsConjugate function for Lie algebras */
load "~/MagmaPackages/MatrixLie/examples/constructions.m";

/* Explore conjugacy of irreducible tensor product representations. */
ExperimentA := function (k, type1, type2, nruns)
  L1 := MatrixLieAlgebra (type1, k);
  L2 := MatrixLieAlgebra (type2, k);
  L := MyTensorProduct (L1, L2);  
  "testing", nruns, "instances of conjugacy of the entire tensor product...";
  bad1 := [ ];
  for i in [1..nruns] do
       g := Random (GL (Degree (L), k));
       Lg := sub < Generic (L) | [ g * Matrix (L.i) * g^-1 : i in [1..Ngens (L)] ] >;
       isit := IsConjugate (L, Lg);
       if not isit then
            Append (~bad1, [L, Lg]);
       end if;
  end for;
  "...and found that", #bad1, "are not conjugate";
  "   ";
  "testing", nruns, "instances of conjugacy of a single tensor factor";
  bad2 := [ ];
  for i in [1..nruns] do
       h := Random (GL (Degree (L1), k));
       L1h := sub < Generic (L1) | [ h * Matrix (L1.i) * h^-1 : i in [1..Ngens (L1)] ] >;
       Lh := MyTensorProduct (L1h, L2);
       isit := IsConjugate (L, Lh);
       Append (~bad2, [L, Lh]);
  end for;
  "...and found that", #bad2, "are not conjugate";
return bad1, bad2;
end function;

/* 
  Explore conjugacy of semisimples that are represented "simply" on their
  summands as standard or adjoint modules. Input is:
  (1) a field k;
  and for each semisimple Lie algebra,
  (2) a list of simple types;
  (3) a list of pairs [m,n] indicating the minimal ideal corresponding to the
      pair should be embedded as m copies of the standard modules plus n copies
      of the adjoint module.
  If the simple types and representation types of the two Lie algebras coincide,
  they should be conjugate; if they do not, then they will not be conjugate.
*/
ExperimentB := function (k, stypes1, rtypes1, stypes2, rtypes2)
  L1 := MySemisimpleMatrixLieAlgebra (k, stypes1, rtypes1 : SCRAMBLE := true);
  L2 := MySemisimpleMatrixLieAlgebra (k, stypes2, rtypes2 : SCRAMBLE := true);
  isit, C := IsConjugate (L1, L2);
  if isit then   // final sanity check
     assert L2 eq sub < Generic (L1) | [ C * Matrix (L1.i) * C^-1 : i in [1..Ngens (L1)] ] >;
  end if;
return isit;
end function;