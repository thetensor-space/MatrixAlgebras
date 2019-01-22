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

k := GF (11);
nruns := 10;
ST1 := [ "A1" , "A1" ];  RT1 := [ [2,0] , [1,0] ];
ST2 := [ "A1" , "A1" ];  RT2 := [ [1,0] , [2,0] ];
"testing", nruns, "instances of semisimple conjugacy with simple actions";
flags := [ ];
for i in [1..nruns] do
  "i =", i;
  L1 := MySemisimpleMatrixLieAlgebra (k, ST1, RT1 : SCRAMBLE := true);
  L2 := MySemisimpleMatrixLieAlgebra (k, ST2, RT2 : SCRAMBLE := true);
  isit, C := IsConjugate (L1, L2);
  if isit then   // final sanity check
     assert L2 eq sub < Generic (L1) | [ C * Matrix (L1.i) * C^-1 : i in [1..Ngens (L1)] ] >;
  end if;
  Append (~flags, isit);
end for;
Set (flags);

// NOTE: Magma often spins its wheels on ChevalleyBasis calls.




