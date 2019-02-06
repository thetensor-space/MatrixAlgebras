/* functions to compute normalizers of associative matrix algebras */

import "../utility.m" : __AnnihilatesModule, __IsBlockDiagonalMatrix;
import "conjugacy.m" : __PreprocessSemisimple;

__galois_generator_irred := function (J)
     MA := Generic (Parent (J));
     q := #BaseRing (MA);
     M := RModule (sub < MA | J >);
     Mq := RModule (sub < MA | J^q >);
     isit, gamma := IsIsomorphic (M, Mq);
     assert isit;
     e := Degree (MinimalPolynomial (J));
     assert exists (l){ a : a in BaseRing (MA) | a ne 0 and Order (a*gamma) eq e };
return l * gamma;
end function;


__AutosOfSimpleAssoc := function (A)
     k := BaseRing (A);
     d := Degree (A);
       // decompose the natural <A>-module
     M := RModule (A);
     ind := IndecomposableSummands (M);
       // diagonally embed isomorphisms
     e := Dimension (ind[1]);
     isos := < Identity (MatrixAlgebra (k, e)) >;
     for j in [2..#ind] do
         isit, iso := IsIsomorphic (ind[j], ind[1]);
         assert isit;
	     Append (~isos, iso^-1);
     end for;
     basis := &cat [ Basis (ind[i]) : i in [1..#ind] ];
     C := DiagonalJoin (isos) * Matrix (basis);
     B := sub < Generic (A) | [ C * A.i * C^-1 : i in [1..Ngens (A)] ] >;
       // write down semilinear group for top left block
     gens := [ ExtractBlock (B.i, 1, 1, e, e) : i in [1..Ngens (B)] ];
     R := sub < MatrixAlgebra (k, e) | gens >;
     isit, Rtimes := UnitGroupOfAlgebra (R);   assert isit;
     gens := [ GL (e, k)!(Rtimes.i) : i in [1..Ngens (Rtimes)] ];
     X := RModule (R);
     assert IsIrreducible (X);
     isit, J, f := IsAbsolutelyIrreducible (X);
     if not isit then  // add in a Galois generator
         gamma := __galois_generator_irred (J);
         Append (~gens, GL (e, k)!gamma);
     end if;
       // embed diagonally 
     GENS := [ DiagonalJoin (< gens[i] : j in [1..d div e] >) : i in [1..#gens] ];
       // conjugate back 
     GENS := [ C^-1 * GENS[i] * C : i in [1..#GENS] ];       
     H := sub < GL (d, k) | GENS >; 
         // sanity check 
         assert forall { i : i in [1..Ngens (H)] | A ^ (H.i) eq A };    
return sub < GL (d, k) | GENS >; 
end function;



/* 
  INPUT: a subalgebra, A, of the full matrix algebra M(V), dim(V) = n
     (optional: a partition of [1..n] to indicate that A is actually
      a subalgebra of M(U_1) x ... x M(U_m) in block diagonal form.)
  OUTPUT: the subgroup N(A) of GL(V) of elements normalizing A.
     (optional: the subgroup of GL(U_1) x ... x GL(U_m) normalizing A.)
  REMARK: for the time being this assumes A is semisimple; if we need to 
      stabilize a radical, we can try this externally.
*/

intrinsic GLNormalizer (A::AlgMat : PARTITION := [ ]) -> GrpMat
  { Returns the group of invertible matrices normalizing the matrix algebra A. }
  
  require Identity (Generic (A)) in A : "A must be a unital ring";
  
  require IsSemisimple (A) : 
     "at present the function works only for semisimple algebras";
  
  k := BaseRing (A);
  n := Degree (A);
  G := GL (n, k);
  V := VectorSpace (k, n);
  
  if #PARTITION eq 0 then
      PARTITION := [ n ];
  end if;
  
  require (n eq &+ PARTITION) : "the specified partition is incompatible with the degree of A";
  
  require forall { i : i in [1..Ngens (A)] | __IsBlockDiagonalMatrix (Matrix (A.i), PARTITION) } :
     "the specified partition is incompatible with the block structure of A";
     
  // deal with trivial case
  if Dimension (A) eq 1 then     /// A consists of just scalar matrices
       H := GL (PARTITION[1], k);
       for i in [2..#PARTITION] do
            H := DirectProduct (H, GL (PARTITION[i], k));
       end for;
       return H;
  end if;
     
  // compute the restrictions of A to the blocks determined by PARTITION,  
  // and the subgroup centralizing A within GL(U1) x ... x GL(Ut)
  BLOCKS := [ ];
  CENTS := [ ];
  MPART := [ ];
  pos := 1;
  for i in [1..#PARTITION] do
      m := PARTITION[i];
      Append (~MPART, sub < V | [ V.j : j in [pos..m-1+pos] ] >);
      gens := [ ExtractBlock (Matrix (A.j), pos, pos, m, m) : j in [1..Ngens (A)] ];
      Ai := sub < MatrixAlgebra (k, m) | gens >;
      Append (~BLOCKS, Ai); 
      Mi := RModule (Ai);
      CentMi := EndomorphismAlgebra (Mi);
      isit, Ci := UnitGroupOfAlgebra (CentMi);     assert isit;
      Append (~CENTS, Ci);
      pos +:= m;
  end for;
  H := DirectProduct (CENTS);
  assert forall { i : i in [1..Ngens (A)] |
                      forall { j : j in [1..Ngens (H)] | (A.i) ^ (H.j) eq A.i } };
  vprint MatrixAlgebras, 2 : "built the group centralizing A";
  
  // get the structural information about A
  MIC, C, type, pos, INTS := __PreprocessSemisimple (A : PART := PARTITION);
  vprint MatrixAlgebras, 2 :  "semisimple type of A", type;

  // compute the automorphisms of minimal ideals
  aut_gens :=  [ ];
  SIMPLES := [ ];
  for s in [1..#MIC] do
       ds := &* type[s];
       Js := sub < MatrixAlgebra (k, ds) | 
                     [ ExtractBlock ((MIC[s]).j, pos[s], pos[s], ds, ds) :
                         j in [1..Ngens (MIC[s])] ] 
                 >;
       assert IsSimple (Js);
       Append (~SIMPLES, Js);
       Us := __AutosOfSimpleAssoc (Js);
       aut_gens cat:= [ InsertBlock (Identity (G), Us.j, pos[s], pos[s]) : 
                                                     j in [1..Ngens (Us)] ];
  end for;
  vprint MatrixAlgebras, 2 : "lifted the automorphisms of the minimal ideals";
  //AC := sub < Generic (A) | [ C * A.i * C^-1 : i in [1..Ngens (A)] ] >;
  //assert forall { g : g in aut_gens | AC ^ (GL (Nrows (g), k)!g) eq AC };
  
  // construct the group permuting the terms in each isotypic component
  perm_gens := [ ];
  ID := Identity (MatrixAlgebra (k, n));
  ISOTYPICS := { 
     { j : j in [1..#SIMPLES] | (type[i] eq type[j]) and (INTS[i] eq INTS[j]) } :
           i in [1..#SIMPLES] };
  vprint MatrixAlgebras, 2 : "ISOTYPICS", ISOTYPICS;
  for SI in ISOTYPICS do
       LI := [ i : i in SI ];
       for i in [1..#LI-1] do
            for j in [i+1..#LI] do
                 I := SIMPLES[LI[i]];
                 J := SIMPLES[LI[j]];
                 // interchange ideals I and J
                 isit, g := IsConjugate (I, J);   assert isit;
                 h := ID;
                 InsertBlock (~h, MatrixAlgebra (k, Degree (I))!0, pos[LI[i]], pos[LI[i]]);
                 InsertBlock (~h, MatrixAlgebra (k, Degree (I))!0, pos[LI[j]], pos[LI[j]]);
                 InsertBlock (~h, g, pos[LI[i]], pos[LI[j]]);
                 InsertBlock (~h, g^-1, pos[LI[j]], pos[LI[i]]);
                 Append (~perm_gens, h);
            end for;
       end for;
  end for;
  //assert forall { g : g in perm_gens | AC ^ (GL (Nrows (g), k)!g) eq AC };
  vprint MatrixAlgebras, 2 : "built the group permuting the terms of the isotypic components";
   
  // add in conjugated automorphism and permutation gens
  aut_gens := [ C^-1 * aut_gens[i] * C : i in [1..#aut_gens] ];
  perm_gens := [ C^-1 * perm_gens[i] * C : i in [1..#perm_gens] ];
  
  H := sub < G | H , aut_gens , perm_gens >;  
  
  // final sanity check
  assert forall { i : i in [1..Ngens (H)] | A ^ (H.i) eq A };  
  
return H;

end intrinsic;


