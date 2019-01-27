/* functions to compute normalizers of associative matrix algebras */

import "../utility.m" : __AnnihilatesModule;

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
     Rtimes := MyUnitGroup (R);   
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
  
  require IsSemisimple (A) : 
     "at present the function works only for semisimple algebras";
  
  k := BaseRing (A);
  n := Degree (A);
  G := GL (n, k);
  V := VectorSpace (k, n);
  
  if #PARTITION eq 0 then
      PARTITION := [ n ];
  end if;
  vprint MatrixAlgebras, 1 : "  [ GLNormalizer : PARTITION =", PARTITION, "]";
  
  require (n eq &+ PARTITION) : "the specified partition is incompatible with the degree of A";
  
  require forall { i : i in [1..Ngens (A)] | __IsBlockDiagonalMatrix (Matrix (A.i), PARTITION) } :
     "the specified partition is incompatible with the block structure of A";
     
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
      Ci := MyUnitGroup (CentMi);
      Append (~CENTS, Ci);
      pos +:= m;
  end for;
  H := DirectProduct (CENTS);
  assert forall { i : i in [1..Ngens (A)] |
                      forall { j : j in [1..Ngens (H)] | (A.i) ^ (H.j) eq A.i } };
  vprint MatrixAlgebras, 2 : CompositionFactors (H);
  
  // get the minimal ideals of A    
  MI := MinimalIdeals (A);
  indV := [ sub < V | [ V.i * (J.j) : i in [1..n], j in [1..Ngens (J)] ] > : J in MI ];
      // the following is a relic from the Lie algebra function; the condition always holds here
  if #MI gt 1 then
      assert forall { s : s in [1..#MI] |
            __AnnihilatesModule (MI[s], &+ [indV[t] : t in [1..#indV] | s ne t ]) };
  end if;
  IDIMS := [ [ Dimension (indV[i] meet MPART[j]) : j in [1..#MPART] ] : i in [1..#indV] ];
  assert forall { i : i in [1..#indV] | Dimension (indV[i]) eq &+ IDIMS[i] };
  vprint MatrixAlgebras, 2 : "    intersection dimensions:", IDIMS;
  
  // put A into block diagonal form corresponding to the minimal ideals                   
  degs := [ Dimension (indV[i]) : i in [1..#indV] ];
  C := Matrix (&cat [ Basis (indV[i]) : i in [1..#indV] ]);
  AC := sub < Generic (A) | [ C * Matrix (A.i) * C^-1 : i in [1..Ngens (A)] ] >;
  MIC := [ sub < Generic (J) | [ C * Matrix (J.i) *C^-1 : i in [1..Ngens (J)] ] > :
                     J in MI ];
  
  // extract the blocks and construct the unit groups and outer automorphisms on each block
  pos := 1;
  aut_gens := [ ];
  ISOTYPICS := [* *];
  SIMPLES := [ ];
  POSITIONS := [ ];
  for s in [1..#MIC] do
       Append (~POSITIONS, pos);
       Js := sub < MatrixAlgebra (k, degs[s]) |
            [ ExtractBlock ((MIC[s]).j, pos, pos, degs[s], degs[s]) : 
                          j in [1..Ngens (MIC[s])] ] >;
       assert IsSimple (Js);
       Append (~SIMPLES, Js);
       if s eq 1 then
            Append (~ISOTYPICS, <IDIMS[1], [s]>);
       elif exists (i){ j : j in [1..#ISOTYPICS] | 
                         ISOTYPICS[j][1] eq IDIMS[s] } then
            Append (~ISOTYPICS[i][2], s);
       else
            Append (~ISOTYPICS, <IDIMS[s], [s]>); 
       end if;   
       Us := __AutosOfSimpleAssoc (Js);
       aut_gens cat:= [ InsertBlock (Identity (G), Us.j, pos, pos) : 
                                                     j in [1..Ngens (Us)] ];
       pos +:= degs[s];
  end for;
  assert forall { g : g in aut_gens | AC ^ (GL (Nrows (g), k)!g) eq AC };
  vprint MatrixAlgebras, 2 : "    isotypic component data:", ISOTYPICS;
  
  perm_gens := [ ];
  ID := Identity (MatrixAlgebra (k, n));
  for s in [1..#ISOTYPICS] do
       S := ISOTYPICS[s][2];   // the simples to be permuted
       if #S gt 1 then
           for i in [1..#S-1] do
               for j in [i+1..#S] do
                   // try to interchange simples S[i] and S[j]
                   I := SIMPLES[S[i]];
                   J := SIMPLES[S[j]];
                   isit, g := IsConjugate (I, J); // THIS NEEDS TO BE REWRITTEN
                   if isit then
                       h := ID;
                       InsertBlock (~h, MatrixAlgebra (k, degs[S[i]])!0, POSITIONS[S[i]], POSITIONS[S[i]]);
                       InsertBlock (~h, MatrixAlgebra (k, degs[S[j]])!0, POSITIONS[S[j]], POSITIONS[S[j]]);
                       InsertBlock (~h, g^-1, POSITIONS[S[i]], POSITIONS[S[j]]);
                       InsertBlock (~h, g, POSITIONS[S[j]], POSITIONS[S[i]]);
                       Append (~perm_gens, h);
                   end if;
               end for;
           end for;
       end if;
  end for;
  assert forall { g : g in perm_gens | AC ^ (GL (Nrows (g), k)!g) eq AC };
  
  // add in conjugated auto gens
  aut_gens := [ C^-1 * aut_gens[i] * C : i in [1..#aut_gens] ];
  H := sub < G | aut_gens , H >;  
  
  // add in conjugated perm gens
  perm_gens := [ C^-1 * perm_gens[i] * C : i in [1..#perm_gens] ];
  H := sub < G | H , perm_gens >;
  
  // final sanity check
  assert forall { i : i in [1..Ngens (H)] | A ^ (H.i) eq A };  
  
return H;

end intrinsic;


