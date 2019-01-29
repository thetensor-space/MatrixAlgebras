/* functions to compute normalizers of matrix *-algebras */

import "../utility.m" : __AnnihilatesModule,  __IsBlockDiagonalMatrix;

/* returns generators for the lift of Out(J) to GL(V) when J < gl(V) is simple. */
__AutosOfSimpleLie := function (J, E, F)

     assert IsSimple (J);
     k := BaseRing (J);
     n := Degree (J);
     t := SemisimpleType (J);
     LieType := t[1];
     LieRank := StringToInteger (&cat [t[i] : i in [2..#t]]);
     assert (#E eq LieRank) and (#F eq LieRank);
     
     // decompose the J-module
     M := RModule (J);
     indM := IndecomposableSummands (M);
     dims := [ Dimension (S) : S in indM ];
     assert n eq &+ dims;
     X := VectorSpace (k, n);
     indX := [ sub < X | [ Vector (M!(S.i)) : i in [1..Dimension (S)] ] > : S in indM ];
     assert forall { U : U in indX | not __AnnihilatesModule (J, U) };
     C := Matrix (&cat [ Basis (U) : U in indX ]);
     JC := sub < MatrixLieAlgebra (k, n) | 
                  [ C * Matrix (J.i) * C^-1 : i in [1..Ngens (J)] ] >;
     EC := [ C * Matrix (E[i]) * C^-1 : i in [1..LieRank] ];
     FC := [ C * Matrix (F[i]) * C^-1 : i in [1..LieRank] ];
     
     pos := 1;
     S := [ PrimitiveElement (k) ] cat [ k!1  : i in [1..LieRank] ];
     delta := Identity (MatrixAlgebra (k, n));  // diagonal auto
     GA := [ ];
     if (LieType eq "A") and (LieRank ge 2) then
          Append (~GA, Sym (LieRank)![LieRank + 1 - i : i in [1..LieRank] ]);
     elif (LieType eq "D") then
          Append (~GA, Sym (LieRank)!(LieRank-1,LieRank));
          if (LieRank eq 4) then
               Append (~GA, Sym (4)!(1,3,4));
          end if;
     end if;
     
     if #GA gt 0 then
          GA := sub < Sym (LieRank) | GA >;
          GA := [ pi : pi in GA | pi ne Identity (GA) ];
          GAMMA := [ Identity (MatrixAlgebra (k, n)) : j in [1..#GA] ];  // graph autos
     else
          GAMMA := [ ];
     end if;
  
     for i in [1..#indX] do 
            
          ni := dims[i];
          Ji := sub < MatrixLieAlgebra (k, ni) | 
                       [ ExtractBlock (J.j, pos, pos, ni, ni) : j in [1..Ngens (J)] ] >;
          ECi := [ Ji!ExtractBlock (EC[j], pos, pos, ni, ni) : j in [1..LieRank] ];
          FCi := [ Ji!ExtractBlock (FC[j], pos, pos, ni, ni) : j in [1..LieRank] ];
          
          Ci, Ai := CrystalBasis (Ji : E := ECi, F := FCi);  
          
          // lift diagonal auto 
          D0 := [ k!1 ];
          for a in [2..#Ai] do
              word := Ai[a][2];  // the word labelling the i-th node 
              Append (~D0, &*[ S[word[j]] / S[1+word[j]] : j in [1..#word] ]);
          end for;
          D0 := DiagonalMatrix (D0);
          Di := GL (Nrows (D0), k)!(Ci^-1 * D0 * Ci);
          assert Ji ^ Di eq Ji;   // sanity check
          InsertBlock (~delta, Di, pos, pos);
          delta := GL (Nrows (delta), k)!delta;
          
          // try to lift remaining graph automorphisms
          Bi := [ Vector (Ci[a]) : a in [1..Nrows (Ci)] ];
          Vi := VectorSpaceWithBasis (Bi);
          assert #GA eq #GAMMA;
          NGA := [ ]; NGAMMA := [ ];
          for j in [1..#GA] do
               g0 := [ ];
               for a in [1..#Ai] do
                   word := Ai[a][2];
                   gword := [ word[c]^(GA[j]) : c in [1..#word] ];           
                   vec := Vi.1;
                   for b in [1..#gword] do  
                       vec := vec * FCi[gword[b]];
                   end for;
                   Append (~g0, Coordinates (Vi, vec));
               end for;
               g0 := Matrix (g0);
               if Rank (g0) eq Rank (Ci) then
                   g := GL (Nrows (g0), k)!(Ci^-1 * g0 * Ci);
                   if Ji ^ g eq Ji then
                       InsertBlock (~GAMMA[j], g, pos, pos);
                       Append (~NGAMMA, GAMMA[j]);
                       Append (~NGA, GA[j]);
                   end if;
               end if;
          end for; 
          GA := NGA;
          GAMMA := NGAMMA;   
          
          pos +:= ni;
          
     end for;
     assert JC ^ delta eq JC;
     assert forall { g : g in GAMMA | JC ^ (GL(Degree(g),k)!g) eq JC };
     
     gens := [ delta ] cat 
             [ gamma : gamma in GAMMA | gamma ne Identity (MatrixAlgebra (k, n)) ];
     gens := [ C^-1 * gens[i] * C : i in [1..#gens] ];
     H := sub < GL (n, k) | [ GL (n, k)!x : x in gens ] >;

return H;
end function;


/* 
Used the same name as the function created (presumably) by Colva for groups.
  INPUT: a subalgebra, L, of the matrix Lie algebra gl(V), dim(V) = n
     (optional: a partition of [1..n] to indicate that L is actually
      a subalgebra of gl(U_1) x ... x gl(U_m) in block diagonal form.)
  OUTPUT: the subgroup N(L) of GL(V) of elements normalizing L.
     (optional: the subgroup of GL(U_1) x ... x GL(U_m) normalizing L.)
*/
intrinsic GLNormalizer (L::AlgMatLie : PARTITION := [ ]) -> GrpMat
  { Returns the group of invertible matrices normalizing the matrix Lie algebra L. }
  
  flag, LL := HasLeviSubalgebra (L);
  require (flag and (L eq LL)) : 
     "at present the function works only for semisimple Lie algebras";
  
  k := BaseRing (L);
  n := Degree (L);
  G := GL (n, k);
  V := VectorSpace (k, n);
  
  if #PARTITION eq 0 then
      PARTITION := [ n ];
  end if;
  vprint MatrixAlgebras, 1 : "  [ GLNormalizer : PARTITION =", PARTITION, "]";
  
  require (n eq &+ PARTITION) : "the specified partition is incompatible with the degree of L";
  
  require forall { i : i in [1..Ngens (L)] | __IsBlockDiagonalMatrix (Matrix (L.i), PARTITION) } :
     "the specified partition is incompatible with the block structure of L";
     
  // find a Chevalley basis for L and use it to exponentiate
  E, F := ChevalleyBasis (L);
  H := sub < G | [ Exponentiate (z) : z in E cat F ] >;
  vprint MatrixAlgebras, 1 : "  [ GLNormalizer: exponential subgroup has order", #H,"]";
  vprint MatrixAlgebras, 2 : CompositionFactors (H); 
  
  // compute the restrictions of L to the blocks determined by PARTITION,  
  // and the subgroup centralizing L within GL(U1) x ... x GL(Ut)
//  BLOCKS := [ ];
  CENTS := [ ];
  MPART := [ ];
  pos := 1;
  for i in [1..#PARTITION] do
      m := PARTITION[i];
      Append (~MPART, sub < V | [ V.j : j in [pos..m-1+pos] ] >);
      gens := [ ExtractBlock (Matrix (L.j), pos, pos, m, m) : j in [1..Ngens (L)] ];
      Li := sub < MatrixLieAlgebra (k, m) | gens >;
//      Append (~BLOCKS, Li); 
      Mi := RModule (Li);
      CentMi := EndomorphismAlgebra (Mi);
      Ci := MyUnitGroup (CentMi);
      Append (~CENTS, Ci);
      pos +:= m;
  end for;
  C := DirectProduct (CENTS);
  assert forall { i : i in [1..Ngens (C)] | 
                      forall { j : j in [1..Ngens (L)] | L.j ^ C.i eq L.j } };
  ord := #H;
  H := sub < G | H , C >;
  vprint MatrixAlgebras, 1 : "  [ GLNormalizer: centralizer / exponential has order", #H div ord, "]";
  vprint MatrixAlgebras, 2 : CompositionFactors (H);
  
  // get the minimal ideals of L and make sure they act "simply" on V     
  MI := IndecomposableSummands (L);
  indV := [ sub < V | [ V.i * (J.j) : i in [1..n], j in [1..Ngens (J)] ] > : J in MI ];
V0 := &meet [ Nullspace (Matrix (L.i)) : i in [1..Ngens (L)] ];
  if #MI gt 1 then
      require forall { s : s in [1..#MI] |
            __AnnihilatesModule (MI[s], &+ [indV[t] : t in [1..#indV] | s ne t ]) } :
"not all summands of L are irreducible J-modules for some minimal ideal J of L";
  end if;
  IDIMS := [ [ Dimension (indV[i] meet MPART[j]) : j in [1..#MPART] ] : i in [1..#indV] ];
  assert forall { i : i in [1..#indV] | Dimension (indV[i]) eq &+ IDIMS[i] };
  vprint MatrixAlgebras, 2 : "    intersection dimensions:", IDIMS;
  
  // put L into block diagonal form corresponding to the minimal ideals                    
  degs := [ Dimension (indV[i]) : i in [1..#indV] ];
C := Matrix ((&cat [ Basis (indV[i]) : i in [1..#indV] ]) cat Basis (V0));
  LC := sub < Generic (L) | [ C * Matrix (L.i) * C^-1 : i in [1..Ngens (L)] ] >;
  MIC := [ sub < Generic (J) | [ C * Matrix (J.i) *C^-1 : i in [1..Ngens (J)] ] > :
                     J in MI ];
  EC := [ C * Matrix (E[i]) * C^-1 : i in [1..#E] ];
  FC := [ C * Matrix (F[i]) * C^-1 : i in [1..#F] ];
  
  // extract the blocks and construct the lifts of the outer automorphisms on each block
  pos := 1;
  aut_gens := [ ];
  ISOTYPICS := [* *];
  SIMPLES := [ ];
  POSITIONS := [ ];
  for s in [1..#MIC] do
       Append (~POSITIONS, pos);
       Js := sub < MatrixLieAlgebra (k, degs[s]) |
            [ ExtractBlock ((MIC[s]).j, pos, pos, degs[s], degs[s]) : 
                          j in [1..Ngens (MIC[s])] ] >;
       assert IsSimple (Js);
       Append (~SIMPLES, Js);
       t := SemisimpleType (Js);
       if s eq 1 then
            Append (~ISOTYPICS, <t, IDIMS[1], [s]>);
       elif exists (i){ j : j in [1..#ISOTYPICS] | 
                   (ISOTYPICS[j][1] eq t) and (ISOTYPICS[j][2] eq IDIMS[s]) } then
            Append (~ISOTYPICS[i][3], s);
       else
            Append (~ISOTYPICS, <t, IDIMS[s], [s]>); 
       end if;                 
       LieRank := StringToInteger (&cat [t[i] : i in [2..#t]]);
       ECs := [ ExtractBlock (EC[j], pos, pos, degs[s], degs[s]) : j in [1..#EC] ];
       FCs := [ ExtractBlock (FC[j], pos, pos, degs[s], degs[s]) : j in [1..#FC] ];
       ECs := [ e : e in ECs | e ne 0 ];
       FCs := [ f : f in FCs | f ne 0 ];
       OUTs := __AutosOfSimpleLie (Js, [ECs[i] : i in [1..LieRank]], [FCs[i] : 
                            i in [1..LieRank]]);
       aut_gens cat:= [ InsertBlock (Identity (G), OUTs.j, pos, pos) : 
                                                     j in [1..Ngens (OUTs)] ];
       pos +:= degs[s];
  end for;
  assert forall { g : g in aut_gens | LC ^ (GL (Nrows (g), k)!g) eq LC }; 
  vprint MatrixAlgebras, 2 : "    isotypic component data:", ISOTYPICS;
  
  perm_gens := [ ];
  ID := Identity (MatrixAlgebra (k, n));
  for s in [1..#ISOTYPICS] do
       S := ISOTYPICS[s][3];   // the simples to be permuted
       if #S gt 1 then
           for i in [1..#S-1] do
               for j in [i+1..#S] do
                   // try to interchange simples S[i] and S[j]
                   I := SIMPLES[S[i]];
                   J := SIMPLES[S[j]];
                   isit, g := IsConjugate (I, J);
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
  assert forall { g : g in perm_gens | LC ^ (GL (Nrows (g), k)!g) eq LC };
  
  // add in conjugated auto gens
  aut_gens := [ C^-1 * aut_gens[i] * C : i in [1..#aut_gens] ];
  ord := #H;
  H := sub < G | aut_gens , H >;  
  vprint MatrixAlgebras, 1 : "  [ GLNormalizer: algebra autos / cent-exp has order", #H div ord, "]";
  vprint MatrixAlgebras, 2 : CompositionFactors (H);
  
  // add in conjugated perm gens
  perm_gens := [ C^-1 * perm_gens[i] * C : i in [1..#perm_gens] ];
  ord := #H;
  H := sub < G | H , perm_gens >;
  vprint MatrixAlgebras, 1 : "  [ GLNormalizer: permutation autos / algebra autos has order", #H div ord;
  vprint MatrixAlgebras, 2 : CompositionFactors (H);
  
  // final sanity check
  assert forall { i : i in [1..Ngens (H)] | L ^ H.i eq L };  
  
return H;

end intrinsic;



