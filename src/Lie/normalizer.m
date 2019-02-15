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
                   [ ExtractBlock (JC.j, pos, pos, ni, ni) : j in [1..Ngens (J)] ] >;
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
     
     // sanity checks
     assert JC ^ delta eq JC;
     assert forall { g : g in GAMMA | JC ^ (GL(Nrows(g),k)!g) eq JC };
     
     // conjugate back
     gens := [ delta ] cat 
             [ gamma : gamma in GAMMA | gamma ne Identity (MatrixAlgebra (k, n)) ];
     gens := [ C^-1 * gens[i] * C : i in [1..#gens] ];
     
     // assign the order of H
     H := sub < GL (n, k) | [ GL (n, k)!x : x in gens ] >;
     order := FactoredOrder (H);

return H;
end function;


/* 
Used the same name as the function created (presumably) by Colva for groups.
  INPUT: a subalgebra, L, of the matrix Lie algebra gl(V), dim(V) = n
     (optional: a partition of [1..n] to indicate that L is actually
      a subalgebra of gl(U_1) x ... x gl(U_m) in block diagonal form.)
  OUTPUT: the subgroup N(L) of GL(V) of elements normalizing L.
     (optional: the subgroup of GL(U_1) x ... x GL(U_m) normalizing L.)
     
  The "SANITY" and "ORDER" flags are temporary, while we figure out the correct
  order formulae for the various components, and the orders of their intersections.
*/
intrinsic GLNormalizer (L::AlgMatLie : PARTITION := [ ], SANITY := false, ORDER := false) 
          -> GrpMat
  { Returns the group of invertible matrices normalizing the matrix Lie algebra L. }
  
  flag, LL := HasLeviSubalgebra (L);
  vprint MatrixAlgebras, 1 : "verified that L is its own Levi subalgebra";
  require (flag and (L eq LL)) : 
     "at present the function works only for semisimple Lie algebras";
   
  k := BaseRing (L); 
  n := Degree (L);
  
  if #PARTITION eq 0 then
      PARTITION := [ n ];
  end if;
     
  // trivial case
  if Dimension (L) eq 0 then    // everything normalizes L
       NORM := GL (PARTITION[1], k); 
       for i in [2..#PARTITION] do
            NORM := DirectProduct (NORM, GL (PARTITION[i], k));
       end for;
       return NORM;
  end if;
  
  G := GL (n, k);
  V := VectorSpace (k, n);
    
  require (n eq &+ PARTITION) : "the specified partition is incompatible with the degree of L";
  
  require forall { i : i in [1..Ngens (L)] | __IsBlockDiagonalMatrix (Matrix (L.i), PARTITION) } :
     "the specified partition is incompatible with the block structure of L";
     
  // find a Chevalley basis for L and use it to exponentiate
  E, F := ChevalleyBasis (L);
  vprint MatrixAlgebras, 1 : "found a Chevalley basis for L";
  EXP := sub < G | [ Exponentiate (z) : z in E cat F ] >;
  
  // compute the restrictions of L to the blocks determined by PARTITION,  
  // and the subgroup centralizing L within GL(U1) x ... x GL(Ut)
  CENTS := [ ];
  SCALS := [ ];
  MPART := [* *];
  pos := 1;
  for i in [1..#PARTITION] do
      m := PARTITION[i];
      Vi := sub < V | [ V.j : j in [pos..m-1+pos] ] >;
      Append (~MPART, Vi);
      gens := [ ExtractBlock (Matrix (L.j), pos, pos, m, m) : j in [1..Ngens (L)] ];
      Li := sub < MatrixLieAlgebra (k, m) | gens >;
      Mi := RModule (Li);
      CentMi := EndomorphismAlgebra (Mi);  
      isit, Ci := UnitGroupOfAlgebra (CentMi);   assert isit;
      ScalMi := CentreOfEndomorphismAlgebra (Mi);
      isit, SCALi := UnitGroupOfAlgebra (ScalMi);   assert isit;
      Append (~SCALS, SCALi);
      Append (~CENTS, Ci);
      pos +:= m;
  end for;
  CENT := DirectProduct (CENTS);
  SCAL := DirectProduct (SCALS);
  // compulsory sanity check 1
  assert forall { i : i in [1..Ngens (CENT)] | 
                      forall { j : j in [1..Ngens (L)] | L.j ^ CENT.i eq L.j } };
  
           // remove eventually
           if ORDER then
             CENT_ORDER := &* [ FactoredOrder (CENTS[i]) : i in [1..#CENTS] ];
             ttt := Cputime ();
             SCAL := LMGMeet (G, SCAL, EXP);
             SCAL_ORDER := FactoredOrder (SCAL);
             vprint MatrixAlgebras, 2 : "time to intersect full scalars with exponentiated group",
             Cputime (ttt);
             // optional SANITY check 1
             if SANITY then
                  INT := LMGMeet (G, EXP, CENT);
                  flag := LMGEqual (INT, SCAL);
                  vprint MatrixAlgebras, 2 : "   [SANITY CHECK 1]", flag;
             end if;
           end if;
  
  // get the minimal ideals of L and make sure they act "simply" on V     
  MI := IndecomposableSummands (L);
  indV := [ sub < V | [ V.i * (J.j) : i in [1..n], j in [1..Ngens (J)] ] > : J in MI ];
  V0 := &meet [ Nullspace (Matrix (L.i)) : i in [1..Ngens (L)] ];

  if #MI gt 1 then

/*
      require forall { s : s in [1..#MI] |
            __AnnihilatesModule (MI[s], &+ [indV[t] : t in [1..#indV] | s ne t ]) } :
"all L-module summands must be irreducible J-modules for some minimal ideal J of L (only in this restricted setting do the current methods work)";
*/

// PAB inserted the following on Feb 15, 2019 at request of EAO to permit continuous testing
if not forall { s : s in [1..#MI] |
            __AnnihilatesModule (MI[s], &+ [indV[t] : t in [1..#indV] | s ne t ]) } then
vprint MatrixAlgebras, 2 : "not all L-summands are irreducible J-modules for some minimal ideal";
return false;

end if;

  end if;
  IDIMS := [ [ Dimension (indV[i] meet MPART[j]) : j in [1..#MPART] ] : i in [1..#indV] ];
  // compulsory sanity check 2
  assert forall { i : i in [1..#indV] | Dimension (indV[i]) eq &+ IDIMS[i] };
  
  // put L into block diagonal form corresponding to the minimal ideals                    
  degs := [ Dimension (indV[i]) : i in [1..#indV] ];
  C := Matrix ((&cat [ Basis (indV[i]) : i in [1..#indV] ]) cat Basis (V0));
  LC := sub < Generic (L) | [ C * Matrix (L.i) * C^-1 : i in [1..Ngens (L)] ] >;
  MIC := [ sub < Generic (J) | [ C * Matrix (J.i) *C^-1 : i in [1..Ngens (J)] ] > :
                     J in MI ];
  EC := [ C * Matrix (E[i]) * C^-1 : i in [1..#E] ];
  FC := [ C * Matrix (F[i]) * C^-1 : i in [1..#F] ];
  
  // extract the blocks and construct the lifts of the outer automorphisms on each block
  aut_gens := [ ];
  ISOTYPICS := [* *];
  SIMPLES := [ ];
  POSITIONS := [ ];
              // remove eventually
              if ORDER then
                HAS_ORDER := true;
                OUT_ORDER := Factorization (1);
                EXP_ORDER := Factorization (1);
              end if;
  pos := 1;
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
 
             // remove eventually: update the order of EXP
             if ORDER then
               if Characteristic (k) gt LieRank then  // we know the order of the exponentiated part
                    EXP_ORDER *:= FactoredOrder (GroupOfLieType (t, k));
               else
                    HAS_ORDER := false;
               end if;
             end if;
       
       ECs := [ ExtractBlock (EC[j], pos, pos, degs[s], degs[s]) : j in [1..#EC] ];
       FCs := [ ExtractBlock (FC[j], pos, pos, degs[s], degs[s]) : j in [1..#FC] ];
       ECs := [ e : e in ECs | e ne 0 ];
       FCs := [ f : f in FCs | f ne 0 ];
       OUTs := __AutosOfSimpleLie (Js, [ECs[i] : i in [1..LieRank]], [FCs[i] : 
                            i in [1..LieRank]]);
                            
              // remove eventually
              if ORDER then
                OUT_ORDER *:= FactoredOrder (OUTs);
              end if;
              
       aut_gens cat:= [ InsertBlock (Identity (G), OUTs.j, pos, pos) : 
                                                     j in [1..Ngens (OUTs)] ];
       pos +:= degs[s];
       
  end for;
  
  NORM := sub < G | EXP , CENT >;
  
             // remove eventually
             if ORDER then
               if HAS_ORDER then
                    EXP`FactoredOrder := EXP_ORDER; 
       
                    // optional SANITY check 2
                    if SANITY then
                         vprint MatrixAlgebras, 2 : "   [SANITY CHECK 2]", 
                         FactoredOrder (NORM) eq EXP_ORDER * CENT_ORDER / SCAL_ORDER;
                    end if;
       
                    // optional SANITY check 3
                    if SANITY then
                         AUT := sub < G | [ C^-1 * aut_gens[i] * C : i in [1..#aut_gens] ] >;
                         IAN := LMGMeet (G, AUT, NORM);
                         vprint MatrixAlgebras, 2 : "    [SANITY CHECK 3]", 
                         FactoredOrder (IAN);
                    end if;
       
                end if;
              end if;
  
  assert forall { g : g in aut_gens | LC ^ (GL (Nrows (g), k)!g) eq LC }; 
  vprint MatrixAlgebras, 2 : "    isotypic component data:", ISOTYPICS;
  
  // compute the group permuting the isotypic components
  perm_gens := [ ];
  PERM_ORDER := Factorization (1);
  ID := Identity (MatrixAlgebra (k, n));
  for s in [1..#ISOTYPICS] do
       S := ISOTYPICS[s][3];   // the simples to be permuted
       if #S gt 1 then
           SYM_GENS := [ ];    // related to ORDER computation only
           perm_gens := [ ];
           for i in [1..#S-1] do
               for j in [i+1..#S] do
                   // try to interchange simples S[i] and S[j]
                   I := SIMPLES[S[i]];
                   J := SIMPLES[S[j]];
                   isit, g := IsConjugate (I, J);
                   if isit then
                       Append (~SYM_GENS, SymmetricGroup (#S)!(i,j));
                       h := ID;
                       InsertBlock (~h, MatrixAlgebra (k, degs[S[i]])!0, POSITIONS[S[i]], POSITIONS[S[i]]);
                       InsertBlock (~h, MatrixAlgebra (k, degs[S[j]])!0, POSITIONS[S[j]], POSITIONS[S[j]]);
                       InsertBlock (~h, g^-1, POSITIONS[S[i]], POSITIONS[S[j]]);
                       InsertBlock (~h, g, POSITIONS[S[j]], POSITIONS[S[i]]);
                       Append (~perm_gens, h);
                   end if;
               end for;
           end for;
                     
                     // remove eventually
                     if ORDER then
                       PERM_s := sub < SymmetricGroup (#S) | SYM_GENS >;
                       PERM_ORDER *:= FactoredOrder (PERM_s);  
                     end if;
                            
       end if;
  end for;
  
  assert forall { g : g in perm_gens | LC ^ (GL (Nrows (g), k)!g) eq LC };
  
  NORM := sub < G | NORM , 
                    [ C^-1 * aut_gens[i] * C : i in [1..#aut_gens] ] , 
                    [ C^-1 * perm_gens[i] * C : i in [1..#perm_gens] ]
              >;
  
            // remove eventually
            if ORDER then
                 if HAS_ORDER then
                    NORM`FactoredOrder := CENT_ORDER * EXP_ORDER * OUT_ORDER * PERM_ORDER / SCAL_ORDER;
                    vprint MatrixAlgebras, 2 : "storing factored order";
                 else
                    vprint MatrixAlgebras, 2 : "could not store factored order";
                 end if;
                 // optional SANITY check 4
                 if SANITY then
                    H := sub < G | NORM >;
                    assert not assigned H`FactoredOrder;
                    vprint MatrixAlgebras, 2 : "   [SANITY CHECK 4]", 
                          IntegerRing ()!FactoredOrder (NORM) eq LMGOrder (H);
                    vprint MatrixAlgebras, 2 : "   |NORM| =", FactoredOrder (NORM);
                    vprint MatrixAlgebras, 2 : "   |H| =", FactoredOrder (H);
                 end if;
             end if;

  // final compulsory sanity check
  assert forall { i : i in [1..Ngens (NORM)] | L ^ NORM.i eq L };  
  
return NORM;

end intrinsic;



