/*
    INPUT:
      (1) A, a k-algebra (e.g. Lie or associative) of matrices.
      (2) S, a set of invertible linear transformations of the 
          underlying k-algebra.
    
    OUTPUT: true if, and only  if, A^s = A for all s in S.
*/
NORMALIZES_ALGEBRA := function (A, S)  
     k := BaseRing (A);
     n := Degree (A);
     MS := KMatrixSpace (k, n, n);
     X := KMatrixSpaceWithBasis ([ MS!Matrix (x) : x in Basis (A) ]);    
return forall { s : s in S | 
          forall { i : i in [1..Ngens (X)] |
              s^-1 * X.i * s in X
                 }
              };             
end function;


ANNIHILATES := function (J, U)
return forall { i : i in [1..Ngens (J)] | forall { t : t in [1..Ngens (U)] |
          U.t * J.i eq 0 } };
end function;


/* returns generators for the lift of Out(J) to GL(V) when J < gl(V) is simple. */
OUTER_SIMPLE := function (J, E, F)

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
     assert forall { U : U in indX | not ANNIHILATES (J, U) };
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
          Di := Ci^-1 * D0 * Ci;
          assert NORMALIZES_ALGEBRA (Ji, [Di]);  // sanity check
          InsertBlock (~delta, Di, pos, pos);
          
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
                   g := Ci^-1 * GL (Nrows (g0), k)!g0 * Ci;
                   if NORMALIZES_ALGEBRA (Ji, [g]) then
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
     
     assert NORMALIZES_ALGEBRA (JC, [delta]);
     assert NORMALIZES_ALGEBRA (JC, GAMMA);
     
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
  
  // get the minimal ideals of L and make sure they act "simply" on V   
  MI := IndecomposableSummands (L);
  indV := [ sub < V | [ V.i * (J.j) : i in [1..n], j in [1..Ngens (J)] ] > : J in MI ];
  if #MI gt 1 then
      require forall { s : s in [1..#MI] |
            ANNIHILATES (MI[s], &+ [indV[t] : t in [1..#indV] | s ne t ]) } :
"not all irreducible L-modules are irreducible J-modules for some minimal ideal J of L";
  end if;

  // compute the subgroup centralizing L
  ModL := RModule (L);
  CentL := EndomorphismAlgebra (ModL);
  isit, C := UnitGroup (CentL); assert isit;
//"the group, C, centralizing L has order", #C;
  
  // find a Chevalley basis for L and use it to exponentiate
  E, F := ChevalleyBasis (L);
  EXP := sub < G | [ Exponentiate (z) : z in E cat F ] , C >;
//"EXP / C has order", #EXP div #C;
  
  // put L into block diagonal form corresponding to the minimal ideals                    
  degs := [ Dimension (U) : U in indV ];
  C := Matrix (&cat [ Basis (U) : U in indV ]);
  LC := sub < Generic (L) | [ C * Matrix (L.i) * C^-1 : i in [1..Ngens (L)] ] >;
  MIC := [ sub < Generic (J) | [ C * Matrix (J.i) *C^-1 : i in [1..Ngens (J)] ] > :
                     J in MI ];
  EC := [ C * Matrix (E[i]) * C^-1 : i in [1..#E] ];
  FC := [ C * Matrix (F[i]) * C^-1 : i in [1..#F] ];
  
  // extract the blocks and construct the lifts of the outer automorphisms on each block
  pos := 1;
  aut_gens := [ ];
  for s in [1..#MIC] do
       Js := sub < MatrixLieAlgebra (k, degs[s]) |
            [ ExtractBlock ((MIC[s]).j, pos, pos, degs[s], degs[s]) : 
                          j in [1..Ngens (MIC[s])] ] >;
       assert IsSimple (Js);
       t := SemisimpleType (Js);                 
       LieRank := StringToInteger (&cat [t[i] : i in [2..#t]]);
       ECs := [ ExtractBlock (EC[j], pos, pos, degs[s], degs[s]) : j in [1..#EC] ];
       FCs := [ ExtractBlock (FC[j], pos, pos, degs[s], degs[s]) : j in [1..#FC] ];
       ECs := [ e : e in ECs | e ne 0 ];
       FCs := [ f : f in FCs | f ne 0 ];
       OUTs := OUTER_SIMPLE (Js, [ECs[i] : i in [1..LieRank]], [FCs[i] : i in [1..LieRank]]);
       aut_gens cat:= [ InsertBlock (Identity (G), OUTs.j, pos, pos) : 
                                                     j in [1..Ngens (OUTs)] ];
       pos +:= degs[s];
  end for;
  
  aut_gens := [ C^-1 * aut_gens[i] * C : i in [1..#aut_gens] ];
  AUT := sub < G | aut_gens , EXP >;  
//"AUT / EXP has order", #AUT div #EXP;

  // STILL NEED TO INSERT GENERATORS FOR THE GROUP PERMUTING ISOTYPIC COMPONENTS
  
assert NORMALIZES_ALGEBRA (L, [ AUT.i : i in [1..Ngens (AUT)] ]); 
  
return AUT;

end intrinsic;
