import "utility.m" : MySort;
import "normalizer.m" : __AnnihilatesModule;

/* decides conjugacy between two matrix Lie algebras acting irreducibly on their modules */
__IsConjugate_IRRED := function (J1, E1, F1, J2, E2, F2)  
     assert IsIrreducible (RModule (J1)) and IsIrreducible (RModule (J2));
     C1 := CrystalBasis (J1 : E := E1, F := F1);
     C2 := CrystalBasis (J2 : E := E2, F := F2);
     K1 := sub < Generic (J1) | [ C1 * Matrix (J1.i) * C1^-1 : i in [1..Ngens (J1)] ] >;
     K2 := sub < Generic (J2) | [ C2 * Matrix (J2.i) * C2^-1 : i in [1..Ngens (J2)] ] >;
     C := C1^-1 * C2;
     isit := (K1 eq K2);
     if not isit then
          vprint MatrixLie, 1 : "\t [ __IsC_IRR: crystal bases do not give module similarity ]";
          vprint MatrixLie, 1 : "\t [ __IsC_IRR: C1 =", C1, "]";
          vprint MatrixLie, 1 : "\t [ __IsC_IRR: C2 =", C2, "]"; 
     end if;
     if isit then
          assert J2 eq sub < Generic (J1) | [ C^-1 * Matrix (J1.i) * C : i in [1..Ngens (J1)] ] >;
     end if;
return isit, C; 
end function; 

/*
  Given a semisimple matrix Lie algebra, L, gather data to help determine conjugacy
  with other such Lie algebras, and to construct its normalizer. Specifically:
    * IDEALS is a list of the minimal ideals of L, sorted lexicographically on iso type.
    * TYPES the iso types of the minimal ideals.
    * PARTITION of the minimal ideals into isotypes.
    * SUMMANDS is a list of irreducible L-submodules of the given L-module V.
    * SUPPORTS for each irreducible L-submodule records the ideals that act nontrivially.
*/
__PreprocessSemisimple := function (L)
     k := BaseRing (L);
     d := Degree (L);
     V := VectorSpace (k, d);
     /* first find ideals and sort them */
     tt := Cputime ();
     IDEALS := IndecomposableSummands (L);
     vprint MatrixLie, 1 : "\t [ __PS decomposed L into minimal ideals in time", Cputime (tt), "]";
     n := #IDEALS; S := {1..n};
     Sort (~IDEALS, func<x,y| MySort (SemisimpleType(x),SemisimpleType(y))>);
     TYPES := [ SemisimpleType (IDEALS[i]) : i in [1..n] ];
     /* find isomorphisms classes of minimal ideals and basic permutation group */
     PARTITION := [ ];
     T := S;
     while #T gt 0 do
          assert exists (t){u : u in T};
          tpart := { u : u in T | TYPES[u] eq TYPES[t] };
          T diff:= tpart;
          Append (~PARTITION, tpart);
     end while; 
     PERM := DirectProduct ([ SymmetricGroup (part) : part in PARTITION ]); 
     /* next find the indecomposable summands of V and their supports */
     M := RModule (L);
     tt := Cputime ();
     SUMMANDS := IndecomposableSummands (M);
     vprint MatrixLie, 1 : "\t [ __PS found indecomposable summands of M in time", Cputime (tt), "]";
     m := #SUMMANDS; T := {1..m};
     SUMMANDS := [ sub < V | [ Vector (M!(S.i)) : i in [1..Dimension (S)] ] > : 
                       S in SUMMANDS ];
                             
return IDEALS, TYPES, PARTITION, PERM, SUMMANDS;
end function;


/*
  Given a list of minimal ideals of a semisimple Lie algebra and an
  indecomposable summand U, determine the support of U––those ideals
  represented nontrivially on U.
*/
__SupportOfModule := function (IDEALS, U)
     n := #IDEALS;
     AU := { j : j in [1..n] | __AnnihilatesModule (IDEALS[j], U) };
return {1..n} diff AU;
end function;
            

/*
  INPUT: two subalgebras, L1 and L2, of the matrix Lie algebra gl(V), dim(V) = n
     (optional: a partition of [1..n] to indicate that L1 and L2 are actually
      subalgebras of gl(U_1) x ... x gl(U_m) in block diagonal form.)
  OUTPUT: a boolean indicating whether L1 and L2 are conjugate by an element of GL(V)
      together with a suitable conjugating element.
     (optional: conjugacy is decided within GL(U_1) x ... x GL(U_m))
*/   

intrinsic IsConjugate (L1::AlgMatLie, L2::AlgMatLie : PARTITION := [ ]) ->
                 BoolElt, AlgMatElt
  { True iff L1 and L2 are conjugate in the ambient group of invertible matrices. }
  
  ttt := Cputime ();
  flag, LL1 := HasLeviSubalgebra (L1);
  require (flag and (L1 eq LL1)) : 
     "at present the function works only for semisimple Lie algebras";
     
  flag, LL2 := HasLeviSubalgebra (L2);
  require (flag and (L2 eq LL2)) : 
     "at present the function works only for semisimple Lie algebras";
  vprint MatrixLie, 1 : "  [ IsConjugate: found both Levi subalgebras in time", Cputime (ttt), "]";

  require (Degree (L1) eq Degree (L2)) and #BaseRing (L1) eq #BaseRing (L2) :
     "matrix algebras must have the same degree and be defined over the same finite field";
     
// TO DO: REDUCE TO NONTRIVIAL PART OF DECOMPOSITION INTO  V = V.L + Null(L)
     
  /* must be able to compute a Chevalley basis .. insert try / catch in case we can't? */
  ttt := Cputime ();
  E1, F1 := ChevalleyBasis (L1);
  E2, F2 := ChevalleyBasis (L2);
  vprint MatrixLie, 1 : "  [ IsConjugate: found both Chevalley bases in time", Cputime (ttt), "]";
  
  /* deal with the irreducible case */
  if IsIrreducible (RModule (L1)) and IsIrreducible (RModule (L2)) then
       return __IsConjugate_IRRED (L1, E1, F1, L2, E2, F2);
  end if;
  
  /* next carry out the preprocessing for the conjugacy test */
  ttt := Cputime ();
  ID1, TYPES1, PART1, PERM1, SUMS1 := __PreprocessSemisimple (L1);
  ID2, TYPES2, PART2, PERM2, SUMS2 := __PreprocessSemisimple (L2);
  vprint MatrixLie, 1 : "  [ IsConjugate: summand dimensions of first Lie module are", 
          [ Dimension (U) : U in SUMS1 ], "]";
  vprint MatrixLie, 1 : "  [ IsConjugate: summand dimensions of second Lie module are", 
          [ Dimension (U) : U in SUMS2 ], "]";
  vprint MatrixLie, 1 : "  [ IsConjugate: semisimple preprocessing completed in time", 
          Cputime (ttt), "]";
  
  /* do the quick tests */
  if TYPES1 ne TYPES2 then
       return false, _;
  else
       assert (PART1 eq PART2) and (PERM1 eq PERM2);  // sanity check
  end if;
  
  MLie := Generic (L1);
  k := BaseRing (L1);
  
  m := #SUMS1;
  if #SUMS2 ne m then
       return false, _;
  end if;
  
  /* test each possible ordering of summands in L2 */
  perms := [ pi : pi in PERM1];
  vprint MatrixLie, 1 : "  [ IsConjugate: testing", #perms, "perms of min ideals of second algebra ]";
  conj := false;   // keeps track of whether or not we've found a conjugating matrix
  s := 0;
  while ((s lt #perms) and (not conj)) do
       s +:= 1;
       pi := perms[s];
       good := true;   // keeps track of whether <pi> is giving a feasible
                       // ordering of ideals
       i := 0;
       rem2 := SUMS2;
       BLOCKS := < >;
       newSUMS2 := [* *];
       while ((i lt m) and (good)) do
            i +:= 1;
            U1 := SUMS1[i];
            d1 := Dimension (U1);
            MLieU1 := MatrixLieAlgebra (k, d1);
            L1U1 := sub < MLieU1 |
                    [ RestrictAction (Matrix (L1.a), U1) : a in [1..Ngens (L1)] ] >;
            E1U1 := [ RestrictAction (Matrix(E1[a]), U1) : a in [1..#E1] ];
            // some elements of E1 act trivially on U1 ... discard them
            E1U1 := [ MLieU1!(E1U1[a]) : a in [1..#E1U1] | E1U1[a] ne 0 ];
            F1U1 := [ RestrictAction (Matrix(F1[a]), U1) : a in [1..#F1] ];
            // some elements of F1 act trivially on U1 ... discard them
            F1U1 := [ MLieU1!(F1U1[a]) : a in [1..#F1U1] | F1U1[a] ne 0 ];
            S1 := __SupportOfModule (ID1, U1);
            poss2 := [ b : b in [1..#rem2] | S1 eq __SupportOfModule (ID2, rem2[b])^pi 
                                         and Dimension (rem2[b]) eq d1 ];

            found := false;   // keeps track of whether or not we've found a U2
                              // such that LU1 is conjugate to LU2
            j := 0;
            while ((j lt #poss2) and (not found)) do
                 j +:= 1;
                 U2 := rem2[poss2[j]];
                 d2 := Dimension (U2);
                 MLieU2 := MatrixLieAlgebra (k, d2);
                 L2U2 := sub < MLieU2 |
                         [ RestrictAction (Matrix (L2.a), U2) : a in [1..Ngens (L2)] ] >;
                 E2U2 := [ RestrictAction (Matrix(E2[a]), U2) : a in [1..#E2] ];
                 // some elements of E2 act trivially on U2 ... discard them
                 E2U2 := [ MLieU2!(E2U2[a]) : a in [1..#E2U2] | E2U2[a] ne 0 ];
                 F2U2 := [ RestrictAction (Matrix(F2[a]), U2) : a in [1..#F2] ];
                 // some elements of F2 act trivially on U2 ... discard them
                 F2U2 := [ MLieU2!(F2U2[a]) : a in [1..#F2U2] | F2U2[a] ne 0 ];
                 isit, BC := __IsConjugate_IRRED (L1U1, E1U1, F1U1, L2U2, E2U2, F2U2);
                 if isit then
                      found := true;
                      Remove (~rem2, Position (rem2, U2));
                      Append (~newSUMS2, U2);
                      Append (~BLOCKS, BC);
                 end if;
            end while;
            if (not found) then
                 good := false;
            end if;
       end while;
       if (good) then
            D := DiagonalJoin (BLOCKS);
            C1 := Matrix (&cat [ [ (SUMS1[i]).j : j in [1..Ngens (SUMS1[i])] ] : i in [1..m] ]);
            C2 := Matrix (&cat [ [ (newSUMS2[i]).j : j in [1..Ngens (SUMS2[i])] ] : i in [1..m] ]);
            L1C1 := sub < MLie | 
                     [ C1 * Matrix (L1.i) * C1^-1 : i in [1..Ngens (L1)] ] >;
            L2C2 := sub < MLie | 
                     [ C2 * Matrix (L2.i) * C2^-1 : i in [1..Ngens (L2)] ] >;
            L1C1D := sub < MLie |
                         [ D^-1 * Matrix (L1C1.i) * D : i in [1..Ngens (L1C1)] ] >;
            if L1C1D eq L2C2 then
                 conj := true;
            end if;
       end if;
  end while;

  if (conj) then
       C := C2^-1 * D^-1 * C1;
       assert L2 eq sub < MLie | [ C * Matrix (L1.i) * C^-1 : i in [1..Ngens (L1)] ] >;
       return true, C;   
  else
       return false, _;
  end if; 
  
end intrinsic;
