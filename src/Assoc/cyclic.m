/* functions to decide whether a given associative matrix algebra is cyclic */


/* analogue of "Eltseq" that allows one to specify basis */
__EltseqWithBasis := function (K, k, bas, x)
     assert #bas eq (Degree (K) div Degree (k));
     W, g := VectorSpace (K, k);
     U := VectorSpaceWithBasis ([ bas[i] @ g : i in [1..#bas] ]);
return Coordinates (U, x @ g);
end function;


/* 
  given <T> acting irreducibly on its underlying module, return 
  inverse isomorphisms from k[<T>] to the isomorphic field.
  Also return a generator for Gal(k[<T>]).
*/
__IsomorphismWithField := function (T : SPEC_FIELD := false)
     assert T ne 0;
     /* use min poly of T to build extension */
     mT := MinimalPolynomial (T);
     assert IsIrreducible (mT);
     e := Degree (mT);
     assert e eq Nrows (T);
     k := BaseRing (Parent (T));
     if Type (SPEC_FIELD) eq BoolElt then
          K := ext < k | mT >;
     else
          K := SPEC_FIELD;
          assert MinimalPolynomial (K.1, k) eq mT;
     end if;
     /* build inverse isomorphisms */
     Kbas := [ (K.1)^i : i in [0..e-1] ];
     Tbas := [ T^i : i in [0..e-1] ];
     MS := KMatrixSpace (k, e, e);
     MS := KMatrixSpaceWithBasis ([ MS!(Tbas[i]) : i in [1..e] ]);
     EnvT := sub < Parent (T) | T >; 
     phi := hom < EnvT -> K | x :-> &+ [c[i] * Kbas[i] : i in [1..e]]
            where c := Coordinates (MS, MS!x) >;
     psi := hom < K -> EnvT | x :-> &+ [c[i] * Tbas[i] : i in [1..e]]
            where c := __EltseqWithBasis (K, k, Kbas, x) >;
return EnvT, K, phi, psi; 
end function;


/*
  given <T1> and <T2> acting irreducibly on their (common) underlying module,
  return a transition matrix conjugating k[<T1>] to k[<T2>]

  This algorithm was communicated to us by W.M. Kantor.
*/
__IsomorphismBetweenFields := function (T1, T2)
     assert Nrows (T1) eq Nrows (T2);
     if Nrows (T1) eq 1 then
          return Identity (MatrixAlgebra (BaseRing (Parent (T1)), 1));
     end if;
     m1 := MinimalPolynomial (T1);
     assert IsIrreducible (m1);
     ET2, K2, phi2, psi2 := __IsomorphismWithField (T2);
     /* factor <m1> over <K2> */
     R2 := PolynomialRing (K2);
     m1K2 := R2!m1;
     roots := Roots (m1K2);
     /* take any root and pull back to ET2 */
     alpha := roots[1][1];
     assert alpha in K2;
     X2 := alpha @ psi2;
     assert MinimalPolynomial (X2) eq m1;
     /* conjugate k[<T1>] to k[<X1>] = k[<T2>] by module isomorphism */
     M1 := RModule (sub < Parent (T1) | T1 >);
     M2 := RModule (sub < Parent (X2) | X2 >);
     isit, C := IsIsomorphic (M1, M2);
     assert isit;
return C^-1;
end function;


__IsCyclic := function (R)
     if not Type (R) eq AlgMat then 
         //"input is not a matrix algebra";
         return false, _; 
     end if;
     if not IsCommutative (R) then 
         //"input is not commutative";
         return false, _; 
     end if;     
     if Ngens (R) eq 1 then 
          return true, R.1; 
     end if;    
     k := BaseRing (R);
     d := Degree (R);
     MA := MatrixAlgebra (k, d);
     J, W := WedderburnDecomposition (R);
     /* first compute what would be the 0-eigenspace of <sigma> */
     V0 := &meet [ Nullspace (W.i) : i in [1..Ngens (W)] ];
     n0 := Dimension (V0); 
     /* find the remaining generalized eigenspaces and corresponding transition matrix */
     degrees := [ n0 ];
     M := RModule (W);
     isubs := IndecomposableSummands (M);
     isubs := [ N : N in isubs | not forall{ w : w in Generators(W) | 
              forall{ n : n in Generators(N) | (n @Morphism(N,M))*w eq N!0 } } ];
     subs := [ ];
     while #isubs gt 0 do
         N := isubs[1];
         U := N;
         while exists (j){ i : i in [1..#isubs] | IsIsomorphic (N, isubs[i]) } do
             U +:= isubs[j];
             Remove (~isubs, j);
         end while;
         Append (~subs, U);
     end while;
     degrees cat:= [ Dimension (subs[i]) : i in [1..#subs] ];
     basis := &cat [ [ M!(subs[i].j) : j in [1..Ngens (subs[i])] ] : i in [1..#subs] ];
     C := Matrix (basis);    
     JC := sub < MA | [ C * J.i * C^-1 : i in [1..Ngens (J)] ] >;
     WC := sub < MA | [ C * W.i * C^-1 : i in [1..Ngens (W)] ] >;    
     /* build central primitive idempotents for <WC> */
     idempotents := [ ];
     z := MA!0;
     pos := 1;
     for i in [1..#degrees] do
        Append (~idempotents, 
           InsertBlock (z, Identity (MatrixAlgebra (k, degrees[i])), pos, pos));
        pos +:= degrees[i];
     end for;     
     /* build semisimple part of <sigma> */
     sigma := MA!0;
     pos := 1 + degrees[1];
     polys := [ ];
     for i in [2..#degrees] do
         ni := degrees[i];
         /* build the algebra induced by the (i-1)-th min ideal on its support */
         S := sub < MatrixAlgebra (k, ni) | [ ExtractBlock (WC.j, pos, pos, ni, ni) :
						    j in [1..Ngens (WC)] ] >;
         dS := Dimension (S);
         if exists (s){ t : t in S | Degree (MinimalPolynomial (t)) eq dS
		       //                  and t ne 0 
                  and not MinimalPolynomial (t) in polys } then
             InsertBlock (~sigma, s, pos, pos);
             Append (~polys, MinimalPolynomial (s));
         else
             //"could not build the semisimple part of <sigma>";
            return false, _;
         end if;
         pos +:= ni;
     end for;
     /* build nilpotent part of <sigma> */
     nsigma := MA!0;
     for i in [1..#degrees] do
         ni := degrees[i];
         ei := idempotents[i];
         Ji := sub < MA | [ ei * JC.j * ei : j in [1..Ngens (JC)] ] >;
         if Dimension (Ji) gt 0 then
              classes := [ ];
              for j in [1..Ngens (Ji)] do
                 isit, c := IsNilpotent (Ji.j);
                 assert isit;
                 Append (~classes, c);
              end for;        
              mi := Max (classes);
              assert exists (ui){ Ji.j : j in [1..Ngens (Ji)] |
                        forall { c : c in [1..mi-1] | Ji.j^c ne 0 } };
              nsigma +:= ui;
         end if;
     end for;
     /* add together the nilpotent and semisimple parts */
     sigma +:= nsigma;     
     /* if <R> is Env(<tau>) for some <tau>, then <R> is Env(<sigma>): check */
     sig := C^-1 * sigma * C;
     assert sig in R;     
     isit := sub < MA | [ sig , Identity (MA) ] > eq R;    
     if isit then
         return true, sig;
     else
         return false, _;
     end if;
return true, sig;
end function;


intrinsic IsCyclic (A::AlgMat) -> BoolElt, AlgMatElt
  {Decide if the algebra is generated by a single element, and return such a generator.}
return __IsCyclic (A);
end intrinsic;


intrinsic IsField (A::AlgMat) -> BoolElt, AlgMatElt
  {Decide if the algebra is a field, and if so return a field generator.}
     require IsIrreducible (RModule (A)) : "A must act irreducibly on its module";
           // remark: we can relax this if we wish
return IsCyclic (A);
end intrinsic;


intrinsic AlgebraToField (A::AlgMat) -> FldFin, Map, Map
  {Construct inverse isomorphisms between the algebra A and a field.}
     isit, T := IsField (A);
     require isit : "A must be a field";
     ET, K, phi, psi := __IsomorphismWithField (T);
     assert A eq ET;
return K, phi, psi;
end intrinsic;


intrinsic FieldToAlgebra (E::FldFin, F::FldFin) -> AlgMat, Map, Map
  {Constructs the field E as an algebra over the subfield F.}
     T := CompanionMatrix (MinimalPolynomial (E.1, F));
     ET, K, phi, psi := __IsomorphismWithField (T : SPEC_FIELD := E);
     assert K eq E;
return ET, psi, phi;
end intrinsic;


intrinsic FieldToAlgebra (E::FldFin) -> AlgMat, Map, Map
  {Constructs the field E as an algebra over its prime subfield.}
     F := PrimeField (E);
return FieldToAlgebra (E, F);
end intrinsic;




