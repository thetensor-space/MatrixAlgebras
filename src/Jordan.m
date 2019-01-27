/* Jordan form functions: not intrinsics since they clash with Magma versions */

/*
   Given an irreducible polynomial <p> over a field <k>,
   and a <partition>, construct the generalised Jordan
   block determined by these parameters.
*/
__build_JF := function (p, partition)
     Cp := CompanionMatrix (p);
     s := #partition;
     m := &+ partition;
     k := BaseRing (Parent (p));
     d := Degree (p);
     IdBlock := Identity (MatrixAlgebra (k, d));
     JF := DiagonalJoin (< Cp : i in [1..m] >);
     mm := 1;      
     for i in [1..s] do
         mi := partition[i];
         for j in [1..mi - 1] do
	     InsertBlock (~JF, IdBlock, mm, mm + d);
             mm +:= d;
	 end for;
         mm +:= d;
     end for;
return JF;
end function;


/*
   Given a primary matrix <P>, return the generalized 
   Jordan normal form of <P> and the partition
   associated with the invariant factors of <P>
*/
__primary_JF := function (P)

     k := BaseRing (Parent (P));

     // first conjugate <P> to Magma JNF
     J, D := JordanForm (P);

     mpol := MinimalPolynomial (J);
     mfac := Factorisation (mpol);

     if (#mfac gt 1) then
        error "<P> must be primary";
     end if;
  
     p := mfac[1][1];
     ifacs := Sort (InvariantFactors (J));
     partition := [ Factorisation (ifacs[i])[1][2] : 
                                      i in [1..#ifacs] ];

     if (Degree (p) gt 1) then   
       
	 /* build the (primary) Jordan form for given parameters */
         JF := __build_JF (p, partition);
         J, C := JordanForm (JF);
         D := C^-1 * D;
         
     else

         /* My Jordan form agrees with the one used by Magma */       
         JF := J;
    
     end if;     
     
return JF, D, partition;
end function;


/* a partition ordering function */
__le_partition := function (part1, part2)
     if part1 eq part2 then return true; end if;
     if #part1 lt #part2 then return true; end if;
     if #part1 gt #part2 then return false; end if;
     i := Min ({ j : j in [1..#part1] | part1[j] ne part2[j] });
return part1[i] lt part2[i];
end function;


/*  
   Builds the generalized Jordan Normal Form of <X> with blocks 
   appearing in increasing order of min poly degree, and within 
   each min poly degree, "increasing" order of partition.

   This modification of an earlier function was written in
   Fort Collins in December, 2014.
*/
__JordanNormalForm := function (X)

     d := Nrows (X);
     k := BaseRing (Parent (X));
     mfac := Factorisation (MinimalPolynomial (X));
     degs := { Degree (mfac[i][1]) : i in [1..#mfac] };
     degs := [ m : m in degs ];
     ordered := [ [ mfac[i] : i in [1..#mfac] | Degree (mfac[i][1]) eq m ] : 
                    m in degs ];

     /* proceed sequentially through the primary components */
     info := [* *];
     basis := [ ];
     
     for j in [1..#degs] do
     
         nullspaces := [* *];
         transition_matrices := [* *];
         partitions := [* *];
         pols := [* *];
         
         for i in [1..#ordered[j]] do
	       
	         pi := ordered[j][i][1];
             Append (~pols, pi);
             ei := ordered[j][i][2];
             fi := pi^ei;   
             Xi := Evaluate (fi, X);
             Vi := Nullspace (Xi);
             Append (~nullspaces, Vi);
             di := Dimension (Vi);
           
             /* restrict <Xi> to <Vi> to get a primary matrix <Pi> */
             rows := [ Coordinates (Vi, (Vi.j) * X) : j in [1..di] ];
             Pi := Matrix (rows);
           
             Ji, Ci, parti := __primary_JF (Pi);
             Append (~transition_matrices, Ci);
             Append (~partitions, parti);
           
         end for;
     
         /* put partitions into a standard order */         
         index := { 1 .. #partitions };
         order := [ ];         
         while #order lt #partitions do
             assert exists (s){ t : t in index | 
                  forall { u : u in index | 
                               __le_partition (partitions[t], partitions[u]) } };
             Append (~order, s);
             Exclude (~index, s);
         end while;
     
         /* select basis to exhibit Jordan structure */
         for i in order do
             Ci := transition_matrices[i];
             Vi := nullspaces[i];
             di := Dimension (Vi);
             bas := [ &+ [ Ci[s][t] * Vi.t : t in [1..di] ] : s in [1..di] ];         
             basis cat:= bas;
             Append (~info, < pols[i], partitions[i] >);
         end for;
         
     end for;
     
     C := Matrix (basis);
     J := C * X * C^-1;
     
return J, C, info;    

end function;

