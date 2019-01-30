

/* functions to elucidate and access the structure of associative matrix algebras */


     /*------- Unit group os associative algebras -------*/

/*
  This function, which exists in the Magma distribution, will now be maintained
  in the MatrixAlgebras package. There was some discussion about the return of
  the Boolean, and it was decided to keep this in. The reason is that the
  MatrixAlgebra constructor in Magma does not automatically produce unital rings. 
*/


ALG := "Field"; // find primitive element of finite field using intrinsic


__IdentityMatrix := function (F, d)
return Identity (MatrixAlgebra (F, d));
end function;


/* 
   matrix blocks for composition factor which does not act absolutely irreducibly 
*/
__SmallOverLargerField := function (block, d, F)
   one := One (F);
   zero := Zero (F);
   root := PrimitiveElement (F);
   m1block := -1 * block;
   zblock := 0 * block;
   n := Nrows (block);
   r := d div n;
   id := __IdentityMatrix (F, d);
   gens := [];
   mat := id;
   InsertBlock (~mat, block, 1, 1);
   Append (~gens, mat);
   if n eq 1 or n eq d then return gens; end if;
   if #F eq 2 then
         mat := id;
         InsertBlock (~mat, zblock, 1, 1);
         InsertBlock (~mat, block, 1, (r - 1) * n + 1);
         for i in [2 .. r] do
              InsertBlock (~mat, block, (i - 1) * n + 1, (i - 2) * n + 1);
              InsertBlock (~mat, zblock, (i - 1) * n + 1, (i - 1) * n + 1);
         end for;
         Append (~gens, mat);
         mat := id;
         InsertBlock (~mat, block, 1, n + 1);
         Append (~gens, mat);
    else
         mat := id;
         InsertBlock (~mat, m1block, 1, 1);
         InsertBlock (~mat, block, 1, (r - 1) * n + 1);
         for i in [2 .. r] do
              InsertBlock (~mat, m1block, (i - 1) * n + 1, (i - 2) * n + 1);
              InsertBlock (~mat, zblock, (i - 1) * n + 1, (i - 1) * n + 1);
         end for;
         Append (~gens, mat);
    end if;
    gens := SequenceToSet (gens);
return SetToSequence (gens);
end function;


__ConstructBlockGenerators := function (M)
   F := BaseRing (M);
   d := Dimension (M);
   E := EndomorphismAlgebra (M);
   assert Ngens (E) eq 1;
   if ALG eq "Field" then
         t := Cputime ();
         m :=  MinimalPolynomial (E.1);
         Q := ext <F | m>;
         h := hom <Q -> E | x :-> Evaluate(PolynomialRing(F)!Eltseq(x, F), E.1)>;
         theta := PrimitiveElement (Q);
         alpha := h(theta);
   else
         t := Cputime ();
         // find a primitive element for E 
         ord := #E - 1;
         if Order (E.1) eq ord then
              alpha := E.1;
         else
              repeat
                   alpha := Random (E);
              until Determinant (alpha) ne 0 and Order (alpha) eq ord;
         end if;
   end if;
   // determine basis so that alpha has identical blocks along its diagonal 
   J, CB, facs := PrimaryRationalForm (alpha);
   e := Degree (facs[1][1]);
   m := Dimension (M) div e;
   if m gt 1 then
         block := ExtractBlock (J, 1, 1, e, e);
   else
         block := J;
   end if;
   size := OrderGL (m, (#F)^e);
   gens := __SmallOverLargerField (block, d, F);
return [CB^-1 * g * CB : g in gens], size;
end function;


__MatricesToAlgebraElement := function (M)
   if #M eq 0 then return []; end if;
return Matrix ([Vector (m): m in M]);
end function;

__VectorsToMatrices := function (N, d)
   if Type (N) eq ModTupFld then N := Basis (N); end if;
   if #N eq 0 then return []; end if;
return [Matrix (d, d, N[i]) : i in [1..#N]];
end function;

/* 
   INPUT: 
         * dims = list of dimensions of blocks
         * d = dimension of matrices
         
   OUTPUT 
         * init = list of integers s.t. i-th block starts at
                  position ( init[i]+1, init[i]+1 )
         * blocks = list of integers containing the positions
                    of the block entries in vector of length d^2 
*/
__BlockInfo := function (dims, d)
   // determine positions in row vector of block entries
   b := #dims;          // number of blocks
   blocks := [];       // positions of block entries in vector
   init := [ 0 ];      // i-th block starts at position init[i]+1
   start := 0;
   for i in [1 .. b] do
         for j in [1 .. dims[i]] do
              blocks cat:= [start+1 .. start+dims[i]];
              start +:= d;
         end for;
         start +:= dims[i];
         if i gt 1 then
              init[i] := init[i-1] + dims[i-1];
         end if;
   end for;
return <init, blocks>;
end function;

/* determine all isomorphic blocks and insert them in 'mat'

  INPUT: 
        * mat = dxd matrix containing 1 nontrivial block
        * block = the nontrivial block of 'mat' (nxn matrix)
        * n = dimension of 'block'
        * iso = list containing positions of isomorphic blocks and the
                actual isomorphisms
                [ b_1, b_2, iso_2, b_3, iso_3, ..., b_t, iso_t ]
                => M_1^iso_i = M_i
        * init = i-th block starts at position init[i]+1

  OUTPUT:  
        matrix 'mat' containing isomorphisc blocks according to 'iso' 
*/
procedure __IsoBlocks (~mat, block, n, iso, init)
   c := #iso;
   for i in [2 .. c-1 by 2] do
         B := iso[i + 1]^1 * block * (iso[i+1]^-1);  // isomorphic block
         s := init[iso[i]];                     // block starts at position s+1
         InsertBlock (~mat, B, s + 1, s + 1);
   end for;
end procedure;


/* 
  determines gens satisfying isomorphism conditions given by 'iso'
  and adds them to 'mats'

  INPUT: 
        * gens = list of matrices already determined
        * iso = [ b_1, b_2, iso_2, b_3, iso_3, ..., b_t, iso_t ]
                b_i-th block ( i = 2, ..., t ) is isomorphic to
                b_1-st block via isomorphism iso_i, i.e.,
                M_1^iso_i = M_i
        * init = i-th block starts at position ( init[i]+1, init[i]+1 )
        * d = dimension of matrices
        * F = field
        * n = dimension of block being dealt with
        * r = block being dealt with starts at position ( r+1, r+1 ) 
*/
procedure __IsoGenerators (~gens, iso, init, d, F, r, sub)
   id := __IdentityMatrix (F, d);
   for i in [1..#sub] do
         mat := id;
         n := Nrows (sub[i]);
         InsertBlock (~mat, sub[i], r + 1, r + 1);
         // insert isomorphic blocks & append generator to 'gens'
         __IsoBlocks (~mat, sub[i], n, iso, init);
         Append (~gens, mat);
   end for;
end procedure;


/* generators for GL (n, F) */
__GLGenerators := function (n, F)
   if Type (F) eq RngIntElt then F := GF (F); end if;

   if #F gt 2 or n gt 1 then
         G := GL (n, F);
         return [G.i: i in [1..Ngens (G)]];
   else
         gens := [ __IdentityMatrix (F, n) ];
   end if;
return gens;
end function;


/* 
  Add to 'gens' generators for a subgroup of GL(n,F) in block
    starting at position ( r+1, r+1 )
   this subgroup is generated by sub;

  INPUT:
        * gens = list of dxd generating matrices already determined
        * d = dimension of matrices
        * F = field
        * r = block starts at position ( r+1, r+1 )
        * sub = generators for subgroup  of appropriate GL block 
*/
procedure __BlockGenerators (~gens, d, F, r, sub)
   id := __IdentityMatrix (F, d);
   for i in [1..#sub] do
         mat := id;
         InsertBlock (~mat, sub[i], r + 1, r + 1);
         Append (~gens, mat);
   end for;
end procedure;

/* INPUT: 
         * dims = list containing dimensions of the blocks
         * isom - isom[i] = [a] => a-th block forms single iso class
                  isom[i] = [ a, b, [iso_b], c, [iso_c], ... ]
                  => i-th block is isomorphic to a-th block and
                     isomorphism is iso_i, i.e.,
                     M_a^iso_i = M_i
         * F = field
         * d = dimension of stabilising matrices
         * init = i-th block starts at position init[i]+1
         
   OUTPUT: 
            a list 'gens' of vectors which as dxd matrices are in
            block form and generate the general linear groups in
            the blocks satisfying the isomorphism conditions 
*/
__GLBlockGenerators := function (dims, isom, CF, F, d, init: Matrices := [])
   Supplied := Matrices;
   supplied := #Supplied eq 0 select false else true;
   li := #isom;
   gens := [];
   size := 1;
   for i in [1 .. li] do
      c := #isom[i];                // length of i-th isomorphism info
      n := dims[ isom[i][1] ];      // dimension of block
      r := init[ isom[i][1] ];      // block starts at position r+1
      index := isom[i][1];
      if IsAbsolutelyIrreducible (CF[index]) then
         if supplied eq false then
            sub := __GLGenerators (n, F);
         else
            sub := Supplied[i];
         end if;
         size *:= OrderGL (n, #F);
      else
         sub, temp := __ConstructBlockGenerators (CF[index]);
         size *:= temp;
      end if;
      if c eq 1 then
            __BlockGenerators (~gens, d, F, r, sub);
      else
            __IsoGenerators (~gens, isom[i], init, d, F, r, sub);
      end if;
   end for;
return __MatricesToAlgebraElement (gens), size;
end function;


/* INPUT: 
        * blockSol = list of vectors which as dxd matrices generate
                     the linear groups in the blocks satisfying
                     isomorphism conditions
        * sys = list of vectors representing the system of linear
                equations whose solution is the non-p-part (in block
                form) of the algebra normalising the lattice
        * F = field
        * d = dimension of the parent vector space

   OUTPUT: 
           a list 'blockPart' containing dxd matrices generating
           the non p-part of the subgroup of GL(d,F) normalising
           the lattice 
*/
__BlockPartGenerators := function (blockSol, sys, blocks, F, d)
   h := d^2;
   nh := h + 1;
   z := Zero (F);
   one := One (F);
   zero := [z: i in [1..nh]];   // zero vector
   blockPart := [];
   Vnh := VectorSpace (F, nh);
   sys := Basis (sys);
   sys := [Eltseq (s) cat [0]: s in sys];
   for i in [1..Nrows (blockSol)] do
      b := blockSol[i];
      // substitute block entries of generator 'b' in the system
      newsys := sys;
      for j in blocks do
         eqn := zero;
         eqn[j] := one;
         eqn[nh] := b[j];
         Append (~newsys, eqn);
      end for;
      N := sub <Vnh | newsys>;
      B := BasisMatrix (N);
      c := Nrows (B);
      // determine one solution for the non-homogeneous system obtained
      if c gt h then
         return false;
      else
         v := Vector (Transpose (ExtractBlock (B, [1..c], [nh])));
         newsys := ExtractBlock (B, 1, 1, c, h);
         flag, s := IsConsistent (Transpose (newsys), v);
         if flag eq true then
            Append (~blockPart, s);
         else
            return false;
         end if;
      end if;
   end for;
   blockPart := __VectorsToMatrices (blockPart, d);
return blockPart;
end function;



/* INPUT: 
      * solution = list of solutions for system of linear equations
                   after changing basis to block form
      * dims = list containing dimensions of blocks
      * isom = list containing isomorphism information for blocks
      * F = field
      * d = dimension of matrices and parent vector space

   OUTPUT:
       * pPart = list of dxd invertible matrices generating the
                    p-part of the stabiliser
       * blockPart = list of dxd invertible matrices generating
                     the non-p-part of the stabiliser
       * size = order of the subgroup of GL(d,F) generated by the
                matrices in 'pPart' and 'blockPart'
   
   If Jacobson is true then use intrinsic Jacobson radical function,
   otherwise compute as in Brooksbank & O'Brien paper 
*/
__UnitsGenerators := function (A, solution, dims, isom, CF :
                             Matrices := [], Jacobson := false)
   d := Degree (A);
   F := BaseRing (A);
   Supplied := Matrices;
   /* get some information on the blocks
      - init = i-th block starts at row and column init[i]+1
      - blocks = list containing the positions in a vector of length d^2
              of the block entries in the corresponding dxd matrix */
   info := __BlockInfo (dims, d);    //   = [ init, blocks ]
   char := Characteristic (F);
   sys := NullspaceOfTranspose (solution);
   // p-part
   if not Jacobson then
      index := info[2];
      MA := KMatrixSpace (F, #index, d^2);
      Z := Zero (MA);
      for i in [1..#index] do Z[i][index[i]] := 1; end for;
      newsys := VerticalJoin (BasisMatrix (sys), Z);
      pPart := NullspaceOfTranspose (newsys);
      pPart := [ Matrix (d, d, p) : p in Basis (pPart) ];
   else
      // "Using inbuilt Jacobson";
      pPart := JacobsonRadical (A);
      pPart := [ pPart.i : i in [1..Ngens (pPart)] ];
   end if;
   if #pPart gt 0 then
      e := Degree (F); w := PrimitiveElement (F);
      W := [w^i : i in [0..e - 1]];
      pPart := &cat[[x * W[i + 1]: i in [0..e - 1]]: x in pPart];
      // go over to group elements by inserting 1's in the diagonal
      MA := MatrixAlgebra (F, d);
      id := Identity (MA);
      pPart := [MA!pPart[i] + id : i in [1..#pPart]];
   end if;
   size := char^#pPart;
   factors := Factorisation (size);
   // determine non-p-part generators as group elements
   blockSol, temp := __GLBlockGenerators (dims, isom, CF, F, d, info[1]:
                                        Matrices := Supplied);
   blockPart := __BlockPartGenerators (blockSol, sys, info[2], F, d);
   if Type (blockPart) eq BoolElt then
      return false, _, _;
   elif blockPart cmpeq [] then
      temp := 1;
   end if;
   factors *:= Factorisation (temp);
   size *:= temp;
   // remove trivial generators
   pPart := [m : m in pPart | IsIdentity (m) eq false];
   blockPart := [m : m in blockPart | IsIdentity (m) eq false];
   // check trivial case
   if pPart eq [] and blockPart eq [] then
      blockPart := [__IdentityMatrix (F, d)];
   end if;
return pPart, blockPart, size, factors;
end function;



__DetermineIsomorphisms := function (S)
   assert #S gt 0;
   Different := [S[1]];
   Combined := [ [*1*] ];
   for i in [2..#S] do
         j := 0; new := true;
         repeat
              j +:= 1;
              flag, map := IsIsomorphic (S[i], Different[j]);
              new := (flag eq false);
         until (new eq false) or (j ge #Different);
         if new then
              Append (~Different, S[i]);
              Append (~Combined, [* i *]);
         else
              Append (~Combined[j], i);
              Append (~Combined[j], map);
         end if;
      end for;
return Combined;
end function;


__HasNoUnits := function (CF)
   for i in [1..#CF] do
      if Dimension (CF[i]) eq 1 then
         A := ActionGenerators (CF[i]);
         if Set (A) eq {0} then return true; end if;
      end if;
   end for;
return false;
end function;


__UnitGroup := function (A, CF, CB : Jacobson := false)
   dims := [Dimension (CF[i]): i in [1..#CF]];
   isom := __DetermineIsomorphisms (CF);
   J := CB^-1;
   gens := Basis (A);
   solution := [CB * b * J : b in gens];
   solution := Matrix ([Vector (s): s in solution]);
   //if exists {x : x in CF | IsAbsolutelyIrreducible (x) eq false} then
   //   vprint Stabiliser: "Not absolutely irreducible";
   //end if;
   pPart, blockPart, order, f_order := __UnitsGenerators (A, solution, dims, isom, CF:
                                               Jacobson := Jacobson);
   if Type (pPart) eq BoolElt then
         return false, _, _, _;
   end if;
   d := Degree (A);
   F := BaseRing (A);
   if Jacobson then
         P := [GL(d, F) ! p : p in pPart];
   else
         P := [GL(d, F) ! (J * b * CB) : b in pPart];
   end if;
   B := [GL(d, F) ! (J * b * CB) : b in blockPart];
return B, P, order, f_order;
end function;

/*
  This is the "UnitGroup" function distributed with Magma. The name
  change is to avoid overwriting this function.
*/
intrinsic UnitGroupOfAlgebra (A::AlgMat) -> BoolElt, GrpMat

  {If matrix algebra defined over a finite field has invertible matrices,
   then return true and group of such matrices, else false.}

   d := Degree (A);
   F := BaseRing (A);
   require IsFinite (F): "Base field for algebra must be finite";
   
   if Dimension (A) eq 0 then return false, _; end if;

   M := RModule (A);
   CS, CF, CB := CompositionSeries (M);

   /* criterion for absence of units */
   nounits := __HasNoUnits (CF);
   if nounits then return false, _; end if;

   B, P, order, f_order := __UnitGroup (A, CF, CB);
   if Type (B) eq BoolElt then return false, _; end if;
   G := sub<GL(d, F) | B, P>;
   G`FactoredOrder := f_order;
   G`Order := order;
   
return true, G;

end intrinsic;