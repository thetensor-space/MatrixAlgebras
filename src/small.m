/* this file contains a function to write algebras over smaller fields */

__image := function (a, f, F)
     d := Degree (Parent (a));
     e := Degree (BaseRing (Parent (a))) div Degree (F);
     im := MatrixAlgebra (F, d*e)!0;
     for i in [1..d] do
          for j in [1..d] do
               InsertBlock (~im, (a[i][j]) @ f, 1+(i-1)*e, 1+(j-1)*e);
          end for;
     end for;
return im;
end function;

__preimage := function (b, g, E)
     e := Degree (E) div Degree (BaseRing (Parent (b)));
     n := Degree (Parent (b)) div e;
     preim := MatrixAlgebra (E, n)!0;
     for i in [1..n] do
          for j in [1..n] do
               preim[i][j] := (ExtractBlock (b, 1+(i-1)*e, 1+(j-1)*e, e, e)) @ g;
          end for;
     end for;
return preim;
end function;

/* 
  There is an analogue of this function in Magma for groups and modules;
  hence, no reason why there should not be one also for algebras. 
*/
intrinsic WriteOverSmallerField (A::AlgMat, F::FldFin) -> AlgMat , Map , Map

  {Given an algebra A of d by d matrices over a finite field E having degree e
        and a subfield F of E having degree f, write the matrices of A as d*e/f 
        by d*e/f matrices over F and return the algebra and inverse isomorphisms.}

     E := BaseRing (A);
     require IsSubfield (F, E) : "F must be a subfield of the defining ring of A";
     
     S, f, finv := FieldToAlgebra (E, F);
     e := Degree (E, F);
     B := Basis (A);
     gens := [ ((E.1) ^ i) * B[j] : i in [0..e-1] , j in [1..#B] ];
     imgens := [ __image (x, f, F) : x in gens ];
     
     d := Degree (A);
     M := MatrixAlgebra (F, d*e);
     AF := sub < M | imgens >;
     phi := hom < A -> AF | a :-> __image (a, f, F) >; 
     psi := hom < AF -> A | b :-> __preimage (b, finv, E) >;
     
     // add involution to AF if A has one
     if assigned A`Star then
          AF`Star := hom < AF -> AF | x :-> ((x @ psi) @ A`Star) @ phi >;
     end if;
     
return AF, phi, psi;
end intrinsic;