              /* some constructor functions for Lie algebras */

/*
  This function produces a randomly conjugated version of a simple
  matrix algebra with specific parameters k, m, e
  It is isomorphic to Mat(K, m) where [K : k] = e
  This is a simplified version of the next function below.
*/

MySimpleAlgebra := function (k, m, e)
  MA := MatrixAlgebra (k, m*e);
  repeat
       x := Random (MatrixAlgebra (k, e));
       mx := MinimalPolynomial (x);
  until IsIrreducible (mx);
  z := DiagonalJoin (< x : i in [1..m] >);
  C := Centralizer (MA, sub < MA | z >);
  g := Random (GL (m*e, k));
  A := sub < MA | [ g * C.i * g^-1 : i in [1..Ngens (C)] ] >;
return A;
end function;


/*  
  The following is a version of a similar function for Lie algebras.
  It builds a semisimple associative algebra according to the input data:
  (1) a field, k
  (2) a list, L, of triples  [ d , m , e ]
  Each triple corresponds to an ideal, isomorphic to M(d,E), where [E:k]=e,
  embedded diagonally m times.
*/
MySemisimpleAssociativeAlgebra := function (k, L : SCRAMBLE := false)  
  ideals := [* *];
  for i in [1..#L] do
       l := L[i];
       K := ext<k|l[3]>;
       JK := MatrixAlgebra (K, l[1]);
       Jk := WriteOverSmallerField (JK, k);   assert Degree (Jk) eq l[1] * l[3];
       di := &* l;
       I := sub < MatrixAlgebra (k, di) | 
          [ DiagonalJoin (< Jk.j : s in [1..l[2]] >) : j in [1..Ngens (Jk)] ] >;
       assert Dimension (I) eq Dimension (Jk);
       Append (~ideals, I);
  end for;
  A := ideals[1];
  for i in [2..#ideals] do
       A := DirectSum (A, ideals[i]);
  end for;
  assert Degree (A) eq &+ [ &* l : l in L ];
  assert Dimension (A) eq &+ [ l[1]^2 * l[3] : l in L ];
  if SCRAMBLE then
       g := Random (GL (Degree (A), k));
       A := sub < Generic (A) | [ g * A.i * g^-1 : i in [1..Ngens (A)] ] >;
  end if;
return A;
end function; 

