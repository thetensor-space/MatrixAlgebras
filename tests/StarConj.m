/* some tests for conjugacy of *-algebras */

test_simple_nat := function (name, d, k)
     S := SimpleStarAlgebra (name, d, k);
     g1 := Random (GL (d, k));
     S1 := S^g1;
     g2 := Random (GL (d, k));
     S2 := S^g2;
     // now carry out conjugacy test
return S1, S2;
end function;

test_simple := function (name, d, K, k)
     T := SimpleStarAlgebra (name, d, K);
     S, phi, psi := WriteOverSmallerField (T, k);
     n := d * Degree (K, k);
     g1 := Random (GL (n, k));
     S1 := S^g1;
     g2 := Random (GL (n, k));
     S2 := S^g2;
     // now carry out conjugacy test
return S1, S2;
end function;