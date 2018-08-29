intrinsic MyDerivationAlgebra (T::TenSpcElt) -> AlgMatLie , Tuple
  {A version of DerivationAlgebra that returns representations on the three
   associated modules.}
    c := Dimension (Domain (T)[1]);
    d := Dimension (Domain (T)[2]);
    e := Dimension (Codomain (T));
    D := DerivationAlgebra (T);
    k := BaseRing (D);
    n := Degree (D);
    DU := sub < MatrixLieAlgebra (k, c) |
                [ ExtractBlock (D.i, 1, 1, c, c) : i in [1..Ngens (D)] ] >;
    DV := sub < MatrixLieAlgebra (k, d) |
                [ ExtractBlock (D.i, c+1, c+1, d, d) : i in [1..Ngens (D)] ] >;
    DW := sub < MatrixLieAlgebra (k, e) |
                [ ExtractBlock (D.i, c+d+1, c+d+1, e, e) : i in [1..Ngens (D)] ] >;
    fU := hom < D -> DU | x :-> DU!ExtractBlock (x, 1, 1, c, c) >;
    fV := hom < D -> DU | x :-> DU!ExtractBlock (x, c+1, c+1, d, d) >;
    fW := hom < D -> DU | x :-> DU!ExtractBlock (x, c+d+1, c+d+1, e, e) >;
return D, <fU, fV, fW>;
end intrinsic;
