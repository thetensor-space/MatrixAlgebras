AD := function (L, x)
return Matrix ([ Coordinates (L, x*y) : y in Basis (L) ]);
end function;

intrinsic IsAdNilpotent (L::AlgLie, x::AlgLieElt) -> BoolElt, RngIntElt
  { Decide whether x in L is ad-nilpotent.}
  ad_x := AD (L, x);
return IsNilpotent (ad_x);
end intrinsic;

intrinsic Exponentiate (z::AlgMatElt) -> GrpMatElt
  { Exponentiate the nilpotent matrix z.}
  require IsNilpotent (z) : "given element is not nilpotent";
	u := z^0;
	i := 1;
	v := z;
	while not (v eq 0) do
		u +:= v / Factorial (i);
		i +:= 1;
		v *:= z;
	end while;
return GL (Degree (Parent (z)), BaseRing (Parent (z)))!u;
end intrinsic;

intrinsic Exponentiate (z::AlgMatLieElt) -> GrpMatElt
  { Exponentiate the nilpotent matrix z.}
  z0 := MatrixAlgebra (BaseRing (Parent (z)), Degree (Parent (z)))!z;
return Exponentiate (z0);
end intrinsic;
