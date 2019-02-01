/* some functions to test the GLNormalizer function for Lie algebras */
load "~/MagmaGit/MatrixAlgebras/examples/Lie_constructs.m";

/*
  A dinky example to illustrate the effect of PARTITION on the permutation
  of isotypic components; one is only allowed to permute isotypic components
  within the domain / codomain specified by PARTITION.
*/
k := GF (7);
SetVerbose ("MatrixAlgebras", 2);
PART1 := [];
PART2 := [2,2,2];
ST := [ "A1" , "A1" , "A1" ];
RT := [ [1,0] , [1,0] , [1,0] ];
L := MySemisimpleMatrixLieAlgebra (k, ST, RT : SCRAMBLE := false);
  // L is the sum of three natural copies of sl(2,k)
G1 := GLNormalizer (L : PARTITION := PART1);
G2 := GLNormalizer (L : PARTITION := PART2);
assert G2 subset G1;
assert #G1 div #G2 eq 6;
"permutation illustration complete";
"   ";

/*
  Another dinky example to illustrate the effect of PARTITION on the
  group centralizing the algebra; one only computes the centralizer
  within the domain / codomain specified by PARTITION.
*/
PART1 := [];
PART2 := [2,2,2];
ST := [ "A2" ];
RT := [ [3,0] ];
L := MySemisimpleMatrixLieAlgebra (k, ST, RT : SCRAMBLE := true);
   // L is a diagonal embedding of sl(2,k) in gl(6,k)
G1 := GLNormalizer (L : PARTITION := PART1, SANITY := true);
   // within G1 is the full centralizer of L in GL(6,k)
G2 := GLNormalizer (L : PARTITION := PART2);
   // G2 contains only the centralizer on each domain / codomain space
assert G2 subset G1;
assert #G1 div #G2 eq #GL(3,k) div (#k-1)^3;
"centralizer illustration complete";
"   ";

