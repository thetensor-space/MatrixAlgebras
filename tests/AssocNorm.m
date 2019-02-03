/* some functions to test the GLNormalizer function for associative algebras */
load "~/MagmaGit/MatrixAlgebras/examples/assoc_constructs.m";

SetVerbose ("MatrixAlgebras", 2); 
k := GF (5);
TYPE := [ [2,3,2] , [2,3,2] , [2,3,2] ];
SCRAM := true;
A := MySemisimpleAssociativeAlgebra (k, TYPE : SCRAMBLE := SCRAM);
PART := [];
H := GLNormalizer (A : PARTITION := PART);