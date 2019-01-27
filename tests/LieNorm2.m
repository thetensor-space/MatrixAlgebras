/* 
  Josh, here is the example from Glasby, Ribeiro, Schneider that you
  referred to in Section 8.2 of the der-densor paper. The answer to
  your question is that we don't yet handle it!
*/
GLASBY := function ()
  H, G := Hypothesis_6_1 (2);
  Factorization (#G);
  t := pCentralTensor (G);
  D := DerivationAlgebra (t);
  // work with the Levi subalgebra of D ...
  isit, L := HasLeviSubalgebra (D);   assert isit;
  
  // now, here's what we want to do ...
  N := GLNormalizer (L : PARTITION := [4,4,4]);
  // actually, this is too big, right? we really want to extract
  // the restriction to V+W and use the partition [4,4];
  // in any case, this is fine for the purposes of walking through
  // the example.

/*
  If you try this you will get the following error:
  
  Runtime error in 'GLNormalizer': not all summands of L are irreducible 
  J-modules for some minimal ideal J of L
  
  The issue is that the minimal ideals J = K = sl(2,11) of L act 
  together on one summand as a tensor product. The code cannot yet
  cope with this situation. Let's examine the steps, and see where
  we potentially run aground:
  
  1. Exponentiating a Chevalley basis. This is fine here assuming that
     we can actually compute a Chevalley basis. We can. If you cut and
     paste from the GLNormalizer function, the exponentiated part is
     SL(2,11) x SL(2,11). That's what we would expect.
     
  2. The centralizer of L. Again, no problem. We get a group of order
     (11-1)^5 = 10^5. This is the direct product of scalars on each
     irreducible summand. Note, it should really be 10^3, since we have
     a coupled action on U+V (see above). (Note also this would be a 
     larger group if we didn't force it to respect the partition. It
     looks as though it would contain GL(4,k), in fact.)
     
  3. Lifting automorphisms of the Lie algebra to the representation.
     This is where the difficulties start for the "non-simple action"
     in this example. I'm guessing this can be worked out for irreducible
     modules using the crystal basis, just as in the "simple action" case. 
     I've not worked through these details yet because I'm less certain
     about what is going on in this situation (see below).
     
  4. Permutations of isotypic components. This is the part that "hides"
     the graph isomorphism problem, but that isn't the issue in the code.
     One first determines a course partition into "possible isotypics"
     based just on simple type and representation type. For "non-simple actions"
     you'd have some sort of labelled hypergraph. This isn't the issue 
     either––we can compute this when we have to. The problem is that to 
     determine whether two ideals that are identically represented can actually 
     be permuted requires the conjugacy test. In the "simple action" case,
     the conjugacy test works swimmingly, but I'm not entirely sure what's
     going on in the "non-simple" case. I need to explore this more.
*/
end function;
