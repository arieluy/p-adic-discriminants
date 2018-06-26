// Galois Group is in here   
   Gu := Sym(4);
// Candidates   
   G1 := AlternatingGroup(4);
   G2 := DihedralGroup(4);
// Galois group contains H
   H := CyclicGroup(4);
   a,b,c := CosetAction(Gu,H);

   o1 := Orbits(a(G1));
   [#oo: oo in o1];

   o2 := Orbits(a(G2));
   [#oo: oo in o2];

   o3 := Orbits(a(H));
   [#oo: oo in o3];

