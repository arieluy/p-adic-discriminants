function MakeGroup2()
G1 := DirectProduct([ Sym(23), Sym(2) ]);
S := Sym(25);
mappy := hom <G1->S|S!(2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,\
24,25), S!(2, 3),S!(1,6)>;
G := sub<S|[mappy(g): g in Generators(G1)]>;
return G;
end function;
