intrinsic AutoGr2(phi::RngUPolElt) -> SeqEnum
{Find the automorphism group of a polynomial}
Zx<x> := PolynomialRing(Integers());
assert IsIrreducible(phi);
E<r> := NumberField(phi);
Ey<y> := PolynomialRing(E);
roo := [j[1] : j in Roots(Ey ! Polynomial(Eltseq(phi)))];
return roo; end intrinsic;


intrinsic GaloisGr2(phi::RngUPolElt) -> SeqEnum
{Find the Galois group of a polynomial}
Zx<x> := PolynomialRing(Integers());
split := Zx ! DefiningPolynomial(SplittingField(phi)); split;
E<r> := NumberField(split);
Ey<y> := PolynomialRing(E);
roo := [j[1] : j in Roots(Ey ! Polynomial(Eltseq(phi)),E)];
sroo := [j[1] : j in Roots(Ey ! Polynomial(Eltseq(split)),E)];
A := [hom<E->E | s> : s in sroo];
S := [[A[i](j) : j in roo] : i in [1..# A]];
Perms := [];
for P in S do
    temp := "";
    for p in P do
	temp cat:= IntegerToString(Index(roo, p));
	end for;
    Append(~Perms, temp); end for;
return Perms;
end intrinsic;
