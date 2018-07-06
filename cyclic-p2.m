load "p-squared-cubed.m";
load "p-adic-extensions.m";

function RandomPossiblyCyclic(p, n, UB, LB)
    Zp := pAdicRing(p, 10*p);
    Zpx<x> := PolynomialRing(Zp);
    phi := x^n;
    for i := n-1 to 0 by -1 do
        if i in [1..(p^2-p-2)] and (i mod p) ne 0 then 
            phi +:= Random(UB, LB)*p^3*x^i;
        elif not i in [0, p^2-p] then
            phi +:= Random(UB, LB)*p^2*x^i;
        elif i eq 0 then
            repeat a := Random(UB, LB); until GCD(a, p) eq 1; 
            phi +:= a*p;
        else
            phi +:= Random(UB, LB)*p^(Random(0, 3))*x^i;
        end if;
    end for;
    return phi;
end function;

function IsoPolys2(p, n)
    lst := [];
    Zp := pAdicRing(p, 10*p);
    Zpx<x> := PolynomialRing(Zp);
    // E := ext<Zp | phi>;
    // j := Valuation(Discriminant(phi)) - n + 1;
    for i := 1 to 1000 do
        psi := RandomPossiblyCyclic(p, n, -1000, 1000); 
        if IsEisenstein(psi) then Append(~lst, psi);
        end if;
    end for;
    return lst;
end function;


p := 5;
Zp := pAdicRing(p, 10*p);
Zpx<x> := PolynomialRing(Zp);

p;
l := CyclicDegreePSquared(p);
plist := 