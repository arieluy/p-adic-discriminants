// poly is Eisenstein
// function modified from Chad Awtrey
function IsNewPoly(poly, lst)
    Zp := CoefficientRing(poly);
    Zpx<x> := PolynomialRing(Zp);
    Q3 := pAdicRing(3, 30);
    E := ext<Q3 | poly>;
    for j in lst do
        if HasRoot(Zpx!j, E) then return false; end if;
    end for; return true;
end function;

// Find a generating polynomial for each of the 10 (non-isomorphic) extensions of degree 3 of Q_3.
// This finds the 9 totally ramified ones. The other is unramified.
lst := [];
for i in [0..5] do
    for j in [0..5] do
        for k in [3,6,12,15,21,24] do
            poly := x^3 + 3*i*x^2 + 3*j*x + k;
            if IsNewPoly(poly, lst) then Append(~lst, poly);
            end if;
        end for;
    end for;
end for;
lst;

[Discriminant(p) : p in lst];