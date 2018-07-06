load "p-squared-cubed.m";

// Checks if two polynomials generate the same extension in Zp
function IsSamePoly(phi, psi, p)
    Zp := pAdicRing(p, 10*p);
    Zpx<x> := PolynomialRing(Zp);
    E := ext<Zp | phi>;
    return HasRoot(Zpx!psi, E);
end function;

// Defining polynomials for all degree n extensions in Zp
function Polys(p, n)
    Zp := pAdicRing(p,10*p);
    Zpx<x> := PolynomialRing(Zp);
    L := AllExtensions(Zp, n);
    return [DefiningPolynomial(k, Zp) : k in L];
end function;

// Generates a list of polynomials with isomorphic extensions to phi
function Deg3(p, phi)
    lst := [];
    Zp := pAdicRing(p, 10*p);
    Zpx<x> := PolynomialRing(Zp);
    E := ext<Zp | phi>;
    for i1 in [0..6] do
        for i2 in [0..6] do
            for i3 in [0..6] do
                for i4 in [0..6] do
                    // for i5 in [0..3] do
                        for j in [1..5] do
                            psi := x^5 + p*i3*x^4 + p*i4*x^3 + p*i1*x^2 + p*i2*x + p*j;
                            if IsEisenstein(psi) and HasRoot(Zpx!psi, E) then Append(~lst, psi);
                            end if;
                        end for;
                    // end for;
                end for;
            end for;
        end for;
    end for;
    return lst;
end function;

// Generates a random polynomial with isomorphic extension to phi
function RandomEisen(p, n, j, UB, LB)
    Zp := pAdicRing(p, 10*p);
    Zpx<x> := PolynomialRing(Zp);
    phi := x^n;
    for i := n-1 to 0 by -1 do
        if i ge j then
            phi +:= Random(UB, LB)*p*x^i;
        elif (i eq j) or (i eq 0) then
            repeat a := Random(UB, LB); until GCD(a, p) eq 1;
            phi +:= a*p*x^i;
        else
            phi +:= Random(UB, LB)*p^2*x^i;
        end if;
    end for;
    return phi;
end function;

// Generates a list of random polynomials with isomorphic extensions to phi
function IsoPolys(p, n, phi)
    lst := [];
    Zp := pAdicRing(p, 10*p);
    Zpx<x> := PolynomialRing(Zp);
    E := ext<Zp | phi>;
    j := Valuation(Discriminant(phi)) - n + 1;
    for i := 1 to 1000 do
        psi := RandomEisen(p, n, j, -10, 10);
        if IsEisenstein(psi) and HasRoot(Zpx!psi, E) then Append(~lst, psi);
        end if;
    end for;
    return lst;
end function;


// Checks the conjecture for a list of polynomials
function CheckC(p, lst)
    n := # lst;
    m := n div 2 + 1;
    D := [Discriminant(phi) : phi in lst];
    L := [];
    for i in [1..m] do
        for j := n to m by -1 do
            a := D[i]; b := D[j];
            if i ne j then Append(~L, Valuation(a-b)-Valuation(a)); end if;
        end for;
    end for;
    return Multiset(L);
end function;

procedure main()
    primes := [3];
    for p in primes do
        n := p; p;
        plist := Polys(p, n);
        for phi in plist do
            if IsEisenstein(phi) then
                l := IsoPolys(p, n, phi);
                v := Valuation(Discriminant(phi));
                print phi, CheckC(p, l);
            end if;
        end for;
    end for;
    "done";
end procedure;

// main();

function SortByGaloisGroup(p, lst)
    newlst := [];
    for phi in lst do
        v := Valuation(Discriminant(phi));
        d := (Integers()!Discriminant(phi) mod p^(1+Integers()!v))/p^(Integers()!v);
        Append(~newlst, <v, d, phi, GaloisGroup(phi)>);
    end for;
    sorted := []; // sorted is a list of equiv classes based on Galois Group
    for phi in newlst do
        for i in [1..#sorted] do
            if IsIsomorphic(phi[4], sorted[i][1][4]) then
                Append(~sorted[i], phi); continue phi; 
            end if;
        end for;
        Append(~sorted, [phi]);
    end for;
    newsorted := [[<s[1], s[2]> : s in equivclass] : equivclass in sorted];
    return newsorted;
end function;



p := 3; n := p;
Zp := pAdicRing(p, 10*p);
Zpx<x> := PolynomialRing(Zp);
a := 1;
phi := x^p - p*x^(p-1) + p*(1+a*p);
d := p^p * (p*(1+a*p))^(p-2) * ((p-1)^p-p*(p-1)^(p-1)+p*(1+a*p));
Valuation(d,p);
Valuation(Discriminant(phi));

/*plist := Polys(p, n);
lst := [f : f in plist | IsEisenstein(f)];
SortByGaloisGroup(p, lst);*/
