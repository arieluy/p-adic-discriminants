// load "p-squared-cubed.m";
load "JM/Master.magma";

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

// Generates a random polynomial
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
    primes := [5];
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

//main();

function SortByGaloisGroup(p, lst)
    newlst := [];
    for phi in lst do
        v := Valuation(Discriminant(phi));
        d := (AbsoluteValue(Integers()!Discriminant(phi)) mod p^(1+Integers()!v))/p^(Integers()!v);
        Append(~newlst, <v-p+1, d, phi, Eisenstein_Case(phi)>);
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
    gen_polys := [[poly[3] : poly in equivclass] : equivclass in sorted];
    galois_size := [[#poly[4] : poly in equivclass] : equivclass in sorted];
    return newsorted;
end function;

// improves readability for the data from SortByGaloisGroup 
function BetterSort(p, lst)
    sorted := [];
    for galois_group in lst do
        new_galois := [<0,[0]>];
        for i := 1 to p do
            value_list := [];
            for tup in galois_group do
                if tup[1] eq i then Append(~value_list, tup[2]); end if;
            end for;
            if value_list ne [] then Append(~new_galois, <i, (value_list)>); end if;
        end for;
        Append(~sorted, new_galois[2..#new_galois]);
    end for;
    return sorted;
end function;

procedure MakeArray(lst)
    for p in lst do
        "\n"; p;
        n := p;
        plist := Polys(p, n);
        lst := [f : f in plist | IsEisenstein(f)];
        BetterSort(p, SortByGaloisGroup(p, lst));
    end for;
end procedure;
