 load "JM/Master.magma";
 load "p-adic-extensions.m";

// find nth power residues mod p
function PowerResidues(p, n)
    residues := {};
    for m in [1..p-1] do
        Include(~residues, m^n mod p);
    end for;
    return residues;
end function;

function MyGaloisGroupArray(p)
    error if not IsPrime(p), "p is not prime";
    A := AssociativeArray();
    A[1] := {1..p-1};
    factors := Factorization(p-1);
    for f in factors do
        for i := 1 to f[2] do
            d := f[1]^i;
            res := PowerResidues(p, d);
            if (p-1) mod (2*d) eq 0 then A[d] := res;
            else A[d] := {1..p-1} diff res;
            end if;
            if i ne 1 then A[d] meet:= A[f[1]^(i-1)]; end if;
        end for;
    end for;
    composite_divisors := [d : d in Divisors(p-1) | not IsDefined(A, d)];
    for d in composite_divisors do
        prime_powers := [f[1]^f[2] : f in Factorization(d)];
        res := A[prime_powers[1]];
        for pp in prime_powers[2..#prime_powers] do
            res meet:= A[pp];
        end for;
        A[d] := res;
    end for;
    return A;
end function;

// size of Galois group of phi
// optionally returns the Galois group and defining polynomial
function MyGaloisGroup(p, phi : galois := false, poly := false)
    error if not IsEisenstein(phi), "phi is not Eisenstein";
    A := MyGaloisGroupArray(p);
    disc := Discriminant(PolynomialRing(Integers())!phi); 
    v := Valuation(disc, p);
    l := ((-1)^(p*(p-1) div 2)*(Integers()!disc) mod p^(1+Integers()!v))/p^(Integers()!v);
    j := v - p + 1;
    for d in Divisors(GCD(p-1, j)) do
        if l in A[d] then best := d; end if;
    end for;
    d2 := (p-1) div best; "d2", d2;
    return_list := [* p*d2 *];
    if galois then
        if (j eq p-1) and (l eq p-1) then galois_group := CyclicGroup(p);
        elif j eq p then galois_group := "Cp : Cp-1";
        else
            Cp := CyclicGroup(p); Cd2 := CyclicGroup(d2);
            A := AutomorphismGroup(Cp);
            h := hom< Cd2 -> A | Cd2.1 -> A.2 >;
            galois_group := SemidirectProduct(Cp, Cd2, h);
        end if;
        Append(~return_list, galois_group);
    end if;
    if poly then
        l := Integers()!l;
        a := (-1)^j*(p-l)*InverseMod(j, p) mod p; // coefficient in defining poly
        Zp := pAdicRing(p, 10*p);
        Zpx<x> := PolynomialRing(Zp);
        phi := x^p + a*p*x^j + p;
        Append(~return_list, phi);
    end if;
    return return_list;
end function;

// some errors that have come up:
// runtime error with homomorphism
// should i use (-1)^(p*(p-1)) or AbsoluteValue ?

p := 11;
Zp := pAdicRing(p, 100*p);
Zpx<x> := PolynomialRing(Zp);
// phi := x^5 - 335*x^4 + 490*x^3 + 390*x^2 + 550*x - 420;
Discriminant(PolynomialRing(Integers())!phi);
phi := RandomEisen(p, p, Random(1,p-1), -100, 100); phi;
// phi := x^7 + 231*x^6 - 3234*x^5 - 2009*x^4 - 1764*x^3 + 441*x^2 + 1176*x + 595;
time a1 := MyGaloisGroup(p, phi : galois := true); a1;
time a2 := Eisenstein_Case(phi); a2;
IsIsomorphic(a1[2], a2);
