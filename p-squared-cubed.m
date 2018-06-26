// from Chad Awtrey

// Generates extensions of degree p^2
CyclicDegreePSquared := function(p,Zp)
    Zpx<x> := PolynomialRing(Zp);
    pols := [];
    for b in [0..p-1] do for a in [0..p-1] do
        pols := pols cat [x^(p^2)+b*p^2*x^(p^2-1)+p^2*x^(p^2-2)+p*(p-1)*x^(p*(p-1))+(p-1)*p^2*x^(p*(p-1)-1)+a*p^3+p+p^2*(p-1-b)]; end for; end for;
    return v;
end function;

// Generates extensions of degree p^3
CyclicDegreePCubed := function(p,Zp)
    Zp<x> := PolynomialRing(Zp);
    pols := [];
    for a in [0..p-1] do for b in [0..p-1] do for c in [0..p-1] do 
      if b lt p-1 then bb := p^3*(p-2-b); end if; 
      if b eq p-1 then bb:=p^4-p^3; end if; 
        Append(~pols,x^(p^3) + a*p^3*x^(p^3-1) + bb*x^(p^3-2) + b*p^2*x^(p^3-p) + p^3*x^(p^3-p-1) + (p^4-2*p^3)*x^(p^3-p-2) + p^2*x^(p^3-2*p) + 2*p^3*x^(p^3-2*p-1) + (p^2-p)*x^(p^3-p^2) + b*p^3*x^(p^3-p^2-1) + p^3*x^(p^3-p^2-2) + (p^3-p^2)*x^(p^3-p^2-p) + (p^4-p^3)*x^(p^3-p^2-p-1) + p + (p-1-b)*p^2 + (p-1-a)*p^3 + c*p^4);
      end for; end for; end for;
    return pols;
end function;