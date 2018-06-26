// from Chad Awtrey

NumberFieldAutomorphismGroup := function(poly)
  Zx<x> := PolynomialRing(Integers());
  E<r> := NumberField(poly);
  Ey<y> := PolynomialRing(E);
  phi := Ey ! poly;
  roo := [j[1] : j in Roots(phi)];
  Sn := Sym(#roo);
  auts := [hom<E->E | j> : j in roo];
  perms := [[Index(roo,j(i)):i in roo]:j in auts];
  return [Sn ! j : j in perms];
end function;


SplittingFieldAutomorphismGroup := function(poly) // can be slow
  Zx<x>:= PolynomialRing(Integers());
  E<r> := NumberField(poly);
  Ey<y> := PolynomialRing(E);
  phi := Ey ! poly;
  roo := [j[1] : j in Roots(phi)];
  if #roo eq Degree(poly) then 
    n := #roo;
    sn := Sym(n);
    auts := [hom<E->E | j> : j in roo];
    perms := [[Index(roo,j(i)):i in roo]:j in auts];
    return [sn ! j : j in perms]; end if;
  S<t> := SplittingField(poly);
  Sz<z> := PolynomialRing(S);
  split := Sz ! DefiningPolynomial(S);
  psi := Sz ! poly;
  roo := [j[1] : j in Roots(psi)];
  sroo := [j[1] : j in Roots(split)];
  sn := Sym(#roo);
  auts := [hom<S->S | j> : j in sroo];
  perms := [[Index(roo,j(i)):i in roo]:j in auts];
  return [sn ! j : j in perms];
end function;


LinearResolventGroup := function(n,k);
  return DirectProduct(Sym({1..k}),Sym({k+1..n}));
end function;


ResolventFactorDegrees := function(X,H,G)
  a,b,c := CosetAction(X,H);
  orbs := Orbits(a(G));
  return Sort([#j : j in orbs]);
end function;


GaloisGroupsOfSubfields := function(G:deg:=0)
  G1 := Stabilizer(G,1);
  sgroups := [j`subgroup :j in Subgroups(G)|#j`subgroup lt #G];
  sfields := [j : j in sgroups | G1 subset j and #j gt #G1 and #j lt #G];
  actions := [CosetImage(G,j):j in sfields];
  degs := [Degree(j) : j in actions];
  ids := [TransitiveGroupIdentification(j) : j in actions];
  ParallelSort(~degs,~ids);
  subs := [[degs[j],ids[j]] : j in [1..#degs]];
  if deg eq 0 then return subs; end if;
  return [j : j in subs | j[1] eq deg];
end function;


IsSeparablePoly := function(poly)
  return GCD(poly,Derivative(poly)) eq 1;
end function;


Tschirnhaus := function(poly)
  Zx<x> := PolynomialRing(Integers());
  phi := Zx ! poly;
  E<r> := NumberField(phi);
  return Zx ! MinimalPolynomial(r^2+r+1);
end function;


SumZeros := function(poly1,poly2)
  Zx<x> := PolynomialRing(Integers());
  Zyz<y,z> := PolynomialRing(Integers(),2);
  return Zx ! UnivariatePolynomial(Resultant(Zyz ! Evaluate(poly1,z), Zyz ! Evaluate(poly2,y-z),z));
end function;


MultiplyZeros := function(poly,d)
  Zx<x> := PolynomialRing(Integers());
  if d eq 0 then return x^Degree(poly); end if;
  Qy<y> := PolynomialRing(Rationals());
  return Zx ! (d^Degree(poly)*Evaluate(Qy ! poly,y/d));
end function;


PolynomialRoot := function(poly,k)
  Zx<x> := PolynomialRing(Integers());
  phi := Zx ! poly;
  if k eq 1 then return phi; end if;
  t := phi div GCD(phi,Derivative(phi));
  r := t;
  s := phi;
  while Degree(r) lt Degree(phi)/k do
    s := Zx ! (s/(t^k));
    t := GCD(s,t);
    r := t*r; end while;
  return Zx ! r;
end function;


DoublePoly := function(poly)
  Zx<x> := PolynomialRing(Integers());
  Qy<y> := PolynomialRing(Rationals());
  res := (Zx ! SumZeros(poly,poly)) / (Zx ! MultiplyZeros(poly,2));
  return PolynomialRoot(res,2);
end function;


LinRes2 := function(poly,a,b)
  Zx<x>:= PolynomialRing(Integers());
  return (Zx ! (SumZeros(MultiplyZeros(poly,a),MultiplyZeros(poly,b))/MultiplyZeros(poly,a+b)));
end function;


TriplePoly := function(poly)
  Zx<x> := PolynomialRing(Integers());
  return (Zx ! (PolynomialRoot(SumZeros(DoublePoly(poly),poly)/LinRes2(poly,1,2),3)));
end function;


LinRes112 := function(poly)
  Zx<x> := PolynomialRing(Integers());
  return (Zx ! (SumZeros(DoublePoly(poly),MultiplyZeros(poly,2))/LinRes2(poly,1,3)));
end function;


QuadPoly := function(poly)
  Zx<x> := PolynomialRing(Integers());
  return (Zx ! (PolynomialRoot(SumZeros(TriplePoly(poly),poly)/LinRes112(poly),4)));
end function;


DegreesOfFactors := function(fac)
  return [Degree(j[1]) : j in fac];
end function;


SquareFreeDoublePoly := function(poly)
  phi := poly;
  res := DoublePoly(phi);
  isok := IsSeparablePoly(res);
  while (isok eq false) do
    phi := Tschirnhaus(phi);
    res := DoublePoly(phi);
    isok := IsSeparablePoly(res); end while;
  return res;
end function;


SquareFreeTriplePoly := function(poly)
  phi := poly;
  res := TriplePoly(phi);
  isok := IsSeparablePoly(res);
  while (isok eq false) do
    phi := Tschirnhaus(phi);
    res := TriplePoly(phi);
    isok := IsSeparablePoly(res); end while;
  return res;
end function;


SquareFreeQuadPoly := function(poly)
  phi := poly;
  res := QuadPoly(phi);
  isok := IsSeparablePoly(res);
  while (isok eq false) do
    phi := Tschirnhaus(phi);
    res := QuadPoly(phi);
    isok := IsSeparablePoly(res); end while;
  return res;
end function;


IndexTwoSubfields := function(poly)
  n := Degree(poly);
  res := SquareFreeDoublePoly(poly);
  fac := Factorization(res);
  return [j[1] : j in fac | Degree(j[1]) eq (n/2)];
end function;


IndexThreeSubfields := function(poly)
  n := Degree(poly);
  res := SquareFreeTriplePoly(poly);
  fac := Factorization(res);
  return [j[1] : j in fac | Degree(j[1]) eq (n/3)];
end function;


IndexFourSubfields := function(poly)
  n := Degree(poly);
  res := SquareFreeQuadPoly(poly);
  fac := Factorization(res);
  return [j[1] : j in fac | Degree(j[1]) eq (n/4)];
end function;
