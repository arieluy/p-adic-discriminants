// Computes the lower convex hull of a set of two-dimensional points.
//
// Input: an enuemrated sequence of <x, y> pairs representing the points.
// Output: a list of vertices of the lower convex hull.
// Implements Andrew's monotone chain algorithm. O(n log n) complexity.
lower_convex_hull := function(points)
    // Sort the points lexicographically (tuples are compared lexicographically).
    // Remove duplicates to detect the case we have just one unique point.
    points := Sort(points);
 
    // Boring case: no points or a single point, possibly repeated multiple times.
    if #points le 1 then
        return points;
    end if;
 
    // 2D cross product of OA and OB vectors, i.e. z-component of their 3D cross product.
    // Returns a positive value, if OAB makes a counter-clockwise turn,
    // negative for clockwise turn, and zero if the points are collinear.
    cross := func<o,a,b | (a[1] - o[1]) * (b[2] - o[2]) - (a[2] - o[2]) * (b[1] - o[1])>;
 
    // Build lower hull 
    lower := [];
    for p in points do
        //while #lower ge 2 and cross(lower[#lower-1], lower[#lower], p) le 0 do  // removes points on lines
        while #lower ge 2 and cross(lower[#lower-1], lower[#lower], p) lt 0 do    // does not remove points on lines
            Prune(~lower);
        end while;
        Append(~lower,p);
    end for;

    return lower;
end function;

// Create the Ramification Polygon of polynomial f
//
// Input:
//   f - an Eisenstein polynomial (correctness of input is not checked)
//   method (optional): "min" the minimum-based definition (default)
//                      "def" the formal definition
//   output (optional): "newton" a NewtonPolyon object (default)
//                      "list" a list of points on the Newton polygon
// Output: 
//   The Newton polygon of the ramificaiton polygon of f (as NewtonPolygon or List)
RamificationPolygon := function(f:method:="min",output:="newton")
    if method eq "def" then
      n := Degree(f);
      k := CoefficientRing(f);
      K<pi> := ext<k|f>;
      KX<X> := PolynomialRing(K);
      F := Evaluate(KX!f,pi*X+pi) div pi^n;
      rp := NewtonPolygon(F);
      c := Vertices(rp)[2..#Vertices(rp)]; // Removes the point at (0,+inf)
      return NewtonPolygon(lower_convex_hull(c));
    end if;
    if method eq "min" then
      n := Degree(f);
      p := Prime(BaseRing(f));
      e := RamificationIndex(BaseRing(f));
      a := Eltseq(f); a := a[2..#a];
      va := [Valuation(ai) : ai in a];
      c := [<1,Min([n*(e*Valuation(k,p)+va[k]-1)+k : k in [1..#va]])>];
      for i in [1..Valuation(n,p)] do
        Append( ~c,<p^i,Min([n*(e*Valuation(Binomial(k,p^i),p)+va[k]-1)+k : k in [p^i..#va]])> );
      end for;
	  
	  // append the horizontal segment if there is tame ramification
      if n gt c[#c][1] then Append(~c,<n,0>); end if;
	  if output eq "list" then
          return lower_convex_hull(c);
      end if;
      return NewtonPolygon(lower_convex_hull(c));
    end if;
	error "Invalid method: use 'min' or 'def'";
end function;

// Create Ramification Polygon from sequence of valuations of f_{p^i}
//
// Input:
//  va - sequence of valuations of f_{p^i}
//   p - prime of our p-adic field
//   j - from discriminant = p^{j+n-1}   (optional)
//   e - ramification index of base ring (optional)
// Output: NewtonPolygon
RamificationPolygonSeq := function(va,p:j:=0,e:=1)
      // If va is the output of most functions, then
      // it lacks the 0 for the monic leading term
      if va[#va] ne 0 then va cat:= [0]; end if;
      n := #va;
      if j eq 0 then
        c := [<1,Min([n*(e*Valuation(k,p)+va[k]-1)+k : k in [1..#va]])>];
      else
        c := [<1,j>];
      end if;
      for i in [1..Valuation(n,p)] do
        Append( ~c,<p^i,Min([n*(e*Valuation(Binomial(k,p^i),p)+va[k]-1)+k : k in [p^i..#va]])> );
      end for;

	  // append the horizontal segment if there is tame ramification
      if n gt c[#c][1] then Append(~c,<n,0>); end if;
	  
      return NewtonPolygon(lower_convex_hull(c));
end function;

// Compute the Ramification Polynomial of f
RamificationPolynomial := function(f)
  n := Degree(f);
  k := CoefficientRing(f);
  K<pi> := ext<k|f>;
  KX<X> := PolynomialRing(K);
  F := Evaluate(KX!f,pi*X+pi) div pi^n;
  return F;
end function;
