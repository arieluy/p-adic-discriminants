// from Brian Sinclair

//
// ENUM.M - Enumerate all extensions given additional invariants
//
//////////////////////////////////////////////////////////////////
// load "rampol-enum.m";
//////////////////////////////////////////////////////////////////


//
// RAMPOL-ENUM.M - Enumerate possible ramificaiton polygons
//

//////////////////////////////////////////////////////////////////
//load "rampol.m";

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
intrinsic RamificationPolygon(f:method:="min",output:="newton") -> .
{Input: f - an Eisenstein polynomial (correctness of input is not checked) method (optional): "min" the minimum-based definition (default) "def" the formal definition output (optional): "newton" a NewtonPolyon object (default) "list" a list of points on the Newton polygon. Output: The Newton polygon of the ramificaiton polygon of f (as NewtonPolygon or List)
}    
    
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
end intrinsic;

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
intrinsic RamificationPolynomial(f:RngPolElt) -> .
{The ramification polynomial of an Eisienstein  polynomial over a local ring.}
  n := Degree(f);
  k := CoefficientRing(f);
  K<pi> := ext<k|f>;
  KX<X> := PolynomialRing(K);
  F := Evaluate(KX!f,pi*X+pi) div pi^n;
  return F;
end intrinsic;


//////////////////////////////////////////////////////////////////
// Current Ramificaiton Polygon
// used to hold data for building ramification polygons
CRP := recformat<
  K : RngPad,
  p : Integers(),   // prime of our p-adic field
  rpolyg : SeqEnum, // Current Vertices of our ramificaiton polygon
  lowerv : SeqEnum, // lower bound for valuations of f_{i}
  fixedv : SeqEnum, // list of fixed valuations of f_{p^i} (as points <i,v(f_p^i)>
  points : BoolElt  // true if we list all points, false for vertices only
                    // (lowerv will be higher to avoid unlisted points on lines if true)
>;

// Compute lower bound for valuations of all f_{p^i} due to point (p^s,y)
// Input:
//  s - abcissa p^s to consider
//  y - valuation of ramification polygon above p^s : v(c_{p^s})
//  p - prime of p-adic field
//  n - degree of polynomial
// Output: l(i,s) as SeqEnum
lfunc := function(s,y,K,n)
  as,bs := Quotrem(Integers()!y,Integers()!n);
  p := Prime(K);
  L := [];
  for i in [1..n-1] do
    if i mod p^s ne 0 then
      Append(~L,1);
    elif i lt bs then
      Append(~L, Max(2+as-Valuation(K!Binomial(i,p^s)),1) );
    else
      Append(~L, Max(1+as-Valuation(K!Binomial(i,p^s)),1) );
    end if;
  end for;
  return L;
end function;

// Compute lower bound for valuations due to no point above p^k
// Input:
//  k - abcissa p^k to consider
//  lvert,rvert - left and right endpoints of segment over p^k
//  p - prime of p-adic field
//  n - degree of polynomial
lnvfunc := function(k,lvert,rvert,K,n:colinear:=false)
  // Find the lower bound for valuations of f due to no point above p^k
  // above a segment with given left and right vertices
  slope := (lvert[2]-rvert[2])/(lvert[1]-rvert[1]);
  p := Prime(K);
  L := [];
  for i in [1..n-1] do
    if i mod p^k ne 0 then
      Append(~L,1);
    else
      mv := (1/n)*(slope*(p^k-lvert[1])+lvert[2]-i)+1-Valuation(K!Binomial(i,p^k));
      // So that we separate cases to include points on lines
      if colinear and mv in Integers() then
        Append(~L,mv+1);
      else
        Append(~L,Ceiling(mv));
      end if;
    end if;
  end for;
  return L;
end function;

//
// AllRamificationPolygonsSub
//

// Find all possible values for ramification polygon point above p^s given current polygon
// Input:
//  crp - current ramificaiton polygon
//   s  - abcissa p^s to consider
AllRamificationPolygonsSub := function(crp,s)
    // Get the degree of the polynomial from the lower bound length
    n := #crp`lowerv + 1;
    // Get j from the point <1,j>
    j := crp`rpolyg[1][2];

    // We know the point above p^0 to be <1,j> so we are almost done.
    if s eq 0 then
      // Check that missing vertices are acceptable
      missing := Valuation(crp`K!crp`rpolyg[#crp`rpolyg][1])-1;
      if missing gt 0 then      
        for k in [1..missing] do
          // Check that we can have a point above the line with current fixed valuations
          fbound := Min([n*(Valuation(crp`K!Binomial(crp`fixedv[iter][1],crp`p^k))+crp`fixedv[iter][2]-1)+crp`fixedv[iter][1] : iter in [1..#crp`fixedv] | crp`fixedv[iter][1] ge crp`p^k]);
          crossing := (j-crp`rpolyg[#crp`rpolyg][2])/(1-crp`rpolyg[#crp`rpolyg][1])*(crp`p^k-1)+j;
          if fbound lt crossing then
            // Upper bound is below the current segment
            return [];
          end if;
          
          // Find the lower bound for valuations of f due to no point above p^k
          Lnv := lnvfunc(k,<1,j>,crp`rpolyg[#crp`rpolyg],crp`K,n:colinear:=crp`points);
          for i in [1..#Lnv] do
            crp`lowerv[i] := Max([crp`lowerv[i],Lnv[i]]);
          end for;
        end for;
      end if;
      return [crp];
    end if;

    // Handle the case of s gt 0
    
    lastvert := crp`rpolyg[#crp`rpolyg];
    
    // Lower bound based on current minimum valutions
    minbound := Min([n*(Valuation(crp`K!Binomial(k,crp`p^s))+crp`lowerv[k]-1)+k : k in [crp`p^s..#crp`lowerv]] cat [n*(Valuation(crp`K!Binomial(n,crp`p^s)))]);

    // Lower bound based on last added segment
    slope := func<a,b| (a[2]-b[2])/(a[1]-b[1])>;
    if crp`rpolyg[#crp`rpolyg][2] gt 0 then
      segbound := Floor( (lastvert[2]-crp`rpolyg[#crp`rpolyg-1][2])/(lastvert[1]-crp`rpolyg[#crp`rpolyg-1][1]) * (crp`p^s-lastvert[1])+lastvert[2] );
      segbound +:= (crp`p^s - segbound mod crp`p^s);
    else segbound := crp`p^s;
    end if;

    // Upper bound based on current fixed valuations (This assumes that <n,0> is present in fixedv)
    fbound := Min([n*(Valuation(crp`K!Binomial(crp`fixedv[k][1],crp`p^s))+crp`fixedv[k][2]-1)+crp`fixedv[k][1] : k in [1..#crp`fixedv] | crp`fixedv[k][1] ge crp`p^s]);

    // Upper bound based on segment <1,j> to lastvert <p^u,y_u> (only applies to vertices of polygon)
    ubound := j - ( (j-crp`rpolyg[#crp`rpolyg][2])/(crp`rpolyg[#crp`rpolyg][1]-1) )* (crp`p^s-1);
    // The following insures that we do not choose a y value on the segment
    if not crp`points and ubound in Integers() then ubound -:= 1;
    else ubound := Floor(ubound);
    end if;
    
    lowerbound := Max(minbound,segbound);
    upperbound := Min(ubound,fbound);
    possibley := [lowerbound..upperbound by crp`p^s];

    // Handle the trivial no vertex case
    
    if lowerbound gt ubound then
      // There is no possible vertex with the current valuation lower bounds.
      return $$(crp,s-1);
    end if;

    // Handle the non-trivial cases

    // Always pass the current polygon forward.
    crps := [crp];
    
    for y in possibley do
      as,bs := Quotrem(Integers()!y,Integers()!n);
      L := lfunc(s,y,crp`K,n);
      
      // CHECK THE VALIDITY OF THIS Y-VALUE
      
      polygon_is_okay := true;

      // Check that any previous "no vertex" choices work.
      missing := Valuation(crp`K!crp`rpolyg[#crp`rpolyg][1])-s-1;
      if missing gt 0 then
        slope := (y-crp`rpolyg[#crp`rpolyg][2])/(crp`rpolyg[#crp`rpolyg][1]-crp`p^s);
        for k in [s+1..s+missing] do
          // Upper bound based on current fixed valuations (This assumes that <n,0> is present in fixedv)
          fbound := Min([n*(Valuation(crp`K!Binomial(crp`fixedv[iter][1],crp`p^k))+crp`fixedv[iter][2]-1)+crp`fixedv[iter][1] : iter in [1..#crp`fixedv] | crp`fixedv[iter][1] ge crp`p^k]);
          crossing := (y-crp`rpolyg[#crp`rpolyg][2])/(crp`p^s-crp`rpolyg[#crp`rpolyg][1])*(crp`p^k-crp`p^s)+y;
          if fbound lt crossing then
            polygon_is_okay := false;
            break;
          end if;
          
          if polygon_is_okay then
            // Find the lower bound for valuations of f due to no point above p^k
            Lnv := lnvfunc(k,<crp`p^s,y>,crp`rpolyg[#crp`rpolyg],crp`K,n:colinear:=crp`points);

            // Check that lnv(i,s) doesn't conflict with fixed valuations
            for i in [1..#Lnv] do
              if Lnv[i] gt crp`lowerv[i] and Index([fx[1]:fx in crp`fixedv],i) gt 0 then
                // Increasing minimum valuation at fixed valuation - discard this polygon
                polygon_is_okay := false;
                break;
              end if;
            end for;
          end if;

          // If this missing point is okay, then increase lower bounds
          if polygon_is_okay then
            for i in [1..#Lnv] do
              L[i] := Max([crp`lowerv[i],Lnv[i],L[i]]);
            end for;
          end if;
        end for;
      end if;
      
      if bs gt 0 and crp`lowerv[bs] gt L[bs] then
        // L[bs] is less than current lower bound
        polygon_is_okay := false;
      end if;

      // Final check - Do the valuations prescribed by this point actually generate it?
      if polygon_is_okay then
        for i in [1..#L] do
          L[i] := Max([crp`lowerv[i],L[i]]);
        end for;
        ycheck := Min([n*(Valuation(crp`K!Binomial(k,crp`p^s))+L[k]-1)+k : k in [crp`p^s..#L]] cat [n*(Valuation(crp`K!Binomial(n,crp`p^s)))]);
        if y ne ycheck then
          // Prescribed valuations do not generate this y value - discard this polygon
          polygon_is_okay := false;
        end if;
      end if;
      
      // If y passes all checks, add the point <p^s,y>
      if polygon_is_okay then      
        // Add a fixed val (if bs ne 0), update our lower bounds, and point to RP
        newcrp := crp;
        if bs ne 0 then
          // If bs eq 0, then we do not add a new fixed valuation, as <n,0> defined it.
          Append(~newcrp`fixedv,<bs,L[bs]>);
        end if;
        newcrp`lowerv := L;
        Append(~newcrp`rpolyg,<crp`p^s,y>);
        Append(~crps,newcrp);
      end if;
    end for;

    // We need to return a flat list of all CRPs
    retrcrps := [];
    for i in [1..#crps] do
      retrcrps cat:= $$(crps[i],s-1);
    end for;
    return retrcrps;
end function;

//
// AllRamificationPolygons
//

// Find all possible values for ramification polygon point above p^i given current polygon
// Input:
//  n - degree of polynomial
//  p - prime of our p-adic field
//  j - discriminant p^{n+j-1}
//  output - (optional) "polygons" or "crps"
//  points - (optional) true to find all points, false for just vertices
intrinsic AllRamificationPolygons(K::RngPad,n,j:output:="polygons",points:=true) -> .
{Find all possible values for ramification polygon point above p^i given current polygon.  Input: n - degree of polynomial, p - prime of our p-adic field,j - discriminant p^(n+j-1). Output - (optional) "polygons" or "crps" points - (optional) true to find all points, false for just vertices}

    // Check that choice of j satisfies Ore's Conditions
    if not OreConditions(K,n,j) then
      error "Choice of discriminant fails Ore's Conditions.";
    end if;
    p := Prime(K);
    
    // Set up valuation lower bounds based on <1,j>
    a,b := Quotrem(Integers()!j,Integers()!n);
    L := lfunc(0,j,K,n);

    // Initialize fixed valuations based on <1,j>,<n,0>
    fixedv := [<n,0>];
    if b gt 0 then Append(~fixedv,<b,L[b]>); end if;

    // Handle the trivial case of n = p
    if n eq p then
      if output eq "crps" then
        crp := rec< CRP | K := K, p := p, rpolyg := [<1,j>,<n,0>], lowerv := L, fixedv := fixedv, points := true>;
        return [[crp]];
      else
        return [[<1,j>,<n,0>]];
      end if;
    end if;

    // Call the recursive step starting at p^{r-1}
    r := Valuation(n,p);
    if n eq p^r then
      crp := rec< CRP | K := K, p := p, rpolyg := [<1,j>,<n,0>], lowerv := L, fixedv := fixedv, points:=points>;
    else
      if points then
        rpolyg := [<1,j>,<n,0>] cat [<i,0> : i in [n-1..p^r+1 by -1] | Valuation(Binomial(n,i),p) eq 0] cat [<p^r,0>];
        crp := rec< CRP | K := K, p := p, rpolyg := rpolyg, lowerv := L, fixedv := fixedv, points:=true>;
      else  
        crp := rec< CRP | K := K, p := p, rpolyg := [<1,j>,<n,0>,<p^r,0>], lowerv := L, fixedv := fixedv, points:=false>;
      end if;
    end if;
    crps := AllRamificationPolygonsSub(crp,Valuation(n,p)-1);

    // Sort the polygons for presentation
    if output eq "polygons" then
      polygons := [];
      for i in [1..#crps] do
        Sort(~crps[i]`rpolyg);
        Append(~polygons,crps[i]`rpolyg);
      end for;
      return polygons;//crps;
    elif output eq "crps" then
      for i in [1..#crps] do
        Sort(~crps[i]`rpolyg);
        Sort(~crps[i]`fixedv);
      end for;
      return crps;
    end if;
end intrinsic;


//
//  DIAGNOSTIC FUNCTIONS
//


CheckCrp := function(crp)
  rp := RamificationPolygonSeq(crp`lowerv,crp`p);
  return Vertices(rp) eq crp`rpolyg;
end function;

// Create Example Polynomial f with a given ramification polygon (input as a CRP)
// Input: crp - a crp to create an example of
// Output: list of coefficients of f (ready to be coerced into a PolynomialRing
ExamplePolyFromCRP := function(crp)
    L := [1] cat crp`lowerv cat [0];
	return [crp`p ^ i : i in L];
end function;



//////////////////////////////////////////////////////////////////
// load "resseg-enum.m";
//////////////////////////////////////////////////////////////////

//
// RESSEG-ENUM.M - Enumerate possible residual polynomials of segments
//

// AllResidualPolynomials
// INPUT:  k   - a p-adic field
//         R   - a ramification polygon
//       phi_0 - constant term of generating polynomial ( can this be made optional ? only needed for linked coeffs )
// OUTPUT: A   - List of possible [_A_] given inputs

intrinsic AllResidualPolynomials(k,R,phi_0) -> .
{INPUT:  k is a p-adic field, R is a ramification polygon, phi_0 is the constant term of generating polynomial.
OUTPUT: A list of possible of representatives of residual polynomial classes [_A_] given inputs.}
    //print Valuation(k!phi_0);
    if Valuation(k!phi_0) ne 1 then
        error "Valuation of phi_0 must be 1";
    end if;
    
    // PHASE ZERO - INITIALIZE DATA
    
    K := FieldOfFractions(k);  // in case we pass a pAdicRing to the function
    ok := RingOfIntegers(K);
    rk := ResidueClassField(ok);
    rkz := PolynomialRing(rk);
    n := R[#R][1];
    
    phi_0 := K!(phi_0);
    
    // Initialize a and b lists
    a := []; b := [];
    for pt in R do
        q,r := Quotrem(pt[2],n);
        Append(~a,q);
        Append(~b,r);
    end for;
    
    // PHASE ONE - ASSIGN RESIDUES TO EACH POINT OF THE POLYGON
    
    // Initialize Aijs using the first point
    if b[1] eq 0 then
        // First point is linked to monic leading term
        binomt := Binomial(n,R[1][1]);
        deltap := ( K!(-phi_0) )^(-a[1]);
        Aijs := [[rk!(K!( binomt * deltap ))]];
    else
        // First point is free
        Aijs := [[i] : i in rk | i ne 0];
    end if;
    
    while Min([#A : A in Aijs]) lt #R do
        // Pop A of the front of Aijs
        A := Aijs[1];
        Aijs := Aijs[2..#Aijs];
        
        // find the index for the next point
        s := #A+1;

        // If this is a linked coeff, assign it's value,
        // Else it is free.
        if b[s] eq 0 then
            if R[s][1] eq n then
                // This is the monic leading term
                Append(~Aijs,Append(A,1));
            else
                // This term is linked to the monic leading term
                //print "linked to leading term";
                //binomt := Binomial(n,R[s][1])^(-1);  // WRONG
                //deltap := ( (-phi_0) )^(a[s]);
				binomt := Binomial(n,R[s][1]);         // Corrected
                deltap := ( K!(-phi_0) )^(-a[s]);
                Append(~Aijs,Append(A,rk!(k!( binomt * deltap ))));
            end if;
        elif b[s] in b[1..s-1] then
            // This term is linked to a previous term
            // Bin(b,pst)^(-1) * Bin(b,psq) * (d0)^(at-aq) * Aq  // THIS IS WRONG
            // Bin(b,pst) * Bin(b,psq)^(-1) * (d0)^(aq-at) * Aq  // Corrected		
            //print "linked coeff";
            at := a[s];
            aq := a[Index(b,b[s])];
            // binomt := Binomial(b[s],R[s][1])^(-1);  // WRONG
            // binomq := Binomial(b[s],R[Index(b,b[s])][1]);
            // deltap := ( (-phi_0) )^(at-aq);
            binomt := Binomial(b[s],R[s][1]);          // Corrected
            binomq := Binomial(b[s],R[Index(b,b[s])][1])^(-1);
            deltap := ( (-phi_0) )^(aq-at);
            LinkedA := rk!(k!( binomt * binomq * deltap )) * A[Index(b,b[s])];
            //print binomt,binomq,deltap,A[Index(b,b[s])];
            Append(~Aijs,Append(A,LinkedA));
        else
            // This term is free
            //print "free coeff";
            for i in [i : i in rk | i ne 0] do
                Append(~Aijs,Append(A,i));
            end for;
        end if;
    end while;

    //print "Aijs",Aijs;
    
    // PHASE TWO - CONSTRUCT POLYNOMIALS USING THOSE RESIDUES
    
    //S := [1] cat [R[i][1] : i in [2..#R-1] | allslopes[i] ne allslopes[i-1]] cat [R[#R][1]];
    allslopes := [ -( (R[i+1][2]-R[i][2]) / (R[i+1][1]-R[i][1]) ) : i in [1..#R-1]];
    Sindex := [1] cat [i : i in [2..#R-1] | allslopes[i] ne allslopes[i-1]] cat [#R];
    S := [R[i][1] : i in Sindex];
    slopes := [allslopes[i] : i in Sindex[1..#Sindex-1]];
    h := [-Numerator(s) : s in slopes];
    e := [Denominator(s) : s in slopes];

    //print "Sindex",Sindex;
    //print "S",S;
    //print slopes;

    Aflat := [];
    for aij in Aijs do
        ThisA := <>;
        for i in [1..#S-1] do
            // RKz![res(rhol[Integers()!(j*e[r]+rpv[r][1])] div (K.1)^(-Integers()!(j*h[r]-rpv[r][2]))) : j in [0..Integers()!(d[r]/e[r])]]);
            deg := Integers()!((S[i+1]-S[i])/e[i]);
            respoly := [Zero(rk) : cnt in [0..deg]];
            //for j in segs[i] do
            for j in [Sindex[i]..Sindex[i+1]] do
                term := Integers()!( (R[j][1]-S[i])/e[i] );
                //print "term",<i,j>,aij[j],"* z ^",term;
                respoly[term+1] := rk!aij[j];
            end for;
            Append(~ThisA,Polynomial(rk,respoly));
        end for;
        Append(~Aflat,ThisA);
    end for;
    
    return Aflat;
    
    // PHASE THREE - PARTITION POLYNOMIAL SETS INTO CLASSES  --- NOT IMPLEMENTED
    
end intrinsic;




//////////////////////////////////////////////////////////////////
// used to hold polynomials and invariants
//////////////////////////////////////////////////////////////////
FRP := recformat<
K : RngPad,       // base field
deg,              // degree pf extensions
j,                // discriminant exponent j
rampol,           // ramification polygon
phi0,             // constant coefficient modulo pi^2
A,                // residual polynomials
generators        // gernerating polynomials of extensions
>;

intrinsic DistinctConstantCoefficients(K::RngPad,n::RngIntElt) -> .
{The possible constant coefficients of extensions of K of degree n, that
yield distinct extensions}
    //K is base field, n is degree of polynomial.  n can be recovered from polygon.

    p:=Prime(PrimeRing(K));

    m:=Valuation(n,p);

    if (n eq p^m) then
        return {p};
    else
        _K_,vk:=ResidueClassField(K);    //vk is Mapping from: RngPad: K to FldFin: _K_

        Kx,vkx:=UnitGroup(_K_);        //vkx is Mapping from: GrpAb: Kx to FldFin: _K_

        if IsCyclic(Kx) then

            a:=Setseq(Generators(Kx))[1];
            den:=sub<Kx|n*a>;

            S,vS:=quo<Kx |den>;      //vS is Mapping from: GrpAb: Kx to GrpAb: S.  

            //Correct to here.

            Delta:={(vkx(s@@vS))@@vk  :s in S};   //Map each element of S to K (through _K_ and Kx)

            return {delta*p: delta in Delta};
        else
            
            error "Error: Something has gone terribly wrong.";
        end if;
        
    end if;        
end intrinsic;


Minval := function(k,R)
    // Find the minimum valuations prescribed by the ramification polygon R

    n := R[#R][1];
    K  := RingOfIntegers(k);
    p := Prime(K);
    xes := [pt[1] : pt in R];

    Lpt := [lfunc(Valuation(K!pt[1]),pt[2],K,n) : pt in R];
    for s in [1..Valuation(n,p)] do
        if p^s notin xes then
            left := #[x : x in xes | x lt p^s];
            Append(~Lpt,lnvfunc(s,R[left],R[left+1],K,n:colinear:=true));
        end if;
    end for;
    minval := [];
    for i in [1..n-1] do
        Append(~minval,Max([1] cat [l[i] : l in Lpt]));
    end for;
    return minval;
end function;

intrinsic AllTotallyRamifiedExtensions(k::RngPad,R::SeqEnum,A,delta_0:CountOnly:=false,TemplateOnly:=false) -> .
{All extension of pi-adic ring or field k with give invariants:
R - points of a ramification polygon, as [<x,y>], 
A - list of residual polynomials for segments of R,
delta_0 - a representative of a class in RK*/(RK*)^n
}
    n  := R[#R][1];
    K  := RingOfIntegers(k);
    Kx := PolynomialRing(K);
    BK := BaseRing(K);
    
    // integral prime
    p := Prime(K);
    pi := UniformizingElement(K);

    // Define Resdidue Class Field of K
    RK := ResidueClassField(K);
    RKz:= PolynomialRing(RK);
    
    // Set up vector space to find quotient with images of Sm
    k_is_base := K eq BK;
    if not k_is_base then
        RBK := ResidueClassField(BK);
        V,Vm := VectorSpace(RK,RBK);
    end if;
    
    // Take R, and find xes[], a[], b[] s.t. <x,y> eq <x,an+b>
    a := []; b := [];
    xes := [pt[1] : pt in R];
    for pt in R do
        q,r := Quotrem(pt[2],n);
        Append(~a,q);
        Append(~b,r);
    end for;
    
    // Find the denominators of the slopes of segments
    allslopes := [ -( (R[i+1][2]-R[i][2]) / (R[i+1][1]-R[i][1]) ) : i in [1..#R-1]];
    Sindex := [1] cat [i : i in [2..#R-1] | allslopes[i] ne allslopes[i-1]] cat [#R];
    S := [R[i][1] : i in Sindex];
    slopes := [allslopes[i] : i in Sindex[1..#Sindex-1]];
    //slopes := [-((R[Index(xes,S[i+1])][2]-R[Index(xes,S[i])][2]) / (S[i+1]-S[i])) : i in [1..#S-1]];
    h := [Numerator(s) : s in slopes];
    e := [Denominator(s) : s in slopes];
    
    // Find the minimum valuations prescribed by the RP
    minval := Minval(K,R);

    // 1. Set Krasner Bound
    c := Ceiling(1+2*a[1]+(2*b[1])/n)-1;   // J_0 is a[1]n+b[1] (magma indexes from 1)

    // Precompute n*Hasse-Herbrand of RP
    m := 1;
    nhhr := [Min([pt[2] : pt in [<pt[1],pt[2]+pt[1]> : pt in R]])];
    while nhhr[#nhhr] lt n*c-1 do
        m +:= 1;
        Append(~nhhr,Min([pt[2] : pt in [<pt[1],pt[2]+m*pt[1]> : pt in R]]));
    end while;
    
    // 2. Initialize Template
    tau := [];
    for i in [1..n] do
        Append(~tau,[{Zero(RK)} : j in [1..c]]);
     end for;
    
    // 3. Set Free Choices (respecting ell)
    free_choices := [];
    //reducedzeros := ([<hhm mod n,(n-(hhm mod n)+hhm)/n> : hhm in nhhr | (n-(hhm mod n)+hhm) mod n eq 0]);
    // correcting for indexing from 1:
    reducedzeros := ([<(hhm mod n)+1,(n-(hhm mod n)+hhm)/n> : hhm in nhhr | (n-(hhm mod n)+hhm) mod n eq 0]);
    for i in [1..n] do
        for j in [1..c] do
            if <i,j> notin reducedzeros and (i eq 1 or j ge minval[i-1]) then
                tau[i][j] := Set(RK);
                if i gt 1 and j gt 1 then
                    Append(~free_choices,<i,j>);
                end if;
            end if;
        end for;
    end for;
    
    // 4. Set coefficients by Sm
    non_surjective_m := [];
    non_surjective_cell := [];
    surjective_s_places := [];
    for m in [1..Floor((R[1][2]-R[2][2])/(R[2][1]-1))] do
        i := nhhr[m] mod n;
        if (n-i+nhhr[m]) mod n eq 0 then
            j := (n-i+nhhr[m]) div n;
            if m notin slopes then
                tau[i+1][j] := {Zero(RK)};
                Append(~surjective_s_places,<i+1,j>);
            else
                image := {Evaluate(Parent(A[1]).1^S[Index(slopes,m)]*A[Index(slopes,m)],gamma) : gamma in RK};
                if image eq Set(RK) then
                    //print m,"is in slopes, Sm is surjective, so",<i+1,j>,"gets 0.",image;
                    tau[i+1][j] := {Zero(RK)};
                    Append(~surjective_s_places,<i+1,j>);
                else
                    //m,Index(slopes,m),slopes,S[Index(slopes,m)],A[Index(slopes,m)];
                    //print m,"is in slopes, Sm not surjective!",image;
                    if k_is_base then
                        tau[i+1][j] := Set(RK);
                    else
                        q,qm := quo<V|[Vm(i):i in image]>;
                        tau[i+1][j] := {Inverse(Vm)(Inverse(qm)(i)):i in q};
                    end if;
                    Append(~non_surjective_m,m);
                    Append(~non_surjective_cell,<i+1,j>);
					// FIX ME: Record the cokernal for possible reduction
                end if;
            end if;
        end if;
    end for;
    
    // 5. Set coefficients by A
    for i in [1..#R] do
        if b[i] ne 0 then
            seg := #[cnt : cnt in S | cnt le R[i][1]];
            j := a[i] + 1 - Valuation(Binomial(b[i],R[i][1]),p);
            tau[b[i]+1][j] := { Coefficient(A[seg],(R[i][1]-S[seg]) div e[seg]) * (-delta_0)^(a[i]+1) * RK!(Binomial(b[i],xes[i])^(-1) * pi^(Valuation(K!(Binomial(b[i],xes[i]))))) };
            // Remove from list of free choices
			Exclude(~free_choices,<b[i]+1,j>);
        end if;
    end for;
    
    // 6. Set tau_{0,1} to delta_0
    tau[1][1] := {delta_0};
    if TemplateOnly then
       return tau;
    end if;

    // 7. Construct list of polynomials
    if CountOnly then
        L := &*[ &*[#cell : cell in row] : row in tau];
    else
        cp := CartesianProduct([CartesianProduct(i):i in tau]);
        L := [Kx.1^n + &+[ Kx.1^(i-1)*&+[K!tup[i][j]*pi^j : j in [1..#tup[i]]] : i in [1..#tup]] : tup in cp];
    end if;

    // 7.5 Postprocess if reduction may be needed
    need_filter := true;
    if #non_surjective_cell eq 0 then
        need_filter := false;
    elif #non_surjective_cell eq 1 then
        if &and[f lt non_surjective_cell[1] : f in free_choices] then
            need_filter := false;
        end if;
    end if;
    //if #free_choices gt 0 and #non_surjective_m gt 0 then
        // Postprocess with reduction
		//print "free_choices", free_choices;
		//print "non_surjective_m",non_surjective_m;
        //print "surjective_s_places",surjective_s_places;
    //end if;

    // 8. Return list of polynomials
    if CountOnly then
        return L, need_filter;
    end if;
    return L;
end intrinsic;

function print_template_old(tau)
    rtau := Reverse(tau);
    c := #rtau[1];
    //print "   " cat &cat[" x^" cat IntegerToString(i) : i in [#tau..0 by -1]];
    str := "   " cat &cat[" x^" cat IntegerToString(i) : i in [#tau..0 by -1]];
    for i in [c..1 by -1] do
        //print "p^" cat IntegerToString(i) cat "  0 " cat &cat[" " cat t[i]:t in rtau];
        str cat:= "\n" cat "p^" cat IntegerToString(i) cat "  0 " cat &cat[" " cat t[i]:t in rtau];
    end for;
    return str;
end function;

function print_template(tau:output:="text")
    rtau := Reverse(tau);
    c := #rtau[1];
    if output eq "text" then
        //print "   " cat &cat[" x^" cat IntegerToString(i) : i in [#tau..0 by -1]];
        str := "   " cat &cat[" x^" cat IntegerToString(i) : i in [#tau..0 by -1]];
        for i in [c..1 by -1] do
            //print "p^" cat IntegerToString(i) cat "  0 " cat &cat[" " cat t[i]:t in rtau];
            str cat:= "\n" cat "p^" cat IntegerToString(i) cat "  0 " cat &cat[" " cat t[i]:t in rtau];
        end for;
    elif output eq "latex" then
        str := "\\begin{center}\n\\small\n\\begin{tabular}{l|cc";
        str cat:= &cat["c":i in [1..#tau]];
        str cat:= "}\n";
        str cat:= "    " cat &cat["&$x^{" cat IntegerToString(i) cat "}$ " : i in [#tau..0 by -1]];
        str cat:= "\\\\\\hline";
        for i in [c..1 by -1] do
            str cat:= "\n" cat "$p^" cat IntegerToString(i) cat "$&$\\{0\\}$ " cat &cat["&$\\{" cat t[i] cat "\\}$ ":t in rtau] cat "\\\\";
        end for;
        str cat:= "\n\\end{tabular}\n\\end{center}";
        return str;
    else
        str := "Invalid output parameter";
    end if;
    return str;
end function;

AllTotallyRamifiedExtensionsDemo := function(K,R:verbose:=false,output:="text")
    // INPUT:
    //     K - a pi-adic field
    //     R - points of a ramification polygon, as [<x,y>]

    // degree of polynomial
    n := R[#R][1];
    
    // integral prime
    p := Prime(K);
    pi := UniformizingElement(K);

    // Precompute n*Hasse-Herbrand of RP
    //nhhr := [Min([pt[2] : pt in rpolyplusm]) : rpolyplusm in [[<pt[1],pt[2]+m*pt[1]> : pt in R] : m in [1..2*n] ]];

    // Take R, and find xes[], a[], b[] s.t. <x,y> eq <x,an+b>
    a := []; b := [];
    xes := [pt[1] : pt in R];
    for pt in R do
        q,r := Quotrem(pt[2],n);
        Append(~a,q);
        Append(~b,r);
    end for;
    
    // Find the denominators of the slopes of segments
    allslopes := [ -( (R[i+1][2]-R[i][2]) / (R[i+1][1]-R[i][1]) ) : i in [1..#R-1]];
    Sindex := [1] cat [i : i in [2..#R-1] | allslopes[i] ne allslopes[i-1]] cat [#R];
    S := [R[i][1] : i in Sindex];
    slopes := [allslopes[i] : i in Sindex[1..#Sindex-1]];
    //slopes := [-((R[Index(xes,S[i+1])][2]-R[Index(xes,S[i])][2]) / (S[i+1]-S[i])) : i in [1..#S-1]];
    h := [Numerator(s) : s in slopes];
    e := [Denominator(s) : s in slopes];
    
    // Find the minimum valuations prescribed by the RP
    minval := Minval(K,R);

    // 1. Set Krasner Bound
    c := Ceiling(1+2*a[1]+(2*b[1])/n)-1;   // J_0 is a[1]n+b[1] (magma indexes from 1)

    // Precompute n*Hasse-Herbrand of RP
    m := 1;
    nhhr := [Min([pt[2] : pt in [<pt[1],pt[2]+pt[1]> : pt in R]])];
    while nhhr[#nhhr] lt n*c-1 do
        m +:= 1;
        Append(~nhhr,Min([pt[2] : pt in [<pt[1],pt[2]+m*pt[1]> : pt in R]]));
    end while;
    
    // 2. Initialize Template
    if verbose then print "2. Init Template"; end if;
    taustr := [];
    for i in [1..n] do
        Append(~taustr,[" 0 " : j in [1..c]]);
     end for;
     if verbose then print print_template(taustr:output:=output) cat "\n"; end if;
    
    // 3. Set Free Choices (respecting ell)
    if verbose then print "3. Set free choices (respecting ell)"; end if;
    reducedzeros := ([<(hhm mod n)+1,(n-(hhm mod n)+hhm)/n> : hhm in nhhr | (n-(hhm mod n)+hhm) mod n eq 0]);
    //print "nhhr",nhhr;
    //print "reducedzeros",reducedzeros;
    for i in [1..n] do
        for j in [1..c] do
            //print <i,j>,<i,j> notin reducedzeros,(i eq 1 or j ge minval[i-1]);
            if <i,j> notin reducedzeros and (i eq 1 or j ge minval[i-1]) then
                taustr[i][j] := "R_K";
            end if;
        end for;
    end for;
    if verbose then print print_template(taustr:output:=output) cat "\n"; end if;
    
    // 4. Set coefficients by Sm
    if verbose then print "4. Set coeffs by Sm"; end if;
    for m in [1..Floor((R[1][2]-R[2][2])/(R[2][1]-1))] do
        i := nhhr[m] mod n;
        if (n-i+nhhr[m]) mod n eq 0 then
            j := (n-i+nhhr[m]) div n;
            //m,<i,j>;
            taustr[i+1][j] := "S_" cat IntegerToString(m);
        end if;
    end for;
    if verbose then print print_template(taustr:output:=output) cat "\n"; end if;
    
    // 5. Set coefficients by A
    if verbose then print "5. Set coeffs by A"; end if;
    for i in [1..#R] do
        if b[i] ne 0 then
            seg := #[cnt : cnt in S | cnt le R[i][1]];
            //seg := 1;
            j := a[i] + 1 - Valuation(Binomial(b[i],R[i][1]),p);
            //print R[i],"(",a[i],"n +",b[i],") sets f_{",b[i],",",j,"} to A_{",seg,",",R[i][1]-S[seg],"/",e[seg],"}";
            taustr[b[i]+1][j] := "A" cat IntegerToString(seg) cat IntegerToString((R[i][1]-S[seg]) div e[seg]);
        end if;
    end for;
    if verbose then print print_template(taustr:output:=output) cat "\n"; end if;
    
    // 6. Set tau_{0,1} to delta_0
    if verbose then print "6. Set f_{0,1} to delta_0"; end if;
    taustr[1][1] := "d_0";
    return print_template(taustr:output:=output);
end function;

NumberOfExtensionsFromPoly := function(f)
    return Degree(f) / #Roots(Polynomial(ext<CoefficientRing(f)|f>,f));
end function;

IsExtensionIsomorphic := function(f,g)
    return HasRoot(g,ext<CoefficientRing(f)|f>);
end function;

intrinsic AllTotallyRamifiedExtensions(k::RngPad,n::RngIntElt:j:=0,phi0:=0,invariants:=false) -> .
{All extension of pi-adic ring or field k with give invariants:
R - points of a ramification polygon, as [<x,y>], 
A - list of residual polynomials for segments of R,
phi0 - the constant coefficient mod pi^2
}
    K     := RingOfIntegers(k);
    Kx<x> := PolynomialRing(K);
   
    // integral prime
    p := Prime(K);
    pi := UniformizingElement(K);

    // Define Resdidue Class Field of K
    RK,res := ResidueClassField(K);
    RKz<z> := PolynomialRing(RK);
    
    "AllRamificationPolygons"; 
    if j ne 0 then
        RR := AllRamificationPolygons(K,n,j:points:=true);
    else
        RR := &cat[AllRamificationPolygons(K,n,j:points:=true) : j in PossibleDiscriminants(k,n)];
    end if;
    " -- done";
    "AllResidualPolynomials";
    if phi0 ne 0 then
       AA := <AllResidualPolynomials(k,R,phi0) : R in RR>;
    //E := [[&cat+[AllTotallyRamifiedExtensions(k,RR[i],a,res(phi_0/Prime(k))) : a in A] : A in AA[i]] : i in [1..#RR]];
      " -- done";
       if invariants then
         E := Flat([[rec<FRP|K:=K,deg:=n,j:=RR[i][1][2],rampol:=RR[i],A:=a,generators:=AllTotallyRamifiedExtensions(k,RR[i],a,res(phi0/Prime(k)))> : a in AA[i]] : i in [1..#RR]]);
       else
         E := [&cat[AllTotallyRamifiedExtensions(k,RR[i],a,res(phi0/Prime(k))) : a in AA[i]] : i in [1..#RR]];
      end if;
    else
      phi0s := DistinctConstantCoefficients(K,n);      
    //E := [[&cat+[AllTotallyRamifiedExtensions(k,RR[i],a,res(phi_0/Prime(k))) : a in A] : A in AA[i]] : i in [1..#RR]];
      " -- done";
       if invariants then
         E := Flat([[[rec<FRP|K:=K,deg:=n,j:=RR[i][1][2],rampol:=RR[i],phi0:=phi0,A:=a,generators:=AllTotallyRamifiedExtensions(k,RR[i],a,res(phi0/Prime(k)))> : a in AllResidualPolynomials(k,RR[i],phi0)] : phi0 in phi0s]:i in [1..#RR]]);
       else
         E := [[&cat[AllTotallyRamifiedExtensions(k,RR[i],a,res(phi0/Prime(k))) : a in AllResidualPolynomials(k,RR[i],phi0)] :phi0 in phi0s]: i in [1..#RR]];
      end if;
    end if;
    return E;
end intrinsic;

