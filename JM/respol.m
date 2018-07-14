 
function ContentVal(f)
  polseq := Coefficients(f);
  //polseq;
  //[Valuation(a):a in polseq];
  return Minimum([Valuation(a):a in polseq]);
end function;

function ResidualPolynomials(phi) //-> .
/*{An implementation of Greve-Pauli Theorem 9.1.
That is a function that given an Eisenstein polynomial returns
the maximal tamely ramified subfield of its splitting field.
Input: an Eisenstein Polynomial of degree n=e0*p^w over Qp or an unramified extension of Qp}*/

        if IsEisenstein(phi) eq false then
                error "Polynomial is not Eisenstein.";
        end if;

        K:=CoefficientRing(phi);
        Zp:=BaseRing(K);

        n:=Degree(phi);
        p:=Prime(PrimeRing(K));

        w:=Valuation(n,p);
        e0:=n div p^w;
        e0:=Integers()!e0;
        
        Coeff:=Eltseq(phi);

        L:=ext<K|phi>;
        alpha:=L.1;
        pi_L:=UniformizingElement(L);
        
        Lx<x>:=PolynomialRing(L);
        rho:=Polynomial(Lx,[&+[Coeff[i]*(alpha*x + alpha)^(i-1): i in [1..(n+1)]]]) div (alpha^n);
        rho:=Lx!rho;

        ramification_polygon := RamificationPolygon(phi);
        vertices := LowerVertices(ramification_polygon);        
        slopes := Slopes(ramification_polygon)[1..#vertices-1]; 
        
        //vertices:=vertices[2..#vertices];    // get rid of point with x-coordinate=0
        //slopes:=slopes[2..#slopes];          // get rid of segment with infinite slope
        
        a:=[Integers()!vertices[i][1]: i in [1..#vertices]];    //list of x-coordinates of vertices
        b:=[Integers()!vertices[i][2]: i in [1..#vertices]];    //list of y-coordinates of vertices

        if e0 eq 1 then
                l:=#slopes;
        else  //e0>1
                l:=#slopes-1;           //l+1 st segment is horizontal on x-axis
        end if;

        e:=[];
        h:=[];
        for i in [1..#slopes] do
                e[i]:=Denominator(-slopes[i]);     // list of (negative) slope denominators
                h[i]:=Numerator(-slopes[i]);       // list of (negative) slope numerators
        end for;
        
        RL,omega:=ResidueClassField(L);
        Ry<y>:=PolynomialRing(RL);                         // Polynomial Ring in variable y over Residue Class Field of L
        
        RK,sigma:=ResidueClassField(K);
        Rt<t>:=PolynomialRing(RK);

        A:=[];                               // Residual Polynomials of segments
        for i in [1..#slopes] do
                di:=a[i+1]-a[i];
                fin:=Integers()!(di/e[i]);
                Ai:=Polynomial(Ry,[&+[omega(Coefficient(rho,j*e[i]+a[i]) div pi_L^(-j*h[i]+b[i]))*y^j: j in [0..fin]]]);
                Ai:=Ry!Ai;
                Append(~A,Ai);
        end for;
        return A;
end function;


