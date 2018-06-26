function Lowercase(s)
    e := Eltseq(s);
    r := "";
    for c in e do
	x := StringToCode(c);
	if x lt 97 then x +:= 32; end if;
	r := r cat CodeToString(x);
	end for;
    return r; end function;

function StringSort(L)
    newL := [];
    for e in L do
	Append(~newL, Lowercase(e));
	end for;
   return newL; end function;

function DivAlg(a,b)
    r := a mod b;
    q := a div b;
    return q, r; end function;

function GCD2(a,b)
    if a lt b then c := a; a := b; b := c; delete c; end if;
    r := a mod b;
    q := a div b;
    if r eq 0 then return b;
    else return GCD2(b,r);
    end if; end function;

function xGCD2(a,b)
    //if a lt b then c := a; a := b; b := c; end if;
    A := [a, 1, 0]; B := [b, 0, 1];
    T := xGCD2_Helper(A,B); 
    if assigned c then return [T[1], T[3], T[2]];
    else return T; end if; end function;

function xGCD2_Helper(A,B)
    q,r := DivAlg(A[1],B[1]);
    if r eq 0 then return B;
    else
        R := [r, A[2]-q*B[2], A[3]-q*B[3]];
        return $$(B,R); end if;
    end function;
