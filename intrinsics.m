intrinsic Negate(~a::RngIntElt)
{negate the real number a.}
a := -a;
end intrinsic;

intrinsic Doppel(~a::RngIntElt)
{double the integer a.}
a*:=2;
end intrinsic;

intrinsic '+'(s1::MonStgElt, s2::MonStgElt) -> MonStgElt
{Concatinate strings}
return s1 cat s2;
end intrinsic;

intrinsic '*'(n::RngIntElt, s::MonStgElt) -> MonStgElt
{Multiply integers and strings}
r := "";
for i in [1..n] do r +:= s; end for;
return r;
end intrinsic;

intrinsic Pwr(g::GrpPerm, n::RngIntElt) -> GrpPerm
{Direct product of g with itself n times.}
if n eq 1 then return g;
else return DirectProduct(g, Pwr(g, n-1));
end if;
end intrinsic;
