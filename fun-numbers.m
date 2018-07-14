// find a list of n numbers that add up to a multiple of p
// n is a factor of p-1

function MySum(lst)
    s := 0;
    for i in lst do s +:= i; end for;
    return s;
end function;

function IsComplete(p, n, lst)
    if (#lst ne n) or (MySum(lst) mod p ne 0) then return false; end if;
    return true;
end function;

function FunNumbers(p)
    divisors := Divisors(p-1);
    prime_divisors := PrimeDivisors(p-1);
    for d in divisors do FunNumbers(d); end for;
end function;

function NonMirrorFunNumbers(p, n : lst := [], unused := [1..p-1])
    if IsComplete(p, n, lst) then return lst;
    elif #lst eq n then return false; end if;
    for m in unused do
        tmpSolution := NonMirrorFunNumbers(p, n : lst := Append(lst, m),
            unused := Exclude(Exclude(unused, m), p-m));
        if tmpSolution cmpne false then return Sort(tmpSolution); end if;
    end for;
    return false;
end function;

function MirrorFunNumbers(p, n : lst := [], unused := [1..p-1])
    if IsComplete(p, n, lst) then return lst;
    elif #lst eq n then return false; end if;
    for m in unused do
        tmpSolution := MirrorFunNumbers(p, n : lst := Append(Append(lst, m), p-m), 
            unused := Exclude(Exclude(unused, m), p-m));
        if tmpSolution cmpne false then return Sort(tmpSolution); end if;
    end for;
    return false;
end function;

MirrorFunNumbers(17, 4 : lst := [1,16], unused := [2..11]);
