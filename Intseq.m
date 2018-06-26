intrinsic Intseq(n::FldReElt, b::RngIntElt, s::RngIntElt) -> SeqEnum, SeqEnum
	{The base b representation of n; first negative powers of b going to \
	b^-s, then positive powers of b.}
	a := n - Floor(n);
	i := -1;
	L := [];
	while i ge -s do
		f := b^i;
		count := 0;
		while a ge f do
			a -:= f;
			count +:= 1; end while;
		Append(~L, count);
		i -:= 1; end while;
	return L, Intseq(Floor(n), b);
	end intrinsic;

intrinsic Intseq(n::FldRatElt, b::RngIntElt, s::RngIntElt) -> SeqEnum, SeqEnum
	{no}	
	R := RealField();
	n := R!n;
	return Intseq(n, b, s);
	end intrinsic;
