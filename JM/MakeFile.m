procedure MakeFile(FileName,M)
   outof := #M;
   
   Mmult := SequenceToMultiset(M);
   
   Mset := Setseq(MultisetToSet(Mmult));
  
   n := #Mset;

   mults := [Multiplicity(Mmult, Mset[i]): i in [1..n]];
//   "mults", mults;
//   "Mset", Mset;  
   line1 := "function MakeGroup2()";

   s := "G1 := DirectProduct(" cat Sprintf("%1o",[Sprintf("Sym(%1o)", x): x in [mults[i]: i in [1..n]]]) cat ");";
   
   t := "S := Sym(" cat Sprintf("%1o", outof) cat ");";
   
   indices := [];
   for i:= n to 1 by -1 do
      if mults[i] ne 1 then
         new := [];
         for j in [1..mults[i]] do
            k := Index(M,Mset[i]);
            new[j] := k;
            M[k] := -5;
         end for;
//"Mset[i]", Mset[i];
//"new", new;
         Append(~indices, new);
      else
         Remove(~mults, i);
      end if;
   end for;
   Reverse(~indices); 
//"indices",indices;
   stringy := "mappy := hom <G1->S|";

   newn := #indices;


   for i in [1..newn] do
      stringy := stringy cat "S!(";
      for j in [1..#indices[i] -1] do
         stringy := stringy cat Sprintf("%1o,", indices[i][j]);
      end for;
      stringy := stringy cat Sprintf("%1o", indices[i][#indices[i]]);
      stringy := stringy cat ")";
      if mults[i] gt 2 then
         stringy := stringy cat ", S!(";
         stringy:= stringy cat Sprintf("%1o, %1o)", indices[i][1], indices[i][2]);
      end if;
      if i ne newn then
         stringy := stringy cat ",";
      end if;
   end for;
  
   stringy := stringy cat ">;";

   Write(FileName, line1 : Overwrite:=true);
   Write(FileName, s);
   Write(FileName, t);
   Write(FileName, stringy);
   Write(FileName, "G := sub<S|[mappy(g): g in Generators(G1)]>;");
   Write(FileName, "return G;");
   Write(FileName, "end function;");
end procedure;


