function tally(seq)

        set := Seqset(seq);
        multiset:=SequenceToMultiset(seq);
        return Sort([<s,Multiplicity(multiset,s)>: s in set]);

end function;

function NeedResolvent(W,H,Candidates)

	a,b,c:=CosetAction(W,H);

	//Figure out orbitlengths for first candidate.  This will be the basis of comparison.

	G1:=Candidates[1];

	phi_G1:=a(G1);

	Orbb1:=Orbits(phi_G1);
	Orb_lengths1:=[#r: r in Orbb1];
	
	Orb_lengths1:=Set(tally(Orb_lengths1));

        orbs :=[];

	for i in [2..#Candidates] do

		G:=Candidates[i];
		phi_G:=a(G);

		Orbb:=Orbits(phi_G);
		Orb_lengths:=[#r: r in Orbb];
	
		Orb_lengths:=Set(tally(Orb_lengths));

Append(~orbs,Orb_lengths);
	
//		if Orb_lengths ne Orb_lengths1 then
//			print "needed !";
		//	return true;
//		end if;

	end for;

	//return false;
	return SequenceToMultiset(orbs);

end function;


function GoodResolvents(W,Hs,Candidates)

        orbs :=[];

  A := AssociativeArray();
  for G in Candidates do
     A[G]:=[];
  end for;
  for H in Hs do
        a,b,c:=CosetAction(W,H);
        
        for G in Candidates do

                phi_G:=a(G);
                Orbb:=Orbits(phi_G);
                Orb_lengths:=[#r: r in Orbb];
                Orb_lengths:=Set(tally(Orb_lengths));

                Append(~A[G],Orb_lengths);

//              if Orb_lengths ne Orb_lengths1 then
//                      print "needed !";
                //      return true;
//              end if;

        end for;
   end for;
        //return false;
        return A;

end function;

