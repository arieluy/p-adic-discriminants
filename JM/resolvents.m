//Version 5-17-17
//Removed unnecessary Code
//Change Polyroot to check
//base ring to call 
//appropriate gcd function
//Fixed Incorrect variable name 
//in 3 block case loop


//Version 5-14-17
//Removed calls to CheckPoly
//Use this version for calculating examples
//for thesis and other work
//Will not add additional features to this file

//Version 4-18-17
//Added sorting Cartestian Product and
//added code to exit early if valuation
//shows that polynomial produced lies in the base field 
//at some point


//Version 4-15-17
//Changed to handle three partitions with all multiplicities
//Changed to loop through cartesian product 

//Version 4-11-17
//Removed some unnecessary code
//Added some comments


//debug flag
//can be replaced with internal verbose flags(eventually)
//Right now this prints out way too much stuff
//so it is useless
debug := false;

//forward statements
forward RelLR;
forward convM2;
forward LR;



//sz, SumZeroes
//Input: polynomials f,g
//Computes the resultant Res_y(f(y),g(x-y)).
function sz(f,g)
   R:=CoefficientRing(f);
   Rxy<x,y>:=PolynomialRing(R,2);

   First:=Rxy!Evaluate(f,y);
   Second:=Rxy!Evaluate(g,(x-y));
 
   Res:=Resultant(First,Second,y);
   Res:=UnivariatePolynomial(Res);
	
   if debug then 
      "Res",Res;
   end if;
   return Res;

end function;


//mz, MultiplyZeroes
//Input:  polynomial f, integer d
//Output:  the polynomial whose roots are equal to 
//the roots of f multiplied by the integer d.
function mz(d,f)

   n := Degree(f);
   R := CoefficientRing(f);
   Rx := PolynomialRing(R);

   if d eq 0 then
      return Rx.1^n;
   end if;
 
   f1 := Eltseq(f);
   goal := Polynomial(R,[f1[i+1]*d^(n-(i)):i in [0..Degree(f)]]);

   return goal;

end function;





//pr, Polyroot
//Input: Positive integer k, monic polynomial u such that u(x)=r(x)^k for some unknown monic r(x)
//Output:  r(x)
function pr(k,u)

   R := CoefficientRing(u);
   Rx := PolynomialRing(R);

   u := Rx!u;
   
   if k eq 1 then
      return u;
   end if;

        
   if debug then
      Parent(u);
   end if;

   if debug then
      "u", u;
      "Derivative(u)", Derivative(u); 
   end if;

   t := u;
   if R cmpeq Integers() then
      t := t div Gcd(u, Derivative(u));
   else
      t:= u div GcdWithLoss(u,Derivative(u));
   end if;

   r:=t;
   s:=u;

   while Degree(r) lt Degree(u)/k do
      s:=s/(t^k);
      s:=Rx!s;		

      t:= GcdWithLoss(s,t);
      r:=t*r;
   end while;

   return r;
end function;





//convM, Converts a sequence M to a record as described
//Input: a sequence M 
//Output: A record respresenting M as a multiset. The record consists
//   of two enumerated sequences, 'coeff', the coefficients, and 
//   'mult', the multiplicities of the coefficients in the order that 
//   they appear in coeff
function convM(M)
   //Set up the record format for the multiset
   MS := recformat<coeff, mult: SeqEnum>;

   r := #M;

   t := Seqset(M);
   k := #t;
   
   N := rec<MS|coeff:= Setseq(t),mult := [0: i in [1..k]]>;

   for j in [1..r] do
      s := Index(N`coeff, M[j]);
      N`mult[s] +:= 1;
   end for;

   return N;
end function; 



     

//LRSeq, Calls LR after converting M to a record
//This is the user function for now
//LR takes a record as input
//Input: A sequence M containing the coefficients of the invariant,                  
//       F, and a polynomial, f
//Output: The linear resolvent of F and f

function LRSeq(M,f)
  
   return LR(convM(M), f);

end function;





//LR, the LinResolv algorithm, this one is the internal function that
//takes the record as input and is recursive
//overload function call to work with multiset representation of M
//Input: Ms is a record representing the invariant, F, as a multiset consisting of two enumerated
//   sequences, 'coeff', the coefficients, and 'mult', the multiplicities
//   of the coefficients in order
//   f is the polynomial for which we are computing the resolvent
//Output: The linear resolvent of the invariant F and the polynomial f
function LR(Ms, f)
   //Set up
   n := Degree(f);
   k := #Ms`coeff; //# of distinct entries //Change for multisets
   r := &+Ms`mult; //total # of coefficients //Change for multisets
   Fx := Parent(f);

   if debug then
      "Fx = ", Fx;
   end if;

   t := Fx!0;
   u := Fx!0;
   s := Fx!1;
   
   if debug then
      "LR(", Ms,", ", f,")";
   end if;

/* This part is unnecessary
   //Deal with 0's in M (Step 1) 
   c := Index(Ms`coeff, 0);
   if c ne 0 then
      if #Ms`coeff eq 1 then //Only 0's in M
         t := Fx.1;
      else	//Remove the 0's from M
         m := Ms`mult[c];
         //m is number of 0's in M
         Remove(~Ms`coeff,c);
         Remove(~Ms`mult,c); 
         t := Fx!LR(Ms, f);
      end if;
      
      d := Binomial(n-r+m, m);
      return Fx!t^d;
   end if;
*/

   //If M has only one nonzero entry
   if r eq 1 then
      j := Fx!mz(Ms`coeff[1], f);
      if debug then
         "Stop Condition: return ", j;
      end if;
      return j;
   end if;
 
   //Setup Step 4
   er := Ms`coeff[k]; // the last coefficient entry in Mn
   //k is initialized earlier (# of distinct entries)
   //Remove last entry (decrease multiplicity of last entry)
   kbar := k;
   Mbar := Ms;
   Mbar`mult[kbar] -:=1;

   //Remove entry if multiplicity is 0
   if Mbar`mult[kbar] eq 0 then
      Remove(~Mbar`coeff, kbar);
      Remove(~Mbar`mult,kbar);
      kbar := kbar-1;
   end if;
   
   //Define u(x)
   u := Fx!LR(Mbar, f);
   if debug then 
      "u(x) = ", u;
   end if;
   //End of Step 4

   //Step 5 - Define s(x)
   for i in [1..kbar] do
      Mi := Mbar;
      new_ai := Mi`coeff[i] + er;
      if Mi`mult[i] gt 1 then
         Mi`mult[i] -:= 1;
      else
         Remove(~Mi`coeff, i);
         Remove(~Mi`mult, i);
      end if;
      c := Index(Mi`coeff,new_ai);
      if c ne 0 then
         Mi`mult[c] +:= 1;
      else
         Append(~Mi`coeff, new_ai);
         Append(~Mi`mult, 1);
         c := kbar;
      end if;
      s *:= Fx!(LR(Mi, f)^Mi`mult[c]);
   end for;
   
   if debug then
      "s(x) = ", s;
   end if;
   //End of Step 5

   //Step 6
   d := Ms`mult[k]; //multiplicity of last element of M
   //Define g(x)
   g := Fx!mz(Ms`coeff[k], f);
   if debug then
      "g(x) = ",g;
   end if;
   //Define t(x)
   t := Fx!sz(Fx!u,Fx!g) div Fx!s; 
   if debug then
      "t(x) = ",t;
   end if;
   return Fx!pr(d,t);
end function;





//From here down is still a work in progress

//RelLRSeq, the user function for computing the relative linear resolvent
//   with respect to the wreath product of S_n and S_n
//Input: f is a sequence of polynomials all of the same degree whose product is the polynomial
//   that we are interested in
//   Order of polynomials is such that the permutations act on the roots appropriately 
//   F is the invariant as a sequence of coefficients (order matters here)
//Output: The relative resolvent of F and the product of the polynomials in f
function RelLRSeq(f, F)
   d := Degree(f[1]);
   n := #F;
   
   //Partition the invariant
   if n lt d then
      M := [F];
   elif n mod d eq 0 then
      M := Partition(F, [d: i in [1..n div d]]);
   else
      M := Partition(F, Append([d: i in [1..n div d]], n mod d) );
   end if;

   //The zeroes are unnecessary once the invariant is partitioned
   for i in [1..#M] do
      while Index(M[i],0) ne 0 do
         Exclude(~M[i],0);
      end while;
   end for;

   for i := #M to 1 by -1 do
      if IsEmpty(M[i]) then
         Remove(~M, i);
      end if;
   end for;

   if debug then
      "NO zero M", M;
   end if;
  
   if debug then
      "Paritition M", M;
   end if;

   //need to convert to sequence of records
   M1 := convM2(M);

   //Constructs the matrix containing the absolute resolvents
   // for each polynomial in f and each partition of M
   //Right now, it prints the time for each one
   
   "Constructing Absolute Resolvents";
   LRMat := [];
   for i in [1..#M1] do
      t := Cputime();
      row := [];
      for j in [1..#f] do
         "M[",i,"]","phi[",j,"]";
         row[j] := LR(M1[i]`MS, f[j]);
      end for;
      LRMat[i]:= row;
      t1 := Cputime(t);
      "Time ", t1;
   end for;
   return RelLR(M1, f,LRMat);
end function;



//iMinus, a helper function
//Input: lrMat, a sequence of sequences, and removed, an index to be removed from each sequence
//Output: The sequence with the appropriate pieces removed from each of the internal sequences
function iMinus(lrMat, removed)
   for i in [1..#lrMat] do
      Remove(~lrMat[i], removed);
   end for;
   return lrMat;
end function;



//RelLR, the internal function for computing the relative linear resolvent
//Input: f is a sequence of polynomials
//   M is a sequence of records with each record containing the
//      multiset record and the multiplicity of the multiset in the sequence
//   LRMat is the matrix of absolute resolvents
function RelLR(M,f, LRMat);
   //"Record M", M;
   r := &+[i`mult: i in M]; //This is the total number of partitions
   linResolv := Parent(f[1])!1;
   m := #f;
   k := #M; //This is the number of distinct multisets


   if r le 3 then
      //"in if r le 3";
      if r eq 1 then
         //"r = 1";
         //"in if r eq 1";
         for i in [1..m] do
            "if i", i;
            linResolv *:= LRMat[1][i]; //LR(M[1]`MS, f[i]);
         end for;
         //"returning";
         return linResolv;
      end if;
      
      if r eq 2 then
         //"r = 2";
         Loopy := Setseq(Permutations(Seqset([1..m]), 2));
         LRM := [LRMat[1]];
         if k eq 1 then    //only 1 distinct partition
            Loopy := {Seqset(Loopy[i]): i in [1..#Loopy]};
            Loopy := [Setseq(L): L in Loopy];
            Append(~LRM, LRMat[1]);
         else
            Append(~LRM, LRMat[2]);
         end if;
         Sort(~Loopy);
         for L in Loopy do
            "Computing for ",L;
            t := Cputime();
            linResolv *:= sz(LRM[1][L[1]], LRM[2][L[2]]);
            t1 := Cputime(t);
            "Degree, i, j, Time: ",Degree(linResolv), L, t1;
         end for;
         return linResolv;         
      end if;

      if r eq 3 then
         //"r = 3";
         Loopy := Setseq(Permutations(Seqset([1..m]), 3));
         LRM := [LRMat[1]];
         if k eq 1 then    //only 1 distinct partition
            Loopy := {Seqset(Loopy[i]): i in [1..#Loopy]};
            Loopy := [Setseq(L): L in Loopy];
            LRM := LRM cat [LRMat[1],LRMat[1]];
         elif k eq 2 then
            Loopy1 := Setseq(Permutations(Seqset([1..m]), 2));
            Loopy1 := {Seqset(Loopy1[i]): i in [1..#Loopy1]};
            Loopy1 := [Setseq(L): L in Loopy1];
            Loopy := [];
            for i in [1..m] do
               for L in Loopy1 do
                  if Index(L, i) eq 0 then
                     Append(~Loopy, L cat [i]);
                  end if;
               end for;
            end for;
            LRM := LRM cat [LRMat[1], LRMat[2]];
         else
            LRM := LRM cat [LRMat[2], LRMat[3]];
         end if;
         Sort(~Loopy);           
         for L in Loopy do
            t := Cputime();
            linResolv *:= sz(sz(LRM[1][L[1]], LRM[2][L[2]]), LRM[3][L[3]]);
            t1 := Cputime(t);
            "Degree, i, j, Time: ",Degree(linResolv), L, t1;
         end for;
         return linResolv;         
      end if;
   end if;

//This part is not being used now
//Reprogramming to use Matrix instead for speed, will fix multiplicity later
   M1 := M;
   M1[r]`mult -:= 1;
   if M1[r]`mult eq 0 then
      Prune(~M1);
   end if;

   endLR := LRMat[#LRMat];
   restLR := Prune(LRMat);
   for i in [1..m] do
      "i", i;   
      linResolv *:= sz(RelLR(M1, Remove(f, i), iMinus(restLR, i)), endLR[i]);//LR(M[r]`MS, f[i]));
      "done i",i;
   end for;
   "outside for"; 
   //c := M[r]`mult;
   //linResolv := pr(linResolv, c);
   return linResolv;
end function;

//Input: a sequence of sequences 
//Output: a sequences of records each containing a multiset
//   record (see convM) and the multiplicity of the multiset  
//   in the input sequence
function convM2(M)
   k := #M; //The number of partitions of the invariant
   d := #M[1]; //length of each partition (corresponds to the degree)

   //Multiset of multisets
   //No need to preserve order
   MM := SequenceToMultiset([SequenceToMultiset(M[i]): i in [1..k]]); 

   //Define the record format
   RMs := recformat<MS:Rec, mult:Integers()>;
   
   Ms := MultisetToSet(MM);

   cM := [];

   for i in Ms do
      Append(~cM, rec<RMs|MS:=convM([j:j in i]), mult:=Multiplicity(MM, i)>);
   end for;

   Sort(~cM, func<a,b|b`mult-a`mult>);   

   return cM; 
end function;
