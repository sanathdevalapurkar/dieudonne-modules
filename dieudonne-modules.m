/* The following is code to count the number of final types for a given genus
 * and prime. Trivial modifications to this code  allow one to check whether
 * there is a curve has a certain final type/mod p Dieudonn'e module. */

/* The reader is referred to Devalapurkar-Halliday, "The Dieudonn'e modules and
 * Ekedahl-Oort types of Jacobians of hyperelliptic curves in odd
 * characteristic", for an explanation of where the formulae in this code come
 * from. */

deg := [];

/* Here, 7 is the degree up to which we are counting the number of curves
 * (where we only count curves of *odd* degree; this can easily be changed). If
 * you wish to fix a degree d, simply change "3 to 7" to "d to d". */

for k := 3 to 7 do
	if GF(2)!k ne 0 then
		deg := Append(deg,k);
		end if;
	end for;

/* This is the range of primes. Again, this can be trivially modified to the
 * users' need. */
pr := PrimesInInterval(3,7);

for w := 1 to #pr do
	p := pr[w];
	q := p;
	for d in deg do
		t := Cputime();

		cantypeset := {};
		cantype := [];

		g := IntegerRing()!((d-1)/2);
		prank := [];
		for i := 1 to g+1 do
			prank := Append(prank,0);
			end for;

		R := GF(p);
		
		QQ := CartesianPower(GF(p),d+1);

		J := 0;
		for a in QQ do
			/* if J ge 0 and a[#a] ne 0 and a[#a-1] eq 0 then */
			if J ge 0 and a[#a] ne 0 then
				S<x> := PolynomialRing(R);
				f := &+[x^(i)*a[i+1]: i in [0..d]];

				if f in R or Discriminant(f) eq 0 then
					/* print "The curve",f,"is singular at p =",p;
					print "-------------------------------------------------------------"; */
				else
					J := J+1;

					b := IntegerRing()!((p-1)/2);
					g := f^b;
					e := Degree(g);
				
					c := [];
					for i := 0 to e do
						c := Append(c,Coefficient(g,i));
						end for;
				
		
					g := IntegerRing()!((d-1)/2);

					F := [];
					for i := 1 to g do
						for j := 1 to g do
							o := p*j - i;
							m := #c;
							if o le m-1 and o ge 0 then
								F := Append(F,c[o+1]);
							else
								F := Append(F,0);
							end if;
							end for;
						for j := 1 to g do
							F := Append(F,0);
							end for;
						end for;
					for i := 1 to g do
						for j := 1 to g do
							l := d-i;
							h := 0;
							for k := g+1 to l do
								o := p*j-k;
								m := #c;
								if o le m-1 and o ge 0 then
									h := h + (k-i)*a[k+i+1]*c[o+1];
								else
									h := h + 0;
								end if;
							end for;
							F := Append(F,h);
							end for;
						for j := 1 to g do
							F := Append(F,0);
							end for;
						end for;
					F := Matrix(2*g,2*g,F);
					
					V := [];
					for i := 1 to g do
						for j := 1 to g do
							V := Append(V,R!0);
							/* print "(",i,",",j,"):", 0; */
							end for;
						for j := 1 to g do
							V := Append(V,R!0);
							/* print "(",i,",",g+j,"):", 0; */
							end for;
						end for;
					
					HW := [];
					for i := 1 to g do
						for j := 1 to g do
							h := 0;
							for k := 0 to j do
								o := p*(i)-k+j;
								m := #c;
								if o le m-1 and o ge 0 then
									y := (k-2*j);
									h := h + y*a[k+1]*c[o+1];
								else
									h := h + 0;
								end if;
								end for;
							/* print "(",g+i,",",j,"):", h; */
							V := Append(V,R!h);
							end for;
						for j := 1 to g do
							o := i*p-j;
							m := #c;
							if o le m-1 and o ge 0 then
								h := c[o+1];
								V := Append(V,R!h);
								
								HW := Append(HW,R!h);
								/* print "(",g+i,",",g+j,"):", h; */
							else
								V := Append(V,R!0);
								/* print "(",g+i,",",g+j,"):", 0; */
							end if;
							end for;
						end for;
					V := Matrix(2*g,2*g,V);

					/* Sanity check */
					L := MatrixAlgebra(IntegerRing(),2*g);
					if V*F ne L!0 then
						print "There's an error --- recheck the code!";
						V*F;
						end if;

					OO := [];
					for k := 1 to g do
						OO := Append(OO,0);
						end for;
					
					/* Uncomment the below line to compile data for non-ordinary stuff only */
					/* if HW ne OO then */
					/* Uncomment the below line to compile data for *all* curves */
					if OO eq OO then
						coh := VectorSpace(GF(p), 2*g);
						
						/* The canonical type computation
						This is specified by a triple (v, f, p) --- see 2.3 of Oort's "A stratification of ..." paper,
						where v,f:{0, ..., 2*g} --> {0, ..., g} are such that V(N_i) = N_{v(i)},
						and F^{-1}(N_i) = N_{f(i)}. Moreover, rank(N_i) = p^{p(i)}.
						*/
	
						Finv := function(X)
							quoSpace,mapToQuoSpace := quo<coh | X>;
							return Kernel(F*Matrix([mapToQuoSpace(coh.i) : i in [1..Dimension(coh)]]));
							end function;
	
						ma := false;
						i := 0;
						while ma eq false do
							if Rank(V^i) eq Rank(V^(i+1)) then
								ma := true;
								mi := i;
							else
								i := i+1;
								end if;
							end while;
						
						L := [];
						dimL := [];
						for k := 0 to mi do
							L := Append(L,Image(V^k));
							dimL := Append(dimL,Rank(Image(V^k)));
							end for;
						
						for k := 1 to 2*g+1 do
							if GF(2)!k eq 1 then
								for a in L do
									if not Rank(Finv(a)) in dimL then
										L := Append(L,Finv(a));
										dimL := Include(dimL,Rank(Finv(a)));
										end if;
									end for;
							elif GF(2)!k eq 0 then
								for a in L do
									if not Rank(Image(Morphism(a,coh)*V)) in dimL then
										L := Append(L,Image(Morphism(a,coh)*V));
										dimL := Include(dimL,Rank(Image(Morphism(a,coh)*V)));
										end if;
									end for;
								end if;
							end for;
					
						L := Sort(L,func<x,y|Rank(x)-Rank(y)>);
						dimL := Append(dimL,0);
						dimL := Sort(dimL);
						
						/* The function v */
						v := [0];
						for X in L do
							Morp := Morphism(X,coh)*V;
							VX := Rank(Image(Morp));
							/* s := []; */
							/* s := Append(s,[Rank(X),VX,Index(dimL,VX)]); */
							/* s := Append(s,[Rank(X),VX]); */
							v := Append(v,Index(dimL,VX)-1);
						end for;
	
						/* The function f */
						ff := [0];
						for X in L do
							FiX := Rank(Finv(X));
							/* s := []; */
							/* s := Append(s,[Rank(X),VX,Index(dimL,FiX)]); */
							/* s := Append(s,[Rank(X),FiX]); */
							ff := Append(ff,Index(dimL,FiX)-1);
						end for;
	
						/* End canonical type computation */
	
						/* Begin final type computation */
						
						rho := dimL;
						phi := [v[1]];
						for i := 1 to #rho-1 do
							if v[i] eq v[i+1] then
								for j := rho[i]+1 to rho[i+1] do
									phi := Append(phi,phi[#phi]);
									end for;
							else
								for j := rho[i]+1 to rho[i+1] do
									phi := Append(phi,phi[#phi]+1);
									end for;
								end if;
						end for;
						phi := Remove(phi,1);
						for k := 1 to g do
							phi := Prune(phi);
							end for;
	
						/* Young type */
						YoungType := [];
						for j := 1 to g do
							s := [];
							for i := 1 to g do
								if i-phi[i] ge j then
									s := Append(s,i);
									end if;
								end for;
							YoungType := Append(YoungType,#s);
							end for;
	
						/* The output: */
	
						Ig1 := [];
						for i := 1 to g do
							Ig1 := Append(Ig1, i-1);
							end for;
	
						/* Uncomment the below line to answer Question 8.3 of http://www.math.colostate.edu/~pries/Preprints/oortchapter16.pdf */
						/* if Rank(Image(V^(g+1))) ge 0 and phi eq Ig1 then */
						
						/* Uncomment the below line to print things for _each_ curve */
						/* if Rank(Image(V^(g+1))) ge 0 then
							print "-------------------------------------------------------------";
							print "* We're working at the prime",p;
							print "* The degree",d,"curve C is y^2 =",f;
							print "* F =",F;
							print "* V =",V;
							print "* p-rank =",Rank(Image(V^(g+1)));
							print "* a-number =",g - Rank(Image(V^2)); */

							/* print "-- First, the function rho is just the sequence of dimensions:";
							print "rho =",dimL;
							print "-- Next, the output for v is of the form [dim V(N_i) = dim N_{v(i)}]:";
							print "v =",v;
							print "-- Lastly, the output for f is of the form [dim F^{-1}(N_i) = dim N_{f(i)}]:";
							print "f =",ff; */

							/* print "* The canonical type is:",phi;
							print "* The Young type is:",YoungType; */
							/* Uncomment the below line to answer Question 8.3 of http://www.math.colostate.edu/~pries/Preprints/oortchapter16.pdf */
							/* break a; */
							/* end if; */
											
						cantype := Append(cantype,phi);
						Include(~cantypeset,phi);
						/* End final type computation */

					end if;

				end if;
			end if;
			end for;

		alltypes := {};
		for k in cantype do
			s := 0;
			for l in cantype do
				if l eq k then
					s := s+1;
					end if;
				end for;
			Include(~alltypes,<k,s>);
			end for;

		print "-------------------------------------------------------------";
		print "Degree:",d;
		print "Prime:",p;
		print "The number of final types coming from hyperelliptic curves is",#cantypeset,"(out of",2^g,"possibilities).";
		print "The final types coming from hyperelliptic curves are (written as <final-type, #of copies>):";
		alltypes;
		print "Time taken:",Cputime(t);

		end for;
	end for;
quit;
