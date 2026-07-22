// Calculates Tk, Ck for a given even k
function TkCk (k);

  assert k mod 2 eq 0;

  R<x> := PolynomialRing(Rationals());
  Tk := 0;

  for l in [0..k] do
    Tk := Tk + Factorial(k + 1)/Factorial(k + 1-l)/Factorial(l) * (-1)^l * Evaluate(BernoulliPolynomial(l), 0) * x^(k + 1-l);
  end for;

  Tk := Tk / (k+1) / x / (x+1) / (2*x+1);

  assert (Denominator(Tk) eq 1);

  Tk := Numerator (Tk);
  Ck := Integers()!(LCM ([ Denominator(c) : c in Coefficients (Tk) ]));

  R<x> := PolynomialRing(Integers());

  return <(Ck*Tk), Ck>;

end function;

// Calculates |Res(f,g,x)|
function AbsResultant (f,g);

  return Integers()!(Abs(Resultant(f,g)));

end function;

// calculate the product of the odd prime divisors of x
function rad2(x);
  r := &*PrimeDivisors(x);

  if r mod 2 eq 0 then
    r := Floor(r/2);
  end if;

  return r;
end function;



// Generates all the possible cases coming from the descent in Schaeffer's conjecture. The descent leads to a system of three equations
//  Ax^n - By^n = 1
//  2By^n - Cz^n = 1
//  Cz^n - 2Ax^n = 1
// A case is represented by a system of of coefficients:
//   [ [A0, B0], [A1, B1], [A2, B2] ]
// for a general system
//   A0x^n - B0y^n = 1
//   A1y^n - B1z^n = 1
//   A2z^n - B2z^n = 1
// where in Schaeffer's conjecture we get the system
//   [ [A, B], [2B, C], [C, 2A] ]
function generate_cases (k);

  I := Integers ();

  Tk_Ck := TkCk(k);
  Tk := Tk_Ck[1];
  Ck := Tk_Ck[2];

  R<x> := PolynomialRing (Integers());

  delta0 := AbsResultant (Tk, x);
  delta1 := AbsResultant (Tk, x+1);
  delta2 := AbsResultant (Tk, 2*x+1);

  DTk := Derivative(Tk);

  good_resultants := [false, false, false];

  if delta0 ne 0 and IsSquarefree(delta0) and I!Evaluate(DTk,0) mod delta0 eq 0 then 
    good_resultants[1] := true;
  end if;

  if delta1 ne 0 and IsSquarefree(delta1) and I!Evaluate(DTk,-1) mod delta1 eq 0 then
    good_resultants[2] := true;
  end if;

  if delta2 ne 0 and IsSquarefree(delta2) and delta2 mod 2 ne 0 and I!(2^(Degree(Tk)-1)*Evaluate(DTk,-1/2)) mod delta2 eq 0 then 
    good_resultants[3] := true;
  end if;

  cases := [];

  for D0 in [ D0 : D0 in Divisors (delta0) ] do

    for D1 in [ D1 : D1 in Divisors (delta1) | Gcd (D0, D1) eq 1 ] do

      for D2 in [ D2 : D2 in Divisors (delta2) | Gcd (D0, D2) eq 1 and Gcd (D1, D2) eq 1 ] do

        D := [D0, D1, D2];

        for alpha0 in [ alpha0 : alpha0 in Divisors(I!(Ck/Gcd(D0^2*D1^2*D2^2, Ck))) ] do

          for alpha1 in [ alpha1 : alpha1 in Divisors(I!(Ck/Gcd(D0^2*D1^2*D2^2, Ck)/alpha0)) | Gcd(alpha0,alpha1) eq 1 and alpha0*alpha1 mod 2 eq 0 and alpha0 ge alpha1 ] do

            for alpha2 in [ alpha2 : alpha2 in Divisors(I!(Ck/Gcd(D0^2*D1^2*D2^2, Ck)/(alpha0*alpha1))) | Gcd (alpha0, alpha2) eq 1 and Gcd (alpha1, alpha2) eq 1 ] do

              // once alpha0,alpha1,alpha2 are known, alpha3 is determined.
              alpha3 := I!(Ck/Gcd(D0^2*D1^2*D2^2, Ck)/(alpha0*alpha1*alpha2));

              possible_d := [[],[],[]];

              // If we have good resultants, then by the descent proposition any prime dividing D_i cannot divide alpha3
              for i in [1..3] do
                if good_resultants[i] then 
                  for q in PrimeFactors (D[i]) do 
                    if alpha3 mod q eq 0 then 
                      continue alpha2;
                    end if;
                  end for;

                  // When the resultant is good, we also have only one choice for d_i
                  possible_d[i] := [d : d in [I!(D[i]^2/Gcd(D[i]^2,Ck))] | Gcd (d, alpha0*alpha1*alpha2*alpha3) eq 1 ];
                else 
                  possible_d[i] := [d : d in Divisors(I!(D[i]^2/Gcd(D[i]^2,Ck))) | Gcd (d, alpha0*alpha1*alpha2*alpha3) eq 1];
                end if;
              end for;

              for d0 in [ d0 : d0 in possible_d[1] | Gcd(d0, alpha0*alpha1*alpha2*alpha3) eq 1 ] do

                for d1 in [ d1 : d1 in possible_d[2] | Gcd(d1, alpha0*alpha1*alpha2*alpha3*d0) eq 1 ] do

                  for d2 in [ d2 : d2 in possible_d[3] | Gcd(d2, alpha0*alpha1*alpha2*alpha3*d0*d1) eq 1 ] do

                    // Note that neither d3 nor dminus1 affect the coefficients. d3*dminus1 is determined once we have d0,d1,d2, so we just check the coprime condition.
                    d3dminus1 := I!(D0^2*D1^2*D2^2/Gcd(D0^2*D1^2*D2^2,Ck)/(d0*d1*d2));

                    if Gcd (d3dminus1, alpha0*alpha1*alpha2*alpha3*d0*d1*d2) ne 1 then 
                        continue d2;
                    end if;

                    // Au_1^n - Bu_0^n = 1
                    A := alpha1*D1/d1;
                    B := alpha0*D0/d0;

                    eq0 := [A, B];

                    // Cu_2^n - 2Bu_0^n = 1
                    C := alpha2*D2/d2;

                    eq1 := [C, 2*B];

                    // 2Au_1^n - Cu_2^n = 1
                    eq2 := [2*A, C];

                    Append (~cases, [eq0,eq1,eq2]);
                    //cases := cases join {[eq0,eq1,eq2]};

                  end for;  // d2
                end for; // d1
              end for; // d0

            end for; // alpha2
          end for; // alpha1
        end for; // alpha0

      end for; // D2
    end for; // D1
  end for; // D0

  return cases;
end function;





D:=EllipticCurveDatabase();

// Calculates the set of possible conductors of the Galois representation associated to the equation Ax^n + By^n + Cz^n = 0 using
//  James' formula
function levels(A, B, C);

    R := Numerator(A*B*C)*Denominator(A*B*C);

    r := rad2(R);
    v2 := Valuation (A*B*C, 2);

    if v2 eq 0 or v2 ge 5 then
        N := [2*r];
    elif v2 eq 1 then
        N := [2*r, 32*r];
    elif v2 eq 2 or v2 eq 3 then
        N := [2*r, 8*r];
    elif v2 eq 4 then
        N := [r];
    else
        // Note the discrepency between this case and the corollary. This is because if v2 < 0, N = r if and only if v2 = 4-p, which depends on p.
        //  However, this program is working with arbitrary p, so we cannot filter this out.
        N := [r, 2*r, 8*r, 32*r];
    end if;

  return N;
end function;



// Generates the set of all possible levels arising from the systems of equations in cases.
function generate_levels(cases);

  level_list := {};

  for c in cases do

    levels0 := levels (c[1][1], c[1][2], -1);
    levels1 := levels (c[2][1], c[2][2], -1);
    levels2 := levels (c[3][1], c[3][2], -1);

    level_list := level_list join Set (levels0 cat levels1 cat levels2);

  end for;

  return level_list;
end function;

// Returns max (Abs(max_p (v_p(A))), Abs(max_p(v_p(B)))), where max_p ranges over primes p
function max_valuation (A,B);

  max_so_far := 0;

  for p in Set(PrimeFactors(Numerator(A)) cat PrimeFactors(Denominator(A)) cat PrimeFactors(Numerator(B)) cat PrimeFactors(Denominator(B))) do

    current := Max (Abs(Valuation (A, p)), Abs(Valuation (B, p)));

    if current gt max_so_far then 
      max_so_far := current;
    end if;
  
  end for;

  return max_so_far;
end function;


// Tries to eliminate the possibility of the form f being associated to the elliptic curve arising from a putative solution (x,y)=(a,b) A0x^p - B0y^p = 1 at l
// where coeffs = [A0, B0], with A0, B0 rational, and vars = [a^p, b^p], where a^p, b^p are in F_l
// We assume that p is at least 5 so that 2 and 3 are never eliminated. Further, the coefficients cannot have any p-th powers, so any prime p smaller than the
//  maximum exponent cannot be eliminated.
function modular_method (coeffs, vars, f, l);
  
  A0 := coeffs[1];
  B0 := coeffs[2];

  ap := vars[1];
  bp := vars[2];
  
  // In order to later define the elliptic curve, one of the terms must be even. If neither coefficient is even, then we cannot determine ahead of time
  //  which term should play the role of "B" in the modular method. Hence we assume that one of the coefficients is even.
  assert Valuation(A0*B0, 2) ge 1;
  
  k := GaloisField(l);
  k<X> := PolynomialRing (k);

  // Create the elliptic curve E: Y^2 = X(X-A)(X+B) over F_l, where A = -1 and B is even and then calculates a_l(E).
  // First, determine B. Since B corresponds to the even term in the general equation Ax^p + By^p + Cz^p = 0. Our equation is A0a^p - B0b^p = 1.
  // Thus if A0 is even, B = A0*a^p. If B0 is even, B = -B0*b^p
  if Valuation(A0, 2) ge 1 then
    B := k!(A0*ap);
  else
    B := k!(-B0*bp);
  end if;

  alf := Coefficient (f, l);

  // If the elliptic curve would be singular after reducing mod l, then Norm((l+1)^2 - a_l(f)^2) eq 0
  if B eq 0 or B eq 1 then
    diffs := Integers()!Norm((l+1)^2 - alf^2);
  else
    E := EllipticCurve (X*(X+1)*(X+B));
    alE := TraceOfFrobenius (E);

    diffs := Integers()!Norm(alE - alf);
  end if;

  if diffs eq 0 then
    return {0};
  else
    largest_valuation := max_valuation(coeffs[1], coeffs[2]);

    if largest_valuation eq 0 then 
      primes_excluded_by_valuation := {};
    else
      primes_excluded_by_valuation := Set(PrimesUpTo(largest_valuation));
    end if;

    // In addition to the primes given by diffs, it is assumed that p doesn't divide the coefficients, that p >=5, and that the exponents of the prime factorization of the
    //  coefficients are less than p.
    return (Set(PrimeDivisors(diffs)) join {2,3,l} join Set(PrimeDivisors(Numerator(&*coeffs)*Denominator(&*coeffs))) join primes_excluded_by_valuation);
  end if;

end function;


// Returns the intersection of a and b, where a and b are sets of prime numbers. We assume that a and b are either finite
//  sets of primes, or {0}
// Throughout this program, {0} is used to denote the set of all primes. 
//  Thus if a is a finite set of primes and b = {0}, a intersect b should return a.
//  Similar when a = {0} instead.
function intersect_primes (a, b);
  if a eq {0} then
    return b;
  elif b eq {0} then 
    return a;
  else 
    return a meet b;
  end if;
end function;


// Runs the Signature (p,p,p) recipe for the modular method, using the extra structure that we are in the system of three equations
//  A0u1^p - B0u0^p = 1
//  A1u2^p - B1u0^p = 1
//  A2u1^p - B2u2^p = 1
// where Ai, Bi are rational numbers and Numerator(Ai),Numerator(Bi),Denominator(Ai),Denominator(Bi) are pairwise coprime. We further assume that 
//  the l-adic valuation of any coefficient is less than 5, otherwise one could absorb it into the variables.
// c = [ [A0,B0], [A1,B1], [A2,B2] ]
// level_list set of precomputed levels that could arise from the descent
// space_list is the space of newforms associated to each level in level_list
function modular_method_loop (c, level_list, space_list);

  levels_per_equ := [];

  for equ in c do
    Append (~levels_per_equ, levels(equ[1],-equ[2], -1));
  end for;


  //  A0*u1^p - B0*u0^p = 1
  //  A1*u2^p - B1*u0^p = 1
  //  A2*u1^p - B2*u2^p = 1
  A0 := c[1][1]; B0 := c[1][2];
  A1 := c[2][1]; B1 := c[2][2];
  A2 := c[3][1]; B2 := c[3][2];


  use_equ := [true, true, true];

  // check to see which equations are computationally feasable to use the modular mehtod on based on whether the space of forms has been computed.
  // Whether or not an equation is feasable is stored in use_equ
  for i in [1..3] do
    for N in levels_per_equ[i] do
      index := Index(level_list, N);
      if index eq 0 then
        use_equ[i] := false;
        continue i;
      end if;
    end for;
  end for;


  // If a prime divides both coeficients of one variable, and not the level of the third equation, then we have a very rigid structure.
  // These are the primes that satisfy Remark 5.2.6 (2) for each of the three equations.
  interesting_primes := <
    [ l : l in Set(PrimeDivisors(Numerator(A1))) meet Set(PrimeDivisors(Numerator(B2))) | &*levels_per_equ[1] mod l ne 0 and l ge 3 and l le 20000 ], // conditions for modular on just the first equation
    [ l : l in Set(PrimeDivisors(Numerator(A0))) meet Set(PrimeDivisors(Numerator(A2))) | &*levels_per_equ[2] mod l ne 0 and l ge 3 and l le 20000 ], // conditions for modular on just the second
    [ l : l in Set(PrimeDivisors(Numerator(B0))) meet Set(PrimeDivisors(Numerator(B1))) | &*levels_per_equ[3] mod l ne 0 and l ge 3 and l le 20000 ]  // conditions for modular on just the third equation
  >;

  // See Remark 5.2.6 (2). When we view the system modulo l, where l is one of the primes in interesting_primes, then there is only one option for
  //  each of the variables in each equation.
  vars := [ [1/A2, -1/B1], [-1/B2, -1/B0], [1/A0, 1/A1] ];

  for i in [1..3] do
    if use_equ[i] then
      for l in interesting_primes[i] do
        //print "short eliminate with l =", l;
        k := GaloisField(l);
        bad_primes := {};

        for N in levels_per_equ[i] do

          for f_orbit in space_list[Index(level_list, N)] do
            f := f_orbit[1];

              primes_after_modular := modular_method (c[i], vars[i], f, l);

              if primes_after_modular eq {0} then
                continue l;
              // If we've reduced the set of possible primes to a finite list, then we can move to the next newform.
              else
                bad_primes := bad_primes join primes_after_modular;
              end if;

          end for; // f_orbit loop
        end for; // N loop

        //If we've made it through all the forms, then the modular method has succeeded
        return bad_primes;
      end for; // l loop
    end if;

    //If we've ran out of primes l, then the modular method in this structure has failed.
  end for; // i loop.

  //print "moving to long eliminate";



  bad_primes := {};

  // Each nested loop represents either an intersection or a union as in Remark 5.2.6 (3) and (4). 
  // From outside in we have: Union over levels -> Union over newforms -> Intersection across auxillary primes l -> Union over solutions to the system mod l.
  // However, if we find a single auxillary prime l such that the set of bad_primes for a triple of newforms is finite, then we move to the next triple. Hence, the 
  //  intersection is across the universe of bad_primes with this single finite set, and is thus equal to the finite set. Thus this intersection is supressed in the program.
  // This loop represents the Union over levels. All the bad primes are stored bad_primes.
  for N in [ [N0,N1,N2] : N0 in levels_per_equ[1], N1 in levels_per_equ[2], N2 in levels_per_equ[3] ] do

    //print "Levels:", N;

    forms_at_levels := <>;

    // Creates the set S_2(N) or S_2(N0,N1) or S_2(N0,N1,N2) depending on how many equations we can use
    // If we can use an equation, then we'll get the space of newforms at level N for each equation. Otherwise, we use [[-1]] as a placeholder so that the we can still iterate over triples
    for i in [1..3] do
      if use_equ[i] then
        forms_at_level := space_list[Index(level_list, N[i])];

        // If there are no forms at this level, then no solution exists, so we can move on.
        if #forms_at_level eq 0 then
          continue N;
        end if;

        Append (~forms_at_levels, forms_at_level);
      else
        Append (~forms_at_levels, [[-1]]);
      end if;
    end for;

    // If we can't use any equation, the the modular method exceeds our reasonable computational ability
    if use_equ[1] eq false and use_equ[2] eq false and use_equ[3] eq false then
      // Returns {0} to indicate that all primes are still possible.
      return {0};
    end if;

    // Gets a triple of forms, one from each Galois orbit, which we will try to eliminate.
    // This loop represents the Union over newforms
    for forms in < <f0, f1, f2> : f0 in forms_at_levels[1][1], f1 in forms_at_levels[2][1], f2 in forms_at_levels[3][1] > do

        //print "Current forms:", forms;

        // Primes appropriate for using the equations in use_equ
        // This loop represents the Intersection across primes. 
        // Once we find a single prime l such that the modular method reduces the set of possible primes to a finite list for this triple of newforms, we move to the next triple.
        for l in [ l : l in PrimesUpTo(1000) | &*N mod l ne 0 and l ge 3 ] do

          //print "Trying l =", l;
          //print "We'll use eqs:", use_equ;

          k := GaloisField(l);
          R<x> := PolynomialRing(k);

          // The next three loops over u0p, u1p, and u2p function as the Union over the solutions of the system when viewed modulo q. 
          // If the set {p prime : p | B_q^(i)(f_i, w) for all i=0,1,2, or p = q} as in Corollary 5.2.5 is infinite for any w in W_q, then the whole union is infinite and thus no information
          //  is gained from the modular method and so we need to move to the next auxillary prime q. Since q can be quite large, instead of computing W_q first and looping
          //  through each w in W_q, we instead find each w one at a time since there is no guarentee we will need to loop over all of W_q.
          for u0p in k do
            for u1p in k do
              if k!(A0*u1p - B0*u0p) ne 1 then
                continue;
              end if;

              for u2p in k do
                if k!(A1*u2p - B1*u0p) ne 1 or k!(A2*u1p - B2*u2p) ne 1 then
                  continue;
                end if;

                vars := [ [u1p, u0p], [u2p, u0p], [u1p, u2p] ];

                // We compute the set {p prime : p | B_q^(i)(f_i, w) for all i=0,1,2, or p=q } as in Corollary 5.2.5
                // The set is equal to the intersection of the three sets {p prime : p | B_q^(i)(f_i, w), or p = q}
                primes_remaining := {0}; // We use 0 as a placeholder to show that every prime exponent is still possible.

                // Run the modular method on each possible equation
                for i in [1..3] do
                  if use_equ[i] then
                    primes_after_modular := modular_method (c[i],vars[i],forms[i],l);

                    primes_remaining := intersect_primes (primes_remaining, primes_after_modular);
                  end if;
                end for;

                // If we've managed to eliminate all but a finite set of primes for this triple using l, then we can move on to the next triple. Otherwise, we need to try another l for this triple
                if primes_remaining ne {0} then
                  bad_primes := bad_primes join primes_remaining;
                  continue forms;
                else
                  continue l;
                end if;

              end for; //u2p loop
            end for; //u1p loop
          end for; // U loop.

          // If we've made it out of the U loop, then we've eliminated the possibility that the triple of forms could have came from our descent except possibly at the finite set bad_primes
          continue forms;

        end for; // l loop.

        // If we've made it out of the l loop, then we've ran out of primes to try and thus the modular method has failed.
        return {0};

    end for; //forms loop
  end for; // levels loop

  // If we've made it through all of the forms and levels, then the modular method has succeeded
  return bad_primes;
end function;

// Returns the true if n1 < n2, where n1 and n2 are positive integers. Otherwise it returns false. If either is -1, then it is automatically bigger than any natural number.
function compare (n1, n2);

    if n2 eq -1 and n1 ne -1 then 
        return true;
    elif n1 eq -1 then
        return false;
    else 
        return n1 lt n2;
    end if;
    

end function;

// Returns min (n1, n2), where n1 and n2 are natural numbers and -1 represents a number bigger than any natural number.
function modified_min (n1, n2);
  if compare (n1, n2) then 
    return n1;
  else 
    return n2;
  end if;
end function;


// Given rational numbers A, B and real rho > 1, this function finds an upper bound on n in the equation
//  Ax^p - By^p = 1, where it is assume that Denominator(B) | b^n.
// Based on Theorem 7.3.1
function find_bound_rho (A, B, rho);

    lambda := Log(rho);
    n0 := rho^5;

    // print n0;

    alpha1 := A/B; 
    a1 := (rho - 1)*Abs(Log(alpha1)) + 2*Log(Height(alpha1));

    A2 := (rho - 1)/n0 * (2/B + Abs(Log(A/B))) + 2 * Max(1/n0 * Log(1/A * (B+1))+1,1);

    // We don't meet all of the assumptions.
    if a1 + A2 lt 4*Max(1,lambda) or 1/a1 + 1/A2 gt Min(1, 1/lambda) then 
        return -1;
    end if;

    A3 := (Log(n0))^2;

    R1 := 4/lambda + 4/Log(n0) + lambda/(Log(n0))^2;
    S1 := 1/Log(n0) + 1/lambda;

    // // print R1, S1;

    B1 := a1*A2*R1^2/(9*lambda);
    B2 := 2*R1*a1/(3*Log(n0)) + 2*A2*R1/(3*Log(n0));
    B3 := 16*2^(1/2)/3*(a1*A2)^(1/2)*S1^(3/2)*(Log(n0))^(-1/2);
    B4 := (Log(a1*A2*S1^2/lambda) + 3/2*lambda + 3/20)/A3 + Log(A3)/A3 + 2/Log(n0);

    // // print B1,B2,B3,B4;

    C := Log(2/B)/A3 + (B1+B2+B3+B4);

    n2 := 1/(A2 * (Exp(-(Log(lambda)+1.56)) - 1/a1));

    // print n2;

    n1 := 2;

    //print C;

    R := RealField();

    // Since n/log^2(n) is an increasing function, we can use a binary search to find the smallest n1 such that n1*log 2/log^2(n1) > C
    lo := 8; hi := 10^18; // 8 = first integer above e^2
    while lo lt hi do
        mid := (lo + hi) div 2;
        if mid/(Log(mid))^2 gt C/Log(2) then 
            hi := mid; 
        else 
            lo := mid + 1; 
        end if;
    end while;
    n1 := lo;

    //print n1;

    return Max (Max (n0, n1), n2);

end function;


// Given rational numbers A, B, this function finds an upper bound on n in the equation
//  Ax^p - By^p = 1, where it is assume that Denominator(B) | b^n.
// by trying different values for rho. Based on Theorem 7.3.1
function find_bound (A, B);

    rho := 1.5;

    best_bound := find_bound_rho (A, B, rho);
    best_rho := rho;

    while rho lt 10 do 

        rho +:= 0.05;

        //print "Trying:", rho;

        new_bound := find_bound_rho (A, B, rho);

        if compare (new_bound, best_bound) then 
            best_bound := new_bound;
            best_rho := rho;
        end if;

    end while;

    return <Ceiling(best_bound), best_rho>;

end function;


// Given rational numbers A, B and real rho > 1, this function finds an upper bound on n in the equation
//  Ax^p - By^p = 1, where it is assume that Denominator(B) | b^n.
// Based on Remark 7.3.8
function bound_equation (A, B);

  // Need to rule out the b = 1 solution. See Lemma 7.3.3. IsPower(n) cannot handle when n=1, so it is checked seperately
  if Denominator (B) eq 1 and Denominator((1+B)/A) eq 1 and ((1+B)/A eq 1 or IsPower(Integers()!((1+B)/A))) then 
    return <-1, -1>;
  // Need to rule out the b = -1 solution. See Lemma 7.3.3. IsPower(Abs(n)) cannot handle when Abs(n)=1, so it is checked separately. 
  //  Additionally, IsPower(n) requires n > 0. Since A,B>0, it is possible that (1-B)/A = 0, we need to check this too.
  elif Denominator (B) eq 1 and Denominator((1-B)/A) eq 1 and (1-B)/A ne 0 and ((1-B)/A eq -1 or IsPower(Integers()!(Abs((1-B)/A)))) then 
    return <-1, -1>;
  end if;

  n1 := find_bound (A, B);
  n2 := find_bound (B, A);

  if compare (n1[1], n2[1]) then
      return n1;
  else 
      return n2;
  end if;

end function;

// This function searches for suitable auxillary primes l such that we can apply Corollary 5.2.10 to the system of equations
//  A0u1^p - B0u0^p = 1
//  A1u2^p - B1u0^p = 1
//  A2u1^p - B2u2^p = 1
// where Ai, Bi are rational numbers, when viewed modulo the auxillary prime
// c = [ [A0,B0], [A1,B1], [A2,B2] ] denotes the system
// primes is either a finite set of primes p that are possible exponenets for the system, or {0}, which denotes that every prime needs to be eliminated
// bound is the largest prime that needs to be eliminated, stemming from the theory of linear forms of logarithms.
function local_kraus (c, primes);

  A0 := c[1][1];
  B0 := c[1][2];

  A1 := c[2][1];
  B1 := c[2][2];

  A2 := c[3][1];
  B2 := c[3][2];

  // We never try to eliminate 2.
  bad_primes := {2};

  // Gets a bound on the size of n using Theorem 7.3.1
  log_bound := modified_min (modified_min (bound_equation (A0, B0)[1], bound_equation (A1, B1)[1]), bound_equation (A2, B2)[1]);

  print "log_bound =", log_bound;

  if log_bound eq -1 then 
    print "CANNOT FIND BOUND";
    return {0};
  end if;

  // {0} denotes all primes. Thus we eliminate all primes up to the bound
  if primes eq {0} then
    print "trying local kraus to eliminate all primes";
    primes := [ p : p in PrimesUpTo(log_bound) | p ge 3 ];
  // Otherwise, we eliminate all prescribed primes up to the bound.
  else
    print "trying local kraus to eliminate remaining primes";
    primes := [ p : p in primes | p ge 3 and p le log_bound ];
  end if;

  // for prime exponents up to bound, show that no solutions exist
  for p in primes do

    // Look at the system mod l for l = 1 mod p
    // Note that the upper bound on the interval p^4 is given by Kraus' conjecture. However, this is often too large for
    //  MAGMA's PrimesInInterval function, so we arbitrarily search instead just up to p*100. This can be adjusted.
    //for l in [l : l in PrimesInInterval(2*p, Min(p*100, p^4)) | l mod p eq 1 and Denominator(A0*B0*B1*A1*A2*B2) mod l ne 0 ] do

    for k in [2..p^3 by 2] do 
        l := k*p + 1;

        if not IsPrime(l) or Denominator(A0*B0*B1*A1*A2*B2) mod l eq 0 then 
            continue k;
        end if;

      n := Integers()!((l-1)/p);

      Fl := GaloisField(l);

      // We know that H is cyclic. Thus let g be a generator for H so that  H = < g^p > join 0.
      gp := PrimitiveElement(Fl)^p;
      H := [gp^i : i in [0..n-1]] cat [Fl!0];

      A0H := Set([ Fl!(A0*u) : u in H ]);
      B0H := Set([ Fl!(B0*v + 1) : v in H ]);

      if A0H meet B0H eq {} then
        continue p;
      end if;

      if Numerator(B0) mod l ne 0 then
        B1H := Set([ Fl!(B1*u + 1) : u in H ]);

        CH := Set([ Fl!(A1*B0^(-1)*(w-1)) : w in A0H meet B0H ]);

        if B1H meet CH eq {} then
          continue p;
        end if;
      end if;

      if Numerator(A0) mod l ne 0 then
        A2H := Set ([ Fl!(A2*u) : u in H ]);

        DH := Set([ Fl!(B2*A0^(-1)*w + 1) : w in A0H meet B0H ]);

        if A2H meet DH eq {} then
          continue p;
        end if;
      end if;

    end for;

    bad_primes := bad_primes join {p};
  end for;

  return bad_primes;
end function;



// Tries to eliminate the system of equations for every exponent up to the bound from having solutions
// First, we check if any of the equations are of the form of DM
// Next, we check if there is the trivial solution to the system
// Then we run the modular method
// Finally, we use local_kraus
function eliminate (c, level_list, space_list);

  A0 := c[1][1];
  B0 := c[1][2];

  A1 := c[2][1];
  B1 := c[2][2];

  A2 := c[3][1];
  B2 := c[3][2];

  // DM Check
  if (Denominator(A0) eq 1 and Denominator(B0) eq 1 and A0*B0 eq 2) or (Denominator(A1) eq 1 and Denominator(B1) eq 1 and A1*B1 eq 2) or (Denominator(A2) eq 1 and Denominator(B2) eq 1 and A2*B2 eq 2) then
    print "DM";
    return {};
  end if;

  // If A = B \pm 1, for all three equations, then there is a (1,1,1) or (-1,-1,-1) solution for all n
  if  (A0 eq B0 + 1 or A0 eq B0 - 1) and (A1 eq B1 + 1 or A1 eq B1 - 1) then
    print "consistent";
    return {0};
  end if;

  // Gets the list of bad primes after running modular method on the first equation
  //  {0} indicates that the modular method failed
  bad_primes_after_modular := modular_method_loop (c, level_list, space_list);

  if bad_primes_after_modular ne {0} then
    print "was eliminated and has", bad_primes_after_modular, "left";
  end if;

  bad_primes_after_kraus := local_kraus (c, bad_primes_after_modular);

  return bad_primes_after_kraus;

end function;



function run_k (k, min);

  assert k mod 2 eq 0;

  print "generating cases";

  cases := SetToSequence(Set(generate_cases (k)));
  llist := generate_levels (cases);


  print "generating forms";

  // generates global list of spaces of modular forms
  level_list:=[];
  space_list:=[];

  for N in llist do
    if N le 10000 then
      H:=Newforms(CuspidalSubspace(ModularForms(Gamma0(N))));
      Append(~level_list,N);
      Append(~space_list,H);
    end if;

  end for;

  bad_cases := <>;

  total := #cases;
  current := min-1;

  for c in cases[min..total] do

    current := current + 1;

    print "(", current, "\\", total, ") Trying to eliminate case =", c;

    bad_primes := eliminate (c, level_list, space_list);

    // A result by Pinter shows that if k <= 58 and even, then there are no solutions when p = 2
    if k le 58 then
      bad_primes := bad_primes diff {2};
    end if;

    if bad_primes ne {} then
      Append (~bad_cases, <c, bad_primes>);
    end if;

    if current mod 5000 eq 0 then
      print "(", current, "\\", total, ") Bad cases so far:", bad_cases;
    end if;

  end for;

  return bad_cases;

end function;
