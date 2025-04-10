#######################################################################
## Global function to calculate the a reduced element in a basis     ##
#######################################################################

InstallGlobalFunction( "ReducePcpElement", function( elm, basis )

    local   exp,    #Exponents of elm
            l,      #Leading exponents of the elements in the basis
            d,      #Depth of the elements in the basis
            v,      #Reduced preimage
            i,      #Bucle variable
            r,      #Residuo
            x;      #Exponents of the element in the basis

    v     := elm ;
    basis := Reversed(basis);
    exp   := Exponents( v );
    l     := List( basis, LeadingExponent );
    d     := List( basis, Depth);
    

    for i in [1..Length(d)] do

        if exp[ d[i] ]<0 or exp[ d[i] ]>(l[i]-1) then
            r   :=  exp[ d[i] ] mod l[i];
            x   := (exp[ d[i] ] - r)/l[i];
            v   := v * basis[i]^-x;
            exp := Exponents( v );
        fi;
    od;

    return v;

end );

####################################################################
## Generates a random element of G using only generators between  ##
##                                                      m and n   ##
####################################################################

InstallGlobalFunction( "RandomElementRangeGenerators", 
                                function( arg )

    local   G,      #Group given
            n,      #Second argument given
            m,      #Third argument given
            pcp,    #Pcp of g
            rel,    #Relative orders of G
            i,      #Bucle variable
            g;      #Element to return using the range of elements between n and m

    G := arg[1];
    n := arg[2];
    pcp := Pcp(G);

    if Length( arg ) > 2 then
        m := arg[3];
    else
        m := Length( pcp );
    fi;

    pcp := Pcp(G);
    rel := RelativeOrdersOfPcp( pcp );
    g   := [];

    if m > Length( pcp ) then 
        Error("The number m is greater than the number of generators of G."); 
    fi;

        
    if Length( pcp ) = 0 then
        return One( G );
    fi;

    for i in [1..Length( pcp )] do
        if i in [n..m] then
            if rel[i] = 0 then
                g[i] := Random( -1000, 1000 );
            else
                g[i] := Random( 1, rel[i]-1 );
            fi;
        else
            g[i] := 0;
        fi;
    od;

    return MappedVector( g, pcp );

end );

####################################################################
## Generates a random subgroup of G                               ##
## if the input n is given generates a subgroup with n generators ##
####################################################################

InstallGlobalFunction( "RandomSubgroup", function( arg )

    local   G,      #Group given
            cgs,    #Canonical generators of G
            n,      #Second argument
            gens,   #List of generators
            nums,   #Numbers to generate the generators
            r,      #Random integer
            g,      #Random element in G
            i,      #Bucle variable
            U;      #Subgroup to return

    G    := arg[1];
    cgs  := Cgs(G);
    gens := [];
    nums := [];

    if Length(arg) > 1 then
        n := arg[2];
        if n > Length( cgs ) then Error("The number n is greater than the number of generators of G."); fi;
    else
        n := Random( [1..Length( cgs )] );
    fi;


    for i in [1..n] do
        r := Random([1..Length(cgs)]);
        while r in nums do
            r := Random([1..Length(cgs)]);
        od;
        Add( nums, r );
    od;

    Sort(nums);
    
    for i in [1..n] do
        g := RandomElementRangeGenerators(G, nums[i]);
        Add( gens, g );
    od;

    U := Subgroup(G, gens);
    return U;

end );

####################################################################
### Returns true if is less or equal in the order                ###
### 0 << 1 << ... << -1 << ...                                   ###
####################################################################

IntegerOrder := function(a,b)
    if a = 0 then
        return true;
    elif b = 0 then
        return false;
    elif a > 0 then
        if b < 0 then
            return true;
        else
            return a <= b;
        fi;
    else
        if b > 0 then
            return false;
        else
            return b <= a;
        fi;
    fi;
end;   

####################################################################
### Returns true if is less in the order                         ###
### 0 << 1 << ... << -1 << ...                                   ###
####################################################################

IntegerOrderStrict := function(a,b)
    if a = 0 then
        return true;
    elif b = 0 then
        return false;
    elif a > 0 then
        if b < 0 then
            return true;
        else
            return a < b;
        fi;
    else
        if b > 0 then
            return false;
        else
            return b < a;
        fi;
    fi;
end; 

####################################################################
### Returns true if is less or equal in the order                ###
### extended to the exponents of g and h                         ###
####################################################################

ExponentOrder := function(g,h)
    local   e1, #Exponents of g
            e2, #Exponents of h
            i;  #Bucle variable

    e1  := Exponents(g);
    e2  := Exponents(h);

    for i in [1..Length(e1)] do
        if e1[i] <> e2[i] then
            return IntegerOrder( e1[i], e2[i] );
        fi;
    od;
    return true;
end;

####################################################################
### Returns true if g <<= h                                      ###
####################################################################

InstallGlobalFunction( "ConjugacyOrder" , function(g,h) 

    local   fam,ord;

    fam := FamilyObj( g );
    ord := OrderingByLessThanFunctionNC(fam, ExponentOrder);

    return IsLessThanUnder(ord, g, h);

end );

####################################################################
### Sifting algorithm using a sequence                           ###
####################################################################

SiftingWithGens := function(arg)

    local   gen,    #Canonical generators of U
            g,      #Element to sift
            n,      #Number of generators
            d,      #List of depths of the generators
            exp,    #Exponents of the depths of the generators   
            y,      #Element to return such that gy^-1 is in the subgroup
            B,      #Exponent vector of xy^-1
            alp,    #Exponents of the element in each depth
            l,      #List of conditions
            i;      #Bucle variable

    gen := arg[1];
    g   := arg[2];

    if Length(arg) = 2 then  
        n   := Length(gen);
        d   := List( gen, Depth );
        exp := List( gen, Exponents );
        exp := List( [1..n], x -> exp[x][d[x]]);
    else
        n   := arg[3];
        d   := arg[4];
        exp := arg[5];
    fi;
    
    y   := g;
    B   := List( [1..n], x -> 0);
    alp := List( [1..n], x -> Exponents(y)[d[x]]);
    l   := List( [1..n], x -> IntegerOrderStrict( alp[x], exp[x]) );
    
    while not ForAll( l, x -> x = true ) do
        i    := PositionProperty(l, x -> x = false );
        B[i] := Int( alp[i] / exp[i] );
        y    := (gen[i] ^ -B[i]) * y;
        alp := List( [1..n], x -> Exponents(y)[d[x]]);
        l   := List( [1..n], x -> IntegerOrderStrict( alp[x], exp[x]) );
    od;

    return rec( y := y, B := B);

end ;

####################################################################
### Sifting algorithm using a subgroup                           ###
####################################################################

InstallGlobalFunction( "Sifting", function(U, g)

    local   gen,    #Canonical generators of U
            n,      #Number of generators
            d,      #List of depths of the generators
            exp;    #Exponents of the depths of the generators
            
    gen := Cgs(U);
    n   := Length(gen);
    d   := List( gen, Depth );
    exp := List( gen, Exponents );
    exp := List( [1..n], x -> exp[x][d[x]]);

    return SiftingWithGens(gen, g, n, d, exp);

end );

RandomListElements := function(arg)

    local   G,      #Group 
            n,      #Number of random elements
            no_id,  #Flag to not include the identity element
            l,      #List to return
            i,      #Bucle variable
            g;      #Element in each iteration

    G := arg[1];
    n := arg[2];

    if Length(arg) > 2 then no_id := true; fi;

    l := [];
    for i in [1..n] do
        g := Random(G);
        while no_id and g = One(G) do
            g := Random(G);
        od;
        Add(l, g);
    od;

    return l;
end ;

