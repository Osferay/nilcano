SubgroupProductPairCyclic := function(G, U, V)

    local   gU,
            gV,
            e;

    gU := Cgs(U)[1];
    gV := Cgs(V)[1];

    e := Gcd( LeadingExponent( gU ), LeadingExponent( gV ) );
    return rec( P1 := [ gU^e ], P2 := [ One(G) ]);

end;


InstallGlobalFunction( "SubgroupProductPair", function(G, U, V)

    local   ser,    #Series of G
            Gn,     #Last term of ser
            gn,     #Generator of Gn
            d,      #Depth of gn
            p,      #Projection map
            pP1,    #First element of the product pair of the projection
            pP2,    #Second element of the product pair of the projection
            P1,     #First element of the product pair
            P2,     #Second element of the product pair
            I,      #Intersection of p(U) and p(V)
            A,      #Diference of exponents
            i,      #Bucle variable
            b,      #Preimages
            hu,     #Preimage of generators of I in U
            hv,     #Preimage of generators of I in V
            Un,     #Intersection of U with Gn
            Vn,     #Intersection of V with Gn
            R,      #Gcd representation of A
            x,      #Value to add to P1
            y;      #Value to add to P2

    #Trivial cases
    if U = V then
        return rec( P1 := ShallowCopy( Cgs(U) ), P2 := [One(G)] );

    elif Size(U) = 1 then
        return rec( P1 := List( Cgs(V), x -> One(G) ), P2 := ShallowCopy( Cgs(V) ) );

    elif Size(V) = 1 then
        return rec( P1 := ShallowCopy( Cgs(U) ), P2 := List( Cgs(U), x -> One(G) ) );

    #Cyclic case
    elif Length( Igs(G) ) = 1 then
        return SubgroupProductPairCyclic(G, U, V);

    #General Case
    else
        ser := PcpSeries(G);
        Gn  := ser[Length(ser)-1];
        gn  := Pcp(Gn)[1];
        d   := Depth(gn);
        p   := NaturalHomomorphismByNormalSubgroup(G, Gn);
        pP1 := SubgroupProductPair( Image(p), p(U), p(V) );
        pP2 := pP1.P2;
        pP1 := pP1.P1;

        P1 := [];
        P2 := [];
        for i in [1..Length(pP1)] do
            b     := PreImagesRepresentative( p, pP1[i]);
            P1[i] := b *(Sifting(U, b).y)^-1;

            b     := PreImagesRepresentative( p, pP2[i]);
            P2[i] := b *(Sifting(V, b).y)^-1;
        od;

        I   := IntersectionSubgroupsNilGroups( Image(p), p(U), p(V) );
        A   := [];
        hu  := [];
        hv  := [];
        
        for i in [1..Length(I)] do
            
            b    := PreImagesRepresentative( p, I[i]);
            hu[i]:= b * (Sifting(U, b).y)^-1;
            hv[i]:= b * (Sifting(V, b).y)^-1;
            A[i] := Last( Exponents(hu[i]) )-Last( Exponents(hv[i]) );

        od;

        Un := IntersectionSeriesTerm(U, Gn).gens[1];
        Vn := IntersectionSeriesTerm(V, Gn).gens[1];
        Append(A, [ Exponents(Un)[d], Exponents(Vn)[d], FactorOrder(gn)] );

        if ForAll(A, a -> a = 0) then
            Add( P1, One(G) );
            Add( P2, One(G) );

        else 

            R   := GcdRepresentation( A );
            Add( hu, Un );

            x   := R{[1..Length(R)-2]};
            x   := MappedVector( x, hu );
            Add( P1, x );

            Add( hv, Vn^-1 );
            y   := R{[1..Length(R)-3]};
            Add( y, R[Length(R)-1]);
            y   := MappedVector( y , hv);
            Add( P2, y );

        fi;
    fi;

    return rec( P1 := P1, P2 := P2 );

end );

MembershipProductPair := function( G, P1, P2, x)

    local   h1, #
            h2, #
            i,  #Bucle variable
            y,  #
            n,  #
            e,  #
            b,  #
            l;  #

    h1 := One(G);
    h2 := One(G);
    y  := x;
    i  := 1;
    n  := Length(P1);

    while i < n+1 do

        if y = One(G) then
            return rec( h1 := h1, h2 := h2);
        fi;

        i  := Depth(y);
        e  := LeadingExponent(y);
        b  := P1[i]*(P2[i])^-1;
        if b = One(G) then
            return false;
        else
            l  := LeadingExponent(b);
        fi;

        if ( e mod l ) = 0 then
            b  := e/l;
            h1 := h1*P1[i]^b;
            h2 := h2*P2[i]^b;
            y  := P1[i]^(-b) * y * P2[i]^b;
        else
            return false;
        fi;

    od;

    return rec( h1 := h1, h2 := h2);

end;

InstallGlobalFunction( "ProductDecomposition", function(G, U, V, x)

    local   prod,   #Subgroup product pair
            P1,     #
            P2,     #
            d1,     #
            d2,     #
            n,      #
            i;      #

    prod := SubgroupProductPair(G, U, V);
    P1   := prod.P1;
    P2   := prod.P2;

    #Prepare the product pair
    n    := Length( Cgs(G) );
    
    d1   := List( P1, Depth );
    d2   := List( P2, Depth );
    i    := 1;
    while Length(P1) <> n do
        
        if not ( d1[i] = i ) or ( d1[i]> n ) then
            Add( P1, One(G), i );
            Add( d1, Depth( One(G) ), i);
        fi;
        
        i := i + 1;
        if i > Length(P1) then Add(P1, One(G)); Add(d1, Depth( One(G) )); fi;
    od;

    i := 1;
    while Length(P2) <> n do
        
        if not ( d2[i] = i ) or ( d2[i]> n ) then
            Add( P2, One(G), i );
            Add( d2, Depth( One(G) ), i);
        fi;

        i := i + 1;
        if i > Length(P2) then Add(P2, One(G)); Add(d2, Depth( One(G) )); fi;
    od;
    
    return MembershipProductPair(G, P1, P2, x);

end );