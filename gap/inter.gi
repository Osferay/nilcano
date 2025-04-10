#######################################################################
## Helper function to calculate the intersection of U with a term    ##
## of the efa series of G                                            ##
#######################################################################

InstallGlobalFunction( "IntersectionSeriesTerm", function(U, term)

    local   gens,   #Generators of U
            pos;    #Position of the first generator that is in U and term

    #Trivial case
    if Size(term) = 1 or Size(U) = 1 then 
        return rec( cross := Subgroup(term!.ParentAttr, []), gens :=[] ); 
    fi;
    
    gens := Cgs(U);
    pos  := 1;
    while ( not gens[pos] in term ) do
        pos := pos+1;
        if pos > Length(gens) then 
            return rec( cross := Subgroup( term!.ParentAttr, [ ] ),
                        gens  := [ One( term!.ParentAttr ) ] );
        fi;
    od;

    return rec( cross := Subgroup( term!.ParentAttr, gens{[pos..Length(gens)]} ),
                gens  := gens{[pos..Length(gens)]} );

end );

#######################################################################
## Global function to calculate the intersection of U with a the     ##
## terms of the efa series of G                                      ##
#######################################################################

InstallGlobalFunction( "InducedIntersectionSeries", function(G, U) 
    
    local   series,     #Series of G
            iseries,    #Intersection with the series
            i,          #Term of the series
            cross;      #Intersection term

    series  := PcpSeries(G);
    iseries := [];
    i       := 1;
    cross   := IntersectionSeriesTerm(U, series[i]).cross;

    while Size(cross) <> 1 do 
        if not cross in iseries then Add(iseries, cross); fi;
        i     := i + 1;
        cross := IntersectionSeriesTerm(U, series[i]).cross;
    od;

    Add(iseries, cross);
    
    return iseries;

end );

#######################################################################
## Global function to calculate the pcps of the induced series       ##
##                                                                   ##
#######################################################################

InstallGlobalFunction( "PcpsOfInducedIntersectionSeries", function(G, U)

    local   cross,  #Intersection series
            pcps,   #Pcps to return
            i;      #Bucle variable

    cross  := InducedIntersectionSeries(G, U);
    pcps   := [];

    for i in [1..Length(cross)-1] do
        Add(pcps, Pcp( cross[i], cross[i+1] ) );
    od;

    return pcps;

end );

#######################################################################
## Local function to calculate the intersection of two cyclic        ##
## subgroups of G                                                    ##
#######################################################################

IntersectionCyclicSubgroupsNilGroups := function(G, U, V)

    local   gU,     #Generator of U
            gV,     #Generator of V
            d1,     #Depth of the generator of U
            d2,     #Depth of the generator of V
            e;      #Lcm of the leading exponent of gU and gV
            
    gU := Cgs(U)[1];
    gV := Cgs(V)[1];
    d1 := Depth( gU );
    d2 := Depth( gV );
    
    if d1 <> d2 then
        return [ ];
    else
        e := Lcm( LeadingExponent( gU ), LeadingExponent( gV ) );
        gU := gU^e;
        gV := gV^e;

        if gU in V and gV in U then
            if gU = gV then
                return [ gU ];
            else
                return [ Cgs(G)[d1]^e ];
            fi;
        else
            return [ ];
        fi;
    fi;

end;

#######################################################################
## Local function to calculate the intersection of two subgroups     ##
#######################################################################

IntersectionSubgroupsNilGroupsSeries := function(G, U, V, ser, Gn, gn, d, p)

    local   G2,     #Second term of ser
            U2,     #Intersection U and G2
            V2,     #Intersection V and G2
            I,      #Intersection U2 and V2
            pI,     #Intersection of p(U) and p(V)
            B,      #Generators of pI
            Un,     #Intersection U and Gn
            Vn,     #Intersection V and Gn
            an,     #Additional values for A
            H,      #Values hu for all generators
            A,      #Exponents of gn to equalize hu and hv
            i,      #Bucle variable
            b,      #Preimage of the generator of pI
            hu,     #Sifting of b in U
            hv,     #Sifting of b in V
            R,      #Representation of d2
            d2,     #Gcd of A{2,...n}
            d1,     #Gcd of A
            x;      #Value to add to the generators

    #Trivial cases
    if U = V then
        I := Cgs(U);

    elif Size(U) = 1 then
        I := [ ];

    elif Size(V) = 1 then
        I := [ ];

    #Cyclic case
    elif Length( Cgs(U) ) = 1 and Length( Cgs(V) ) = 1 then
        I := IntersectionCyclicSubgroupsNilGroups(G, U, V);

    #General Case
    else
        i := 2;
        G2 := ser[i];
        U2  := IntersectionSeriesTerm(U, G2).cross;
        V2  := IntersectionSeriesTerm(V, G2).cross;

        while U2 = U and V2 = V do
            i  := i + 1;
            G2 := ser[i];
            U2 := IntersectionSeriesTerm(U, G2).cross;
            V2 := IntersectionSeriesTerm(V, G2).cross;
        od;   

        I   := IntersectionSubgroupsNilGroupsSeries(G, U2, V2, ser, Gn, gn, d, p);
        I   := ShallowCopy(I);
        
        pI  := IntersectionSubgroupsNilGroups( Image(p), p(U), p(V) );

        if IsEmpty( pI ) then 
            #Do nothing
        elif pI[1] in p(G2) then
            #Do nothing.
        
        else

            Un := IntersectionSeriesTerm(U, Gn).gens[1];
            Vn := IntersectionSeriesTerm(V, Gn).gens[1];
            an := [ Exponents(Un)[d], Exponents(Vn)[d], FactorOrder(gn)];

            H := [];
            A := [];

            for i in [1..Length(pI)] do

                b    := PreImagesRepresentative( p, pI[i]);
                hu   := b * (Sifting(U, b).y)^-1;
                H[i] := hu;
                hv   := b * (Sifting(V, b).y)^-1;
                A[i] := Last(Exponents(hu))-Last(Exponents(hv));
                
            od;
            
            Append( A, an );
            R  := GcdRepresentation( A{[2..Length(A)]} );
            d2 := A{[2..Length(A)]} * R;
            d1 := Gcd( A );
            
            if d2 = 0 and d1 <> 0 then
                

            elif d1 = 0 then
                x := SiftingWithGens(I, H[1]).y;
                Add( I, x, 1);

            else

                b := d2/d1;
                B := R{[1..Length(R)-2]}*(-A[1]/d1);
                B[Length(B)] := B[Length(B)] * an[1];
                Add(B, b, 1);
                Add(H, gn);
                x := MappedVector(B, H);

                if x in G2 then 
                    
                else
                    x := SiftingWithGens(I, x).y;
                    Add(I, x, 1);
                fi;
            fi;
        fi;
    fi;

    I := Filtered( I, x -> x <> One(G) );

    return I;
    

end;

#######################################################################
## Global function to calculate the intersection of two subgroups    ##
#######################################################################

InstallGlobalFunction( "IntersectionSubgroupsNilGroups", function(G, U, V) 

    local   ser,    #Pcp series of G
            Gn,     #Last term of ser
            gn,     #Generator of gn
            d,      #Depth of gn
            p;      #Projection map
    
    ser := PcpSeries(G);
    Gn  := ser[Length(ser)-1];
    gn  := Pcp(Gn)[1];
    d   := Depth(gn);
    p   := NaturalHomomorphismByNormalSubgroup(G, Gn);

    return IntersectionSubgroupsNilGroupsSeries(G, U, V, ser, Gn, gn, d, p);

end );