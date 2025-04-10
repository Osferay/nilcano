
#######################################################################
## Local function to calculate the normalizer of U in G              ##
#######################################################################

NormalizerNilGroupSeries := function(G, U, efa)

    local   genU,   #Generators of U
            N,      #Normalizer of U in G
            H,      #Intersection of the previous step
            Hi,     #Intersection on each step
            i,      #Bucle variable
            h,      #Generator of U/V
            nat;    #Natural homomorphism N->N/V
    
    genU := Reversed( Igs(U) );
    N    := G;
    H  := Subgroup(U, [ genU[1] ]);

    Info( InfoConjugacySubgroups, 1, StringFormatted("The algorithm has to process {} layers.", Length(genU)-1 ) );

    for i in [2..Length(genU)] do
    
        Hi := Subgroup(U, genU{[1..i]});
        h   := Pcp(Hi, H)[1];
        nat := NaturalHomomorphismByNormalSubgroup(N, H);
        N   := PreImage( nat, CentralizerNilGroup( Image(nat), nat(h) ) );
        H   := Hi;
        Info( InfoConjugacySubgroups, 1, StringFormatted("Layer {} done.", i) );
    od;

    return N;

end;

#######################################################################
## Global function to calculate the normalizer of U in G             ##
#######################################################################

InstallGlobalFunction( "NormalizerNilGroup", function(G,U)

    if not IsSubgroup(G,U) then
        Error( "U has to be a subgroup of G.");
    fi;

    return NormalizerNilGroupSeries(G, U, EfaSeries(G));

end );

#######################################################################
## Local function to calculate the preimage of an element            ##
#######################################################################

PreImageByQuotient := function(G, hom, elm )

    local   pcp,
            gens,
            matrix,
            exp,
            solv;

    pcp    := Pcp( Image(hom) );
    gens   := Cgs(G);
    matrix := List( gens, x-> ExponentsByPcp( pcp, hom(x) ) );
    exp    := ExponentsByPcp( pcp, elm );

    solv   := PcpSolutionIntMat( matrix, exp );
    return MappedVector( solv, gens );

end;

#######################################################################
## Local function to calculate is two subgroups of G are conjugated  ##
#######################################################################

IsConjugateSubgroupsNilGroup := function(G, U, V)
    local   x,      #Conjugating element of U and V
            Ui,     #Conjuate of U in each step
            H,      #Intersection of previous step of U
            K,      #Intersection of previous step of V
            N,      #Normalizer of W
            i,      #Bucle variable
            Hi,     #Intersection in each step of U
            Ki,     #Intersection in each step of V
            h,      #Generator of U/W
            k,      #Generator of V/W
            nat,    #Natural homomorphism N->N/W
            conj,   #Conjugating of h and k
            xi,     #Conjugating element in each step
            genU,   #Generators of U
            genV;   #Generators of V

    #Catch trivial case
    genU := Reversed( Cgs(U) );
    genV := Reversed( Cgs(V) );
    
    if Length(genU) <> Length(genV) then
        return false;
    fi;

    #Start the algorithm
    x  := One(G);
    Ui := U;
    H  := Subgroup(U, [  ]);
    K  := Subgroup(V, [  ]);
    N  := G; 

    if H <> K then
        return false;
    fi;

    Info( InfoConjugacySubgroups, 1, StringFormatted("The algorithm has to process {} layers.", Length(genU) ) );

    for i in [1..Length( genU )] do
        #Take the intersection
        Hi := Subgroup(Ui, genU{[1..i]});
        Ki := Subgroup(V, genV{[1..i]});

        #Get the generators of U/W and V/W
        h   := Pcp(Hi, H)[1];
        k   := Pcp(Ki, K)[1];

        #Define the homomorphism N-> N/W
        nat := NaturalHomomorphismByNormalSubgroupNC(N, H );
        conj:= IsConjugateNilGroup( Image(nat), nat(h), nat(k) );

        if IsBool(conj) then
            return false;
        else
            #They are conjugated, update values
            xi  := PreImageByQuotient( N, nat, conj );
            x   := x * xi;
            H   := Hi^ xi;
            Ui  := Ui^ xi;
            genU:= Reversed( Cgs(Ui) );
            K   := Ki;

            #Update the normalizer
            N   := PreImage( nat, CentralizerNilGroup( Image(nat), nat(k) ) );
        fi;
        Info( InfoConjugacySubgroups, 1, StringFormatted("Layer {} done.", i) );
    od;

    return x;

end;

#######################################################################
## Global function to calculate is two subgroups of G are conjugated ##
#######################################################################

InstallGlobalFunction( "IsConjugateSubgroups", function(G, U, V)

    if not (IsSubgroup(G,U) and IsSubgroup(G,V) ) then
        Error( "U and V have to be subgroups of G.");
    fi;

    if U = V then
        return One(G);
    else
        return IsConjugateSubgroupsNilGroup(G, U, V);
    fi;

end );    

#######################################################################
## Local function to calculate the reduced canonical form            ##
#######################################################################

ReducedCanonical := function(G, U, elms)

    local   nat,    #Natural homomrphism from G to G/U
            kan,    #Canonical conjugate of the image of g by nat
            k,      #Reduced preimage of the canonical conjugate
            v,      #Conjugating element
            N,      #Normalizer
            i;      #Bucle variable

    nat := NaturalHomomorphismByNormalSubgroup(G, U );
    kan := CanonicalConjugateElements( Image(nat), List( elms, nat ) );
    k   := [];
    v   := [];

    for i in [1..Length(elms)] do
        k[i]:= PreImagesRepresentative(nat, kan.kano[i]);
        v[i]:= PreImagesRepresentative(nat, kan.conj[i]);
        k[i]:= ReducePcpElement(k[i] , Cgs(U));
    od;

    N   := PreImage( nat, kan.cent[1] );

    return rec( kano := k, conj := v, N := N );

end;

#######################################################################
## Local function to check if two elements are conjugate in the      ##
## quotient                                                          ##
#######################################################################

IsCanonicalConjugateQuotient := function(G, U, elms)

    local   nat,    #Natural homomrphism from G to G/U
            kan,    #Canonical conjugate of the image of g by nat
            k,      #Reduced preimage of the canonical conjugate
            v,      #Conjugating element
            N,      #Normalizer
            i;      #Bucle variable

    nat := NaturalHomomorphismByNormalSubgroup(G, U );
    kan := IsCanonicalConjugateElements( Image(nat), List( elms, nat ));

    if IsBool(kan) then
        return false;
    else;
        v   := [];

        for i in [1..Length(elms)] do
            v[i] := PreImagesRepresentative(nat, kan.conj[i]);
        od;
        
        k := PreImagesRepresentative(nat, kan.kano);
        k := ReducePcpElement(k , Cgs(U));
        N := PreImage( nat, kan.cent );

        return rec( kan := k, v := v, N := N );
    fi;

end;

#######################################################################
## Local function to calculate the canonical conjugate subgroup of  ##
## a subgroup in G                                                   ##
#######################################################################

CanonicalConjugateSubgroupNilGroup := function(G, U)

    local   gU,     #Generators of U 
            N,      #Normalizer of K
            x,      #Conjugating element
            gK,     #Generators of K
            Ui,     #Subgroup Ui in the current step
            K,      #Canonical subgroup
            i,      #Bucle variable
            u,      #Generator on each step
            kan;    #Canonical conjugates of h

    gU := Reversed( Cgs(U) );
    N  := G; 
    x  := One(G);
    Ui := Subgroup( U, [ ]);
    gK := [];

    Info( InfoConjugacySubgroups, 1, StringFormatted("The algorithm has to process {} layers.", Length(gU) ) );

    for i in [1..Length(gU)] do

        u   := NormedPcpElement( gU[i]^x );
        kan := ReducedCanonical(N, Ui, [u]);
        
        x   := x*kan.conj[1];
        Ui  := Subgroup(U, gU{[1..i]} );
        SetCgs(Ui, gU{[1..i]} );
        Ui  := Ui^x;
        
        N   := kan.N;

        Add( gK, kan.kano[1] );
        Info( InfoConjugacySubgroups, 1, StringFormatted("Layer {} done.", i) );
    od;
    
    K  := Subgroup( G, gK );

    return rec( kano := K, conj := x, norm := N);

end;

#######################################################################
## Global function to calculate the canonical conjugate subgroup of  ##
## a subgroup in G                                                   ##
#######################################################################

InstallGlobalFunction( "CanonicalConjugateSubgroup", function(G, U)

    if not IsSubgroup(G,U) then
        Error( "U has to be subgroups of G.");
    fi;

    return CanonicalConjugateSubgroupNilGroup(G, U); 

end );  

######################################################################
## Local function to calculate solve the conjugacy problem in G     ##
## using canonical conjugate elements                               ##
######################################################################

IsCanonicalConjugateSubgroupNilGroup := function(G, U, V)

    local   gU,     #Generators of U 
            gV,     #Generators of V
            N,      #Normalizer of K
            x,      #Conjugating element of U
            y,      #Conjugating element of V
            gK,     #Generators of K
            Ui,     #Subgroup Ui in the current step
            K,      #Canonical subgroup
            i,      #Bucle variable
            u,      #Generator on each step of U
            v,      #Generator on each step of V
            kU;     #Canonical conjugates of 

    gU := Reversed( Cgs(U) );
    gV := Reversed( Cgs(V) );
    N  := G; 
    x  := One(G);
    y  := One(G);
    Ui := Subgroup( U, [ ]);
    gK := [];

    if Length(gU) <> Length(gV) then
        return false;
    fi;

    Info( InfoConjugacySubgroups, 1, StringFormatted("The algorithm has to process {} layers.", Length(gU)-1 ) );

    for i in [1..Length(gU)] do

        u := NormedPcpElement( gU[i]^x );
        v := NormedPcpElement( gV[i]^y );

        kU := IsCanonicalConjugateQuotient(N, Ui, [u,v]);

        if IsBool(kU) then
        
            return false;
        
        else 
            x   := x*kU.v[1];
            Ui  := Subgroup(U, gU{[1..i]} );
            SetCgs(Ui, gU{[1..i]});
            Ui  := Ui^x;

            y   := y*kU.v[2];
        
            N   := kU.N;

            Add( gK, kU.kan );

        fi;
        Info( InfoConjugacySubgroups, 1, StringFormatted("Layer {} done.", i) );
    od;
    
    K    := Subgroup( G, gK );

    return rec( kano := K, conj := [x,y], norm := N);

end;

######################################################################
## Global function to calculate solve the conjugacy problem in G    ##
## using canonical conjugate elements                               ##
######################################################################

InstallGlobalFunction( "IsCanonicalConjugateSubgroups", function(G, U, V)

    if not (IsSubgroup(G,U) and IsSubgroup(G,V) ) then
        Error( "U and V have to be subgroups of G.");
    fi;

    if U = V then
        return One(G);
    else
        return IsCanonicalConjugateSubgroupNilGroup(G, U, V);
    fi;

end );    