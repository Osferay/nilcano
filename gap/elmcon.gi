###########################################################################
## Local function to calculate the centralizer of a set of elements in G ##
###########################################################################

CentralizerNilGroupSeries := function( G, elms, pcps )
    local   C,      #Centralizer of elms in G
            i,      #Bucle variable
            pcp,    #Factor on each step Gi/G(i+1)
            N,      #Subgroup Gi
            fac,    #Factor group C/Gi in each step
            gens,   #Generators of gen
            rels,   #Relation matrix of Gi/G(i+1)
            elm,    #Single elements on elms
            matrix, #Matrix representing the image of the homomorphism f
            null,   #Kernel of f
            stb;    #Elements corresponding to the kernel

    C := G;

    Info( InfoConjugacyElements, 1, StringFormatted("The algorithm has to process {} layers.", Length(pcps)-1) );

    for i in [2..Length(pcps)] do

        pcp := pcps[i]; 
        N   := SubgroupByIgs( G, NumeratorOfPcp(pcp) );

        fac := Pcp(C, N); 
        gens:= AsList(fac);

        rels := ExponentRelationMatrix( pcp );
        stb  := gens;
        for elm in elms do
            if Length( stb ) <> 0 then 

                # set up matrix
                matrix := List( stb, h -> ExponentsByPcp( pcp, Comm(h,elm) ) );
                Append( matrix, rels );

                # get nullspace
                null := PcpNullspaceIntMat( matrix );
                null := null{[1..Length(null)]}{[1..Length(stb)]};
                # calculate elements corresponding to null
                stb  := List( null, x -> MappedVector( x, stb ) );
                stb  := Filtered( stb, x -> x <> x^0 );
            fi;
        od;

        stb := AddIgsToIgs( stb, Igs(N) );
        C   := SubgroupByIgs( G, stb );
        Info( InfoConjugacyElements, 1, StringFormatted("Layer {} done.", i) );

    od;

    return(C);

end;

############################################################################
## Global function to calculate the centralizer of a set of elements in G ##
############################################################################

InstallGlobalFunction( "CentralizerNilGroup", function(G, elms) 

    if not IsList(elms) then
        elms := [elms];
    fi;

    return CentralizerNilGroupSeries(G, elms, PcpsOfEfaSeries(G));

end );

############################################################################
## Local function to check if two elements in G are conjugate             ##
############################################################################

IsConjugateNilGroupSeries := function(G, g, h, pcps )

    local   C,      #Centralizer of elms in G
            k,      #Conjugate element
            i,      #Bucle variable
            pcp,    #Factor on each step Gi/G(i+1)
            c,      #g^k in each step
            N,      #Subgroup Gi
            fac,    #Factor group C/Gi in each step
            gens,   #Generators of gen
            matrix, #Matrix representing the image of the homomorphism f
            exp,    #Exponents of c^-1*g in each pcp
            stb,    #Elements corresponding to the kernel and the preimages
            solv,   #Conjugating element in each step
            null;   #Kernel of f
            

    # the first layer
    if ExponentsByPcp(pcps[1], g) <> ExponentsByPcp(pcps[1], h) then 
        return false; 
    fi;

    Info( InfoConjugacyElements, 1, StringFormatted("The algorithm has to process {} layers.", Length(pcps)-1) );

    C := G;
    k := One(G);

    for i in [2..Length(pcps)] do

        pcp := pcps[i];
        c   := g^k;

        N   := SubgroupByIgs( G, NumeratorOfPcp(pcp) );
        fac := Pcp(C, N);
        gens:= AsList(fac);
        exp := ExponentsByPcp( pcp, c^-1 * h );
        if Length(gens) = 0 then
            if exp = 0*exp then
                stb := rec( stab := gens, prei := c^0 );
            else
                Info( InfoConjugacyElements, 1, StringFormatted("Layer {} done.", i) );
                return false;
            fi;

        else

            # set up matrix
            matrix := List( gens, x -> ExponentsByPcp( pcp, Comm(x,c) ) );
            Append( matrix, ExponentRelationMatrix( pcp ) );

            # get solution
            solv := PcpSolutionIntMat( matrix, -exp );
            if IsBool( solv ) then 
                return false; 
            else
                solv := solv{[1..Length(gens)]};

                # get nullspace
                null := PcpNullspaceIntMat( matrix );
                null := null{[1..Length(null)]}{[1..Length(gens)]};

                # calculate elements
                solv := MappedVector( solv, gens );
                gens := List( null, x -> MappedVector( x, gens ) );
                gens := Filtered( gens, x -> x <> x^0 );
                stb  := rec( stab := gens, prei := solv );
            fi;
        fi;

        # extract results
        k   := k * stb.prei;
        stb := AddIgsToIgs( stb.stab, Igs(N) );
        C   := SubgroupByIgs( G, stb );
        Info( InfoConjugacyElements, 1, StringFormatted("Layer {} done.", i) );
    
    od;

    return k;

end;

####################################################################
## Global function to check if g and h are conjugate in G         ##
####################################################################

InstallGlobalFunction( "IsConjugateNilGroup", function(G,g,h)

    return IsConjugateNilGroupSeries(G,g,h,PcpsOfEfaSeries(G));

end );

####################################################################
## Helper functions of CanonicalConjugateNilGroups, solves the    ##
## the problem of finding m minimal with the well-defined order   ##
####################################################################

####################################################################
## Minimize the function a + x*coef                               ##
####################################################################

MinEq := function( a, coef)

    local   d,      #Gcd of coeficients
            m,      #Minimum of coeficients
            rep;    #Representation of the minimum

    d := Gcd(coef);
    m := a mod d;

    if m = a then 

        return rec( min := a, rep := coef*0);

    else

        rep := (m - a)/d;
        rep := rep * GcdRepresentation( coef );
        return rec( min := m, rep := rep);

    fi;
end;

####################################################################
## Minimize the number of relations used to speed up computations ##
####################################################################

MinimizeRelations := function(l, exp, o)

    local   min,    #Minimum number of relations
            i,      #Bucle variable
            d,      #Gcd of the minimum number of relations
            n,      #Gcd of d and the order
            z;      #Solution
            
    min := [];
    for i in [1..Length(l)] do 
        Add(min, l[i]);
        d := Gcd( min );
        n := Gcd( d , o);
        if exp mod n = 0 then
            z := GcdRepresentation( d/n, o/n );
            z := (exp/n * z[1]) mod (o/n);
            return ( z* GcdRepresentation( min ) mod o);
        fi;
    od;
end;

####################################################################
## Minimize the number of relations used to speed up computations ##
####################################################################

MinimalSolFFE := function(pcp, matrix, gens, h, c, o)

    local   gen,    #Generator of the pcp
            d,      #Depth of the pcp
            pos,    #Positions where the matrix is non zero
            a,      #List of commutators
            exp,    #Exponents
            b,      #Minimum of the equation
            rep,    #Minimum relations
            n,      #Integer variable
            i;      #Bucle variable
    
    gen := pcp[1]; 
    d   := Depth( gen ); 
    exp := Exponents( h^-1 * c )[d];

    #Order the generators to speed computations
    pos := PositionsProperty( matrix , x -> x <> 0*x ); 
    pos := Reversed(gens{pos});

    #Find the exponents of each ordered generator
    a   := List( pos, x -> Comm(c,x) );
    d   := List( a,   x -> Exponents( x )[d] );
    if ForAll( d, x -> x = d[1] ) then
        rep := d*0;
        rep[1] := 1;
    else
        rep := GcdRepresentation( d );
    fi;

    #Minimize the equation
    n   := d * rep;
    a   := Gcd( n, o ); 
    b   := exp mod a; 

    rep := MinimizeRelations( d, b - exp, o);
    pos := pos{[1..Length(rep)]};

    exp := pos[1]^0;
    for i in [1..Length(rep)] do
        rep[i] := rep[i] mod ( o/Gcd(d[i],o) );
        a := (-rep[i] mod o);
        if a < rep[i] then
            exp := exp * pos[i]^(-a);
        else
            exp := exp * pos[i]^( rep[i] );
        fi;
    od;
    
    return rec( solv := gen^( b ), exp := exp );

end;

####################################################################
## Helper function of CanonicalConjugateNilGroups, checks if      ##
## the an element is conjugated in a finite group                 ##
####################################################################

PcpSolutionFFEMat := function( matrix, exp, o)

    local   l,      #Flattened matrix
            i,      #Bucle variable
            n,      #Gcd of the flattened matrix and 
            pos,    #Gcd representation of the matrix
            solv;   #Solution

    #Check if the equation has solution
    l      := List( matrix, x -> x[1] );
    l      := Reversed(l);
    solv   := Gcd( l );
    pos    := GcdRepresentation( l );
    n      := Gcd( solv, o );
    if (exp mod n) <> 0 then return false; fi;

    #Now solve it , trying to use the minimum number of relations
    solv   := MinimizeRelations(l, exp, o);
    
    for i in [1..Length(solv)] do
        if solv[i] <> 0 then
            solv[i] := solv[i] mod (o/Gcd(l[i],o));
            pos := (-solv[i] mod o);
            if pos < solv[i] then
                solv[i] := - pos;
            fi;
        fi;
    od;
    
    return Reversed(solv);

end;

######################################################################
## Local function to calculate the canonical conjugate of elms in G ##
######################################################################

CanonicalConjugateNilGroupSeries := function(G, elms, pcps )

    local   C,      #Centralizer of kanos in G
            h,      #CanonicalConjugate
            k,      #Conjugate element
            i,j,elm,#Bucle variable
            pcp,    #Factor on each step Gi/G(i+1)
            o,      #Factor order
            c,      #g^k in each step
            N,      #Subgroup Gi
            fac,    #Factor group C/Gi in each step
            gens,   #Generators of gen
            matrix, #Matrix representing the image of the homomorphism f
            rels,   #Relations of pcp
            exp,    #Exponents of c^-1*g in each pcp
            stb,    #Elements corresponding to the kernel and the preimages
            solv,   #Conjugating element in each step
            m,      #Minimal element to have h*m conjugate
            null;   #Kernel of f
            

    # the first layer 
    C     := [];
    h     := [];
    k     := [];
    for elm in elms do
        Add( C, G);
        Add( h, G.1^( Exponents(elm)[1] ) );
        Add( k, One(G) );
    od;
    Info( InfoConjugacyElements, 1, StringFormatted("The algorithm has to process {} layers.", Length(pcps)-1) );

    for i in [2..Length(pcps)] do

        pcp  := pcps[i];
        o    := FactorOrder( pcp[1] );
        N    := SubgroupByIgs( G, NumeratorOfPcp(pcp) );

        for j in [1..Length(elms)] do
        
            fac    := Pcp(C[j], N);
            gens   := AsList(fac);
            c      := elms[j]^k[j];
            matrix := List( gens, x -> [ Exponents( Comm(x,c) )[i] ] );
            exp    := Exponents( h[j]^-1 * c )[i];
            
            if matrix = 0*matrix then 
                #This case is when f is the identity homomorphism.
                
                m    := pcp[1]^exp;
                h[j] := h[j] * m;
                Append(matrix, ExponentRelationMatrix( pcp ));

            elif o = 0 then
                # check if they are conjugated
                solv := PcpSolutionIntMat( matrix, [exp] );
                
                if IsBool( solv ) then 
                    #if not add the minimal element to be conjugated
                    m      := List( matrix, x -> x[1] );
                    m      := MinEq( exp , m ).min;
                    h[j]   := h[j] * pcp[1]^m;
                    
                    #Calculate the new exponent
                    exp    := exp - m;
                    solv   := PcpSolutionIntMat( matrix, [exp] );
                fi;

                #Calculate the conjugating element
                solv := MappedVector( solv, gens );
                k[j] := k[j] * solv;
            
            else
                solv := PcpSolutionFFEMat(matrix, exp, o);
                if IsBool(solv) then
                    m    := MinimalSolFFE(pcp, matrix, gens, h[j], c, o);
                    h[j] := h[j] * m.solv;
                    k[j] := k[j] * m.exp;
                else
                    solv := MappedVector( solv, Reversed( Reversed(gens){[1..Length(solv)]} ) );
                    k[j] := k[j]*solv;
                fi; 
                Append(matrix, ExponentRelationMatrix( pcp ));
            fi;
            # get the kernel
            null := PcpNullspaceIntMat( matrix );
            null := null{[1..Length(null)]}{[1..Length(gens)]};

            # calculate elements
            gens := List( null, x -> MappedVector( x, gens ) );
            gens := Filtered( gens, x -> x <> x^0 );   
            stb  := AddIgsToIgs( gens, NumeratorOfPcp(pcp) );
            C[j] := SubgroupByIgs( G, stb );
        od;
        Info( InfoConjugacyElements, 1, StringFormatted("Layer {} done.", i) );
    
    od;

    return rec(conj := k, kano := h, cent := C);

end;

#######################################################################
## Global function to calculate the canonical conjugate of elms in G ##
#######################################################################

InstallGlobalFunction( "CanonicalConjugateElements", function(G, elms)

    local   pcps;

    if not IsList(elms) then
        elms := [elms];
    fi;
    pcps := PcpsBySeries( PcpSeries(G) );
    return CanonicalConjugateNilGroupSeries(G, elms, pcps);
    # return CanonicalConjugateNilGroupSeries(G, elms, PcpsOfEfaSeries(G));

end );

######################################################################
## Local function to calculate solve the conjugacy problem in G     ##
## using canonical conjugate elements                               ##
######################################################################

IsCanonicalConjugateNilGroupSeries := function(G, elms, pcps )

    local   igs,    #Igs of G
            C,      #Centralizer of elms in G
            h,      #CanonicalConjugate
            k,      #Conjugate element
            i,j,elm,#Bucle variable
            pcp,    #Factor on each step Gi/G(i+1)
            c,      #g^k in each step
            N,      #Subgroup Gi
            o,      #Factor order
            fac,    #Factor group C/Gi in each step
            gens,   #Generators of gen
            matrix, #Matrix representing the image of the homomorphism f
            exp,    #Exponents of c^-1*g in each pcp
            stb,    #Elements corresponding to the kernel and the preimages
            solv,   #Conjugating element in each step
            m,      #Minimal element to have h*m conjugate
            exps,   #Exponent of the minimal solution
            ref,    #Reference value of m
            null;   #Kernel of f
            

    # the first layer
    C   := G;
    k   := [One(G)];
    ref := Exponents( elms[1])[1];
    h   := G.1^( ref );

    for i in [2..Length(elms)] do
        if Exponents( elms[i] )[1] <> ref then
            return false;
        fi;
        k[i] := One(G);
    od;
    Info( InfoConjugacyElements, 1, StringFormatted("The algorithm has to process {} layers.", Length(pcps)-1) );

    for i in [2..Length(pcps)] do

        pcp    := pcps[i];
        N      := SubgroupByIgs( G, NumeratorOfPcp(pcp) );
        o      := FactorOrder( pcp[1] );

        fac    := Pcp(C, N);
        gens   := AsList(fac);

        #For the fist element
        c      := elms[1]^k[1];
        matrix := List( gens, x -> [ Exponents( Comm(x,c) )[i] ] );
        exp := Exponents( h^-1 * c )[i];

        if matrix = 0*matrix then 
            #This case is when f is the identity homomorphism.
            h   := h * pcp[1]^exp;
            Append( matrix, ExponentRelationMatrix( pcp ) );

        elif o = 0 then
            # get solution if necessary
            solv := PcpSolutionIntMat( matrix, [exp] );

            if IsBool( solv ) then 

                m      := List( matrix, x -> x[1] );
                m      := MinEq( exp , m ).min;
                h      := h * pcp[1]^m;

                #Calculate the new exponent
                exp    := exp - m;
                solv   := PcpSolutionIntMat( matrix, [exp] );
                
            fi;

            # calculate elements
            solv := MappedVector( solv, gens );
            # extract results
            k[1] := k[1] * solv;

        else

            solv := PcpSolutionFFEMat(matrix, exp, o);

            if IsBool(solv) then
            
                m := MinimalSolFFE(pcp, matrix, gens, h, c, o);
                h := h * m.solv;
                k[1] := k[1] * m.exp;
            else
            
                solv := MappedVector( solv, Reversed( Reversed(gens){[1..Length(solv)]} ) );
                k[1] := k[1]*solv;
            fi; 
            
            Append(matrix, ExponentRelationMatrix( pcp ));
        fi;
        
        
        # Calculate the centralizer
        null := PcpNullspaceIntMat( matrix );
        null := null{[1..Length(null)]}{[1..Length(gens)]};

        stb  := List( null, x -> MappedVector( x, gens ) );
        stb  := Filtered( stb, x -> x <> x^0 );

        stb  := AddIgsToIgs( stb, NumeratorOfPcp(pcp) );
        C    := SubgroupByIgs( G, stb );

        #For the other elements
        for j in [2..Length(elms)] do

            c      := elms[j]^k[j];
            exp    := Exponents(  h^-1 * c )[i];
            matrix := List( gens, x -> [ Exponents( Comm(x,c) )[i] ] );

            if matrix = 0*matrix and exp <> 0 then 
                Info( InfoConjugacyElements, 1, StringFormatted("Layer {} done.", i) );
                return false;

            elif o = 0 then
                # get solution if necessary
                solv := PcpSolutionIntMat( matrix, [exp] );
                if IsBool(solv) then 
                    Info( InfoConjugacyElements, 1, StringFormatted("Layer {} done.", i) );
                    return false; 
                fi;
    
                # calculate elements
                solv := MappedVector( solv, gens );
                # extract results
                k[j] := k[j] * solv;

            else
                solv := PcpSolutionFFEMat( matrix, exp, o);
                if IsBool(solv) then 
                    Info( InfoConjugacyElements, 1, StringFormatted("Layer {} done.", i) );
                    return false;
                fi;

                gens := Reversed( Reversed(gens){[1..Length(solv)]} );
                solv := MappedVector( solv, gens );
                k[j] := k[j] * solv;
            fi;

        od;
        Info( InfoConjugacyElements, 1, StringFormatted("Layer {} done.", i) );
    od;

    return rec(kano := h, conj := k, cent := C );

end;

######################################################################
## Global function to calculate solve the conjugacy problem in G    ##
## using canonical conjugate elements                               ##
######################################################################

InstallGlobalFunction( "IsCanonicalConjugateElements", function( arg )

    local   G,      #Group
            elms,   #Elements
            i,      #Bucle variable
            pcps;   #Pcps

    G := arg[1];
    if IsList( arg[2] ) then
        elms := arg[2];
    else
        elms := [];
        for i in [2..Length(arg)] do
            Add(elms, arg[i]);
        od;
    fi;

    pcps := PcpsBySeries( PcpSeries(G) );
    return IsCanonicalConjugateNilGroupSeries(G, elms, pcps);
    
end );

######################################################################
## Global function to calculate solve the conjugacy problem in G    ##
## of a list of elements using canonical conjugates                 ##
######################################################################

InstallGlobalFunction( "CanonicalConjugateList", function(G, list)

    local   kan,
            con_class,
            positions,
            i,j,
            indexes,
            pos;

    kan       := CanonicalConjugateElements(G, list).kano;
    con_class := [];
    positions := [];
    i         := 1;
    indexes   := [1..Length(list)];
    
    while true do
        pos := Positions(kan, kan[i]);
        Add(positions, pos );
        Add(con_class, kan[i]);
        i := PositionProperty(indexes, x -> not x in pos);
        if i <> fail then
            i := indexes[i];
            for j in [1..Length(pos)] do
                Remove(indexes, Position(indexes, pos[j]));
            od; 
        else
            break;
        fi;
    od;

    return rec( con_class := con_class, positions := positions);

end );

######################################################################
## Global function to calculate solve the conjugacy problem in G    ##
## of a list of elements                                            ##
######################################################################

InstallGlobalFunction( "IsConjugateList", function(G, list)

    local   positions,
            indexes,
            con_class,
            index,
            p,
            conj,
            n;

    positions := [];
    indexes   := [1..Length(list)];
    con_class := [];
    while not IsEmpty(indexes) do

        index := First(indexes);
        Remove( indexes, 1 );
        Add   ( con_class, list[index] );
        p     := [ ];

        for n in indexes do
            conj := IsConjugateNilGroup(G, list[index], list[n]);
            if conj <> false then
                Add   ( p, n );
            fi;
        od;

        for n in p do
            Remove( indexes, Position(indexes, n) );
        od;
        Add( p, index, 1);
        Add( positions, p);
    od;

    return rec( con_class := con_class, positions := positions);

end );