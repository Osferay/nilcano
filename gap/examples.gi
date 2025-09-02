ExamplesOfSomePcpVirtuallyNilpotentGroups := function(n)

    local   coll;

    #[6,0,0,0] the semidirect product of C_6 and the Discrete Heisenberg group H_3
    if n = 1 then
        coll := FromTheLeftCollector( 4 );
        SetRelativeOrder( coll, 1, 6 );
        SetConjugate( coll, 2, 1, [ 3, 1 ] );
        SetConjugate( coll, 2, -1, [ 2, 1, 3, -1 ] );
        SetConjugate( coll, 3, 1, [ 2, -1, 3, 1 ] );
        SetConjugate( coll, 3, -1, [ 2, 1 ] );
        SetConjugate( coll, 3, 2, [ 3, 1, 4, 1 ] );
        SetConjugate( coll, 3, -2, [ 3, 1, 4, -1 ] );

    #[2,3,0,0,0] the semidirect product of S_3 and the Discrete Heisenberg group H_3
    elif n = 2 then
        coll := FromTheLeftCollector( 5 );
        SetRelativeOrder( coll, 1, 2 );
        SetRelativeOrder( coll, 2, 3 );
        SetConjugate( coll, 2, 1, [ 2, 2 ] );
        SetConjugate( coll, 2, -1, [ 2, 2 ] );
        SetConjugate( coll, 3, 1, [ 3, 1, 4, -1 ] );
        SetConjugate( coll, 3, -1, [ 3, 1, 4, -1 ] );
        SetConjugate( coll, 3, 2, [ 4, -1 ] );
        SetConjugate( coll, 3, -2, [ 3, -1, 4, 1, 5, -1 ] );
        SetConjugate( coll, 4, 1, [ 4, -1 ] );
        SetConjugate( coll, 4, -1, [ 4, -1 ] );
        SetConjugate( coll, 4, 2, [ 3, 1, 4, -1 ] );
        SetConjugate( coll, 4, -2, [ 3, -1 ] );
        SetConjugate( coll, 4, 3, [ 4, 1, 5, 1 ] );
        SetConjugate( coll, 4, -3, [ 4, 1, 5, -1 ] );
        SetConjugate( coll, 5, 1, [ 5, -1 ] );
        SetConjugate( coll, 5, -1, [ 5, -1 ] );

    #[10,0,0,0,0,0] the semidirect product of C_10 and the Discrete Heisenberg group H_5
    elif n = 3 then
        coll := FromTheLeftCollector( 6 );
        SetRelativeOrder( coll, 1, 10 );
        SetConjugate( coll, 2, 1, [ 3, 1 ] );
        SetConjugate( coll, 2, -1, [ 2, 1, 3, -1, 4, 1, 5, -1 ] );
        SetConjugate( coll, 3, 1, [ 4, 1 ] );
        SetConjugate( coll, 3, -1, [ 2, 1 ] );
        SetConjugate( coll, 3, 2, [ 3, 1, 6, 1 ] );
        SetConjugate( coll, 3, -2, [ 3, 1, 6, -1 ] );
        SetConjugate( coll, 4, 1, [ 5, 1 ] );
        SetConjugate( coll, 4, -1, [ 3, 1 ] );
        SetConjugate( coll, 4, 3, [ 4, 1, 6, 1 ] );
        SetConjugate( coll, 4, -3, [ 4, 1, 6, -1 ] );
        SetConjugate( coll, 5, 1, [ 2, -1, 3, 1, 4, -1, 5, 1 ] );
        SetConjugate( coll, 5, -1, [ 4, 1 ] );
        SetConjugate( coll, 5, 4, [ 5, 1, 6, 1 ] );
        SetConjugate( coll, 5, -4, [ 5, 1, 6, -1 ] );
    
    fi;

    
    #[2,3,4,4,0,0,0,0,0] the semidirect product of S_3xC_4]C_4 and the Discrete Heisenberg group H_5
    elif n = 4 then
        coll := FromTheLeftCollector( 7 );;
        SetRelativeOrder( coll, 1, 2 );;
        SetRelativeOrder( coll, 2, 6 );;
        SetConjugate( coll, 2, 1, [ 2, 2 ] );;
        SetConjugate( coll, 3, 1, [ 3, 1, 4, -1 ] );;
        SetConjugate( coll, 4, 1, [ 4, -1 ] );;
        SetConjugate( coll, 7, 1, [ 7, -1 ] );;
        SetConjugate( coll, 3, 2, [ 4, -1 ] );;
        SetConjugate( coll, 4, 2, [ 3, 1, 4, -1 ] );;
        SetCommutator( coll, 5, 3, [ 7, 1 ]);;
        SetCommutator( coll, 6, 4, [ 7, 1 ]);;
    
    fi;

    UpdatePolycyclicCollector( coll );
    return PcpGroupByCollectorNC( coll ); 

end;