gap> ftl := FromTheLeftCollector(5);;
gap> SetConjugate( ftl, 2, 1, [2, 1, 3, 11] );;
gap> SetConjugate( ftl, 3, 1, [3, 1, 4, 8]  );;
gap> SetConjugate( ftl, 3, 2, [3, 1, 5, 15] );;
gap> SetConjugate( ftl, 4, 1, [4, 1, 5, 16] );;
gap> G := PcpGroupByCollector( ftl );;
gap> g := RandomElementRangeGenerators(G, 1);;
gap> h := g^Random(G);;
gap> IsBool(IsConjugateNilGroup(G, g, h));
false
gap> IsBool(IsCanonicalConjugateElements(G, [g,h]));
false
gap> U := Subgroup( G, [Random(G), Random(G)]);;
gap> V := U^Random(G);;
gap> IsBool(IsConjugateSubgroups(G,U,V));
false
gap> IsBool(IsCanonicalConjugateSubgroups(G, U, V));
false
gap> l := RandomListElements(G, 3, "no_id");;
gap> list := ShallowCopy(l);;
gap> for i in [4..20] do
> g := Random(l);
> Add(list, Random(l)^Random(G));
> od;
gap> IsBool(IsConjugateList(G, list));
false
gap> IsBool(CanonicalConjugateList(G, list));
false