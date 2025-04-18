#! @Chapter Preface
#! @ChapterLabel preface
#! @ChapterTitle Preface

#! In this package we compute the canonical conjugacy representatives of elements and subgroups of
#! nilpotent groups given by a nilpotent sequence.
#! This package also include functions to compute the intersection of subgroups of nilpotent
#! group and to compute the product of subgroups of nilpotent groups.
	
#! @Section Nilpotent sequences
#! Let $G$ be a finitely generated nilpotent group. Then $G$ has a series $G = G_1 > G_2 > \dots > G_n > G_{n+1} = {1}$
#! so that each Gi is normal in G and each quotient $G_i/G_{i+1}$ is cyclic and central in $G/G_{i+1}$. 
#! We call such a series a nilpotent series of G. Then $(g_1,\dots, g_n)$ is called a nilpotent sequence
#! of $G$ and $(o_1,\dots, o_n)$ are its relative orders. Note that the nilpotent sequence determines its
#! nilpotent series as $G_i = \langle g_i,\dots, g_n \rangle$ holds for $1 \leq i \leq n$.
#!
#! Each element $g \in G$ can be written uniquely as $g = g_1^{e_1} \dots g_n^{e_n}$ with $e_i \in \mathbb{Z}$
#! and $e_i \in \{0,\dots, o_{i −1}\}$ if $i \in I$. The factorisation $ g_1^{e_1} \dots g_n^{e_n}$ for
#! $g \in G$ is called the normal form of $g$. The associated integer vector $(e_1,\dots, e_n)$ is the
#! exponent vector of $g$. We write $e(g) = (e_1, \dots , e_n)$. If $e_1 = \dots = e_{i−1} = 0$  and 
#! $e_i \neq 0$, then we write $dep(g) = i$ and call this the depth of $g$. The leading exponent of an
#! element $g$ is $e_d$ where $d = dep(g)$. The identity element satisfies $dep(1) = n + 1$ and does not
#! have leading exponent.


### General.gi
DeclareGlobalFunction( "ReducePcpElement" );
DeclareGlobalFunction( "RandomElementRangeGenerators" );    
DeclareGlobalFunction( "RandomSubgroup" );
DeclareGlobalFunction( "ConjugacyOrder" );
DeclareGlobalFunction( "Sifting" );

#! @Chapter Conjugacy
#! @ChapterLabel conj
#! @ChapterTitle Conjugacy

#! @Section Canonical conjugate representatives for elements

#! Suppose that the finitely generated group $G$ is given by a nilpotent sequence $(g_1,\dots,g_n)$. 
#! For $g \in G $ and $U \leq G$, we denote the conjugacy class of $g$ under $U$ by $g^U = {g^h | h \in U}$
#! and the centralizer of $g$ in $U$ by $C_U (g) = \{h \in U | g^h = g\}$.
#!
#! Let $\ll$ be the well-order $0 \ll 1 \ll 2 \ll \dots \ll −1 \ll −2 \dots $ of $\mathbb{Z}$. We order the exponent 
#! vectors extending the well-order lexicographically; that is, $(e_1,\dots, e_n) \ll (f_1, \dots, f_n)$
#! if $ e_1 = f_1, \dots , e_{i−1} = f_{i−1}$ and $e_i \ll f_i$ for some $i \in {1,\dots,n} $.
#! We order the elements of G via their exponent vectors; that is, $g \ll h$ if $e(g) \leq e(h)$.

#! One of the main program of this package is to compute the minimum element in $ g^U $ with respect to 
#! $\ll$ this element is known as the canonical conjugacy representative of $ g$, this element is 
#! denoted as $Cano_U(g)$. This program also computes the centralizer $ C_U(g)$. This package is supplementary to the
#! article of Eick and Fernández Ayala <Cite Key="cano" />.

### conjugacy.gi
#! @Description
#! Computes the centralizer of a given set of elements $elms$ in $G$.
#! @Arguments G, elms
DeclareGlobalFunction( "CentralizerNilGroup" );
#! @Description
#! Checks if two given elements $g$ and $h$ in $G$ are conjugate. If so it returns the conjugating element.
#! @Arguments G, g, h
DeclareGlobalFunction( "IsConjugateNilGroup" );
#! @Description
#! Computes the canonical conjugate representative of a given elements $elms$ in $G$. Returns a record containing the
#! canonical conjugates, the conjugating elements to obtain the canonical conjugate and the centralizers of the given elements.
#! @Arguments G, elms
DeclareGlobalFunction( "CanonicalConjugateElements" );
#! @Description
#! Checks if a set of elements $elms$ in $G$ are conjugate using the canonical representative aproach. 
#! If so it returns a record containing the canonical conjugate representative, the conjugating elements and the centralizer.
#! @Arguments G, elms
DeclareGlobalFunction( "IsCanonicalConjugateElements" );
#! @Description
#! Info class for the functions of canonical conjugates for elements.
DeclareInfoClass( "InfoConjugacyElements" );


#! @Section Canonical conjugate representatives for subgroups

#! Suppose that the finitely generated group $G$ is given by a nilpotent sequence $(g_1,\dots,g_n)$. 
#! Given $U, V \leq G$ we write $U^V = \{U^g | g ∈ V \}$ for the conjugacy class of $U$ under $V$ 
#! and $N_V(U) = \{g \in V | U^g = U\}$ for the corresponding normalizer.

#! Let $U \leq G$ be given by its basis $(u_1,\dots, u_n)$. Let $N \leq N_G(U)$ and $g \in N$.
#! We define $Cano_N^U(g)$ as the unique reduced preimage of $Cano_{N/U}(gU)$ under the natural 
#! homomorphism $N \rightarrow N/U$. 
	  
#! Now we consider two subgroups $W$ and $V$ of $G$, and write $W_i = W \cap G_i $ for $1 \leq i \leq n$.
#! We define $Cano_V (W )$ inductively: suppose that $U_{i+1} = Cano_V (W_i+1)$ is given by a basis 
#! $u_{i+1},\dots, u_n$ together with a conjugating element $U_i+1 = W^v_{i+1}$ and its normalizer 
#! $N = N_V (U_{i+1})$. Suppose that $W_i \neq W_{i+1}$ and $W_i = ⟨w_i, W_{i+1}⟩ $. Let 
#! $w_i^\prime$ be the normalized power of the conjugate $w^v_i$. Set $u_i = Cano^{U_{i+1}}_N(w^\prime_i)$,
#! then $(u_i,\dots, u_n)$ is a basis for a subgroup $U_i$ of $G_i$. We write $Cano_V (W )$ for the
#! subgroup $U_1$ eventually determined by an iterated process.

#! One of the main program of this package is to compute $Cano_V (W )$. This program also computes the normalizer
#! of $ N_V(W) $.

#! @Description
#! Computes the normalizer of a given subgroup $U$ of $G$.
#! @Arguments G, U
DeclareGlobalFunction( "NormalizerNilGroup" );
#! @Description
#! Checks if two given subgroups $U$ and $V$ of $G$ are conjugate. If so it returns the conjugating element.
#! @Arguments G, U, V
DeclareGlobalFunction( "IsConjugateSubgroups" );
#! @Description
#! Computes the canonical conjugate representative of a given subgroup $U$ of $G$. Returns a record containing the
#! canonical conjugate subgroup, the conjugating element and the normalizer of the given subgroup.
#! @Arguments G, U
DeclareGlobalFunction( "CanonicalConjugateSubgroup");
#! @Description
#! Checks if two subgroup $U,V$ of $G$ are conjugate using the canonical representative aproach. If so it
#! returns a record containing the canonical conjugate subgroup, the conjugating elements and the normalizer of the given subgroups.
#! @Arguments G, U, V
DeclareGlobalFunction( "IsCanonicalConjugateSubgroups" );
#! @Description
#! Info class for the functions of canonical conjugates for subgroups.
DeclareInfoClass( "InfoConjugacySubgroups" );

#! @Section Canonical conjugate representatives for lists

#! @Description
#! Given a list of elements of a nilpotent group $G$ returns a list of canonical representative conjugates of the list and the position of the elements that
#! belong to the given canonical conjugacy class.
#! @Arguments G, list
DeclareGlobalFunction( "CanonicalConjugateList" );
#! @Description
#! Given a list of elements of a nilpotent group $G$ returns a list of representative conjugates of the list and the position of the elements that
#! belong to the given conjugacy class.
#! @Arguments G, list
DeclareGlobalFunction( "IsConjugateList" );

### Inter.gi
#! @Section Intersection of subgroups and product pairs of subgroups
#! This algorithms are based on Eddie's work <Cite Key="Eddie" />.

DeclareGlobalFunction( "IntersectionSeriesTerm" );
DeclareGlobalFunction( "InducedIntersectionSeries" );
DeclareGlobalFunction( "PcpsOfInducedIntersectionSeries" );


#! @Description
#! Given two subgroups $U,V$ of a nilpotent group $G$ computes the intersection of both subgroups.
#! @Arguments G, U, V
DeclareGlobalFunction( "IntersectionSubgroupsNilGroups" );

### prod.gi

#! @Description
#! Given two subgroups $U,V$ of a nilpotent group $G$ computes the subgroup product pair of both subgroups.
#! @Arguments G, U, V
DeclareGlobalFunction( "SubgroupProductPair" );#! @Description
#! Given two subgroups $U,V$ of a nilpotent group $G$ and an element $g$ in $G$ computes the decompostion of $g$
#! under the product pair of both subgroups.
#! @Arguments G, U, V, g
DeclareGlobalFunction( "ProductDecomposition" );