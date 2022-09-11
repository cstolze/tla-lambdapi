/********************************************************************
 An encoding of TLA+ set theory in LambdaPi, building on the
 representation of (monomorphic) predicate logic.

 Author: Stephan Merz
 Copyright Inria 2022
 MIT License
********************************************************************/

require open tla.predicatelogic;

/*** Elementary operators of set theory ***/
// set membership
symbol ∈ : U → U → U;
notation ∈ infix 2;
// set of subsets (power set)
symbol subset : U → U;
// generalized union (union of all elements)
symbol union : U → U;
// restriction to the elements satisfying a predicate (usually called separation)
symbol subsetOf : U → (U → U) → U;
// replacement: images of elements of a given set under an operator
symbol setOfAll : U → (U → U) → U;
// unspecified infinite set
symbol infinity : U;

/*** Derived operators of set theory ***/
/** 
  The axioms of set theory, given below, use some of these
  derived operators. This is of course inessential, as each
  operator could have been replaced by its definition, but it
  makes the axioms easier to read.
**/
// empty set (NB: the choice of infinity as base set is irrelevant)
symbol ∅ : U;
constant symbol empty-def : Prf (∅ = subsetOf infinity (λ _, false));
// unordered pairs {x,y} = { if z = ∅ then x else y : z ∈ subset (subset ∅) }
symbol upair : U → U → U;
constant symbol upair-def x y : 
  Prf (upair x y = setOfAll (subset (subset ∅)) (λ z, ite (z = ∅) x y));
// binary set union
symbol ∪ : U → U → U;
notation ∪ infix 5;
constant symbol ∪-def s t : Prf (s ∪ t = union (upair s t));
// extension of a set by an element (s ∪ {x})
symbol addElt : U → U → U;
constant symbol addElt-def x s : Prf (addElt x s = (upair x x) ∪ s);
// bounded choice
symbol bchoose : U → (U → U) → U;
constant symbol bchoose-def s p :
  Prf (bchoose s p = `choose z, and (z ∈ s) (p z));
// bounded existential quantification
symbol bexists : U → (U → U) → U;
constant symbol bexists-def s p :
  Prf (bexists s p = `exists z, and (z ∈ s) (p z));
// bounded universal quantification
symbol bforall : U → (U → U) → U;
constant symbol bforall-def s p :
  Prf (bforall s p = `forall z, imp (z ∈ s) (p z));

/*** Axioms of ZFC set theory ***/
// membership is Boolean
constant symbol memBoolean x y : (Prf (x ∈ y) → Prf false) → Prf ((x ∈ y) = false);
// two sets are equal if they contamem the same elements
constant symbol extensionality x y : (Π z, Prf (iff (z ∈ x) (z ∈ y))) → Prf (x = y);
// z is a subset of x iff every element of z is an element of x
constant symbol subset-def x z : 
  Prf (iff (z ∈ (subset x)) (`forall y, imp (y ∈ z) (y ∈ x)));
// union x contains those elements that are contained in some set in x
constant symbol union-def x z : 
  Prf (iff (z ∈ (union x)) (`exists y, and (y ∈ x) (z ∈ y)));
// { z \in x : p(z) }
constant symbol subsetOf-def x p z : 
  Prf (iff (z ∈ (subsetOf x p)) (and (z ∈ x) (p z)));
// { f(y) : y \in x }
constant symbol setOfAll-def x f z : 
  Prf (iff (z ∈ setOfAll x f) (`exists y, and (y ∈ x) (z = f y)));
// axioms about the infinity set
constant symbol infinity_1 : Prf (∅ ∈ infinity);
constant symbol infinity_2 x : Prf (x ∈ infinity) → Prf ((addElt x x) ∈ infinity);
// foundation axiom: a set is either empty, or it contains some element that contains no element of x
constant symbol foundation x y : 
  Prf (y ∈ x) → Prf (bexists x (λ y, bforall y (λ z, (not ((z ∈ x))))));

/*** More derived operators. ***/
// negated set membership (notation only)
symbol ∉ x y ≔ not (x ∈ y);
notation ∉ infix 2;
// subset relation
symbol ⊆ : U → U → U;
notation ⊆ infix 2;
constant symbol ⊆-def x y : Prf ((x ⊆ y) = bforall x (λ z, z ∈ y));
// binary intersection
symbol ∩ : U → U → U;
notation ∩ infix 5;
constant symbol ∩-def x y : Prf ((x ∩ y) = subsetOf x (λ z, z ∈ y));
// set difference
symbol ∖ : U → U → U;
notation ∖ infix 5;
constant symbol ∖-def x y : Prf ((x ∖ y) = subsetOf x (λ z, z ∉ y));
// Generalized intersection is not officially part of TLA+ but can be defined easily.
symbol intersection : U → U;
constant symbol intersection-def x : Prf (intersection x = subsetOf (union x) (λ y, bforall x (λ z, y ∈ z)));

/** Theorems about bounded quantification. **/
opaque symbol ballI s p : (Π z, Prf (z ∈ s) → Prf (p z)) → Prf (bforall s p) ≔
begin
    assume s p pimp;
    apply subst (bforall s p) (`forall z, imp (z ∈ s) (p z)) (λ z, z) (bforall-def s p);
    apply allI (λ z, imp (z ∈ s) (p z));
    assume z;
    apply impI (z ∈ s) (p z);
    refine pimp z
end;

opaque symbol bspec s p z : Prf (bforall s p) → Prf (z ∈ s) → Prf (p z) ≔
begin
    assume s p z pball pin;
    have pall: Prf (`forall z, imp (z ∈ s) (p z))
    {  apply ssubst (bforall s p) (`forall z, imp (z ∈ s) (p z)) (λ z, z) (bforall-def s p) pball };
    have pimp: Prf (imp (z ∈ s) (p z))
    {  apply allE (λ z, imp (z ∈ s) (p z)) z pall };
    apply mp _ _ pimp pin
end;

opaque symbol ballE s p z q : Prf (bforall s p) → Prf (z ∈ s) → (Prf (p z) → Prf q) → Prf q ≔
begin
    assume s p z q pball pin ppzpq;
    apply ppzpq;
    apply bspec s p z pball pin
end;

opaque symbol bexI s p z : Prf (z ∈ s) → Prf (p z) → Prf (bexists s p) ≔
begin
    assume s p z pin ppz;
    apply subst (bexists s p) (`exists z, and (z ∈ s) (p z)) (λ z, z) (bexists-def s p);
    apply exI (λ z, and (z ∈ s) (p z)) z;
    apply andI _ _ pin ppz
end;

opaque symbol bexE s p q : Prf (bexists s p) → (Π z, Prf (z ∈ s) → Prf (p z) → Prf q) → Prf q ≔
begin
    assume s p q pbex pimp;
    have pex : Prf (`exists z, and (z ∈ s) (p z))
    {  apply ssubst (bexists s p) (`exists z, and (z ∈ s) (p z)) (λ z, z) (bexists-def s p) pbex  };
    apply exE (λ z, and (z ∈ s) (p z)) q pex;
    assume z pand;
    apply pimp z (andD1 (z ∈ s) (p z) pand) (andD2 (z ∈ s) (p z) pand);
end;

// we only provide the "generalized" version of this theorem
opaque symbol bChooseI s p q : Prf (bexists s p)
                            → (Π z, Prf (z ∈ s) → Prf (p z) → Prf (q z))
                            → Prf (q (bchoose s p)) ≔
begin
    assume s p q pbex pimp;
    apply subst (bchoose s p) (`choose z, and (z ∈ s) (p z)) (λ z, q z) (bchoose-def s p);
    have pex: Prf (`exists z, and (z ∈ s) (p z))
    {  apply ssubst (bexists s p) (`exists z, and (z ∈ s) (p z)) (λ z, z) (bexists-def s p) pbex  };
    apply chooseI2Ex (λ z, and (z ∈ s) (p z)) q pex;
    assume z pand;
    apply pimp z (andD1 (z ∈ s) (p z) pand) (andD2 (z ∈ s) (p z) pand)
end;

/** Theorems about the subset relation. **/
opaque symbol ⊆I s t : (Π z, Prf (z ∈ s) → Prf (z ∈ t)) → Prf (s ⊆ t) ≔
begin
    assume s t pimp;
    apply subst (s ⊆ t) (bforall s (λ z, z ∈ t)) (λ z, z) (⊆-def s t);
    apply ballI s (λ z, z ∈ t);
    refine pimp
end;

opaque symbol ⊆D s t z : Prf (s ⊆ t) → Prf (z ∈ s) → Prf (z ∈ t) ≔
begin
    assume s t z psub pins;
    have pbf: Prf (bforall s (λ z, z ∈ t))
    {  apply ssubst (s ⊆ t) (bforall s (λ z, z ∈ t)) (λ z, z) (⊆-def s t) psub  };
    apply bspec s (λ z, z ∈ t) z pbf pins
end;

opaque symbol ⊆-refl s : Prf (s ⊆ s) ≔
begin
    assume s;
    apply ⊆I s s;
    assume z pin;
    apply pin
end;

rule $s ⊆ $s ↪ true;

opaque symbol ⊆-trans s t u : Prf (s ⊆ t) → Prf (t ⊆ u) → Prf (s ⊆ u) ≔
begin
    assume s t u pst ptu;
    apply ⊆I s u;
    assume z pins;
    apply ⊆D t u z ptu;
    apply ⊆D s t z pst pins
end;

opaque symbol ⊆-antisym s t : Prf (s ⊆ t) → Prf (t ⊆ s) → Prf (s = t) ≔
begin
    assume s t pst pts;
    apply extensionality s t;
    assume z;
    apply iffI (z ∈ s) (z ∈ t)
    { assume pins; apply ⊆D s t z pst pins }
    { assume pint; apply ⊆D t s z pts pint }
end;

/** Theorems about subsetOf {z in S : p(z)} **/
opaque symbol subsetOfI s p z : Prf (z ∈ s) → Prf (p z) → Prf (z ∈ subsetOf s p) ≔
begin
    assume s p z pzs ppz;
    apply iffE (z ∈ subsetOf s p) (and (z ∈ s) (p z)) _ (subsetOf-def s p z);
    assume _ pimp;
    apply mp (and (z ∈ s) (p z)) (z ∈ subsetOf s p) pimp;
    apply andI _ _ pzs ppz;
end;

opaque symbol subsetOfE s p z q : Prf (z ∈ subsetOf s p) → (Prf (z ∈ s) → Prf (p z) → Prf q) → Prf q ≔
begin
    assume s p z q pso pq;
    apply iffE (z ∈ subsetOf s p) (and (z ∈ s) (p z)) _ (subsetOf-def s p z);
    assume pimp _;
    have both: Prf (and (z ∈ s) (p z))
    { apply mp _ _ pimp pso };
    apply pq (andD1 (z ∈ s) (p z) both) (andD2 (z ∈ s) (p z) both)
end;

/** Theorems about setOfAll {f(z) : z in S} **/
opaque symbol setOfAllI s f z : Prf (z ∈ s) → Prf (f z ∈ setOfAll s f) ≔
begin
    assume s f z pin;
    apply iffE (f z ∈ setOfAll s f) (`exists y, and (y ∈ s) (f z = f y)) _ (setOfAll-def s f (f z));
    assume _ pimp;
    apply mp (exists (λ y, and (y ∈ s) (f z = f y))) (f z ∈ setOfAll s f) pimp;
    apply exI (λ y, and (y ∈ s) (f z = f y)) z;
    apply andI (z ∈ s) (f z = f z) pin (refl (f z))
end;

opaque symbol setOfAll_eqI s f z y : Prf (z = f y) → Prf (y ∈ s) → Prf (z ∈ setOfAll s f) ≔
begin
    assume s f z y peq pin;
    apply iffE (z ∈ setOfAll s f) (`exists y, and (y ∈ s) (z = f y)) _ (setOfAll-def s f z);
    assume _ pimp;
    apply mp (exists (λ y, and (y ∈ s) (z = f y))) (z ∈ setOfAll s f) pimp;
    apply exI (λ y, and (y ∈ s) (z = f y)) y;
    apply andI _ _ pin peq
end;

opaque symbol setOfAllE s f z q : Prf (z ∈ setOfAll s f) → (Π y, Prf (y ∈ s) → Prf (z = f y) → Prf q) → Prf q ≔
begin
    assume s f z q pso pqy;
    apply iffE (z ∈ setOfAll s f) (exists (λ y, and (y ∈ s) (z = f y))) _ (setOfAll-def s f z);
    assume pimp _;
    have pex: Prf (exists (λ y, and (y ∈ s) (z = f y)))
    {  apply mp (z ∈ setOfAll s f) _ pimp pso };
    apply exE (λ y, and (y ∈ s) (z = f y)) q pex;
    assume y pand;
    apply pqy y (andD1 (y ∈ s) (z = f y) pand) (andD2 (y ∈ s) (z = f y) pand)
end;

/** Theorems about generalized set union **/
opaque symbol unionI z s t : Prf (z ∈ t) → Prf (t ∈ s) → Prf (z ∈ union s) ≔
begin
    assume z s t pzin ptin;
    apply iffE (z ∈ union s) (exists (λ y, and (y ∈ s) (z ∈ y))) _ (union-def s z);
    assume _ pimp;
    apply mp (exists (λ y, and (y ∈ s) (z ∈ y))) (z ∈ union s) pimp;
    apply exI (λ y, and (y ∈ s) (z ∈ y)) t;
    apply andI _ _ ptin pzin
end;

opaque symbol unionE z s q : Prf (z ∈ union s) → (Π y, Prf (z ∈ y) → Prf (y ∈ s) → Prf q) → Prf q ≔
begin
    assume z s q pinu pqy;
    apply iffE (z ∈ union s) (exists (λ y, and (y ∈ s) (z ∈ y))) _ (union-def s z);
    assume pimp _;
    have pex: Prf (exists (λ y, and (y ∈ s) (z ∈ y)))
    {  apply mp (z ∈ union s) _ pimp pinu  };
    apply exE (λ y, and (y ∈ s) (z ∈ y)) q pex;
    assume y pand;
    apply pqy y (andD2 (y ∈ s) (z ∈ y) pand) (andD1 (y ∈ s) (z ∈ y) pand)
end;

/** Theorems about generalized intersection.
    Observe that these are not exactly dual to the theorems about generalized union
    because the intersection of the empty set is defined as the empty set. */
opaque symbol intersectionI z s : (Π y, Prf (y ∈ s) → Prf (z ∈ y)) → Prf (`exists y, y ∈ s) → Prf (z ∈ intersection s) ≔
begin
    assume z s yszy exs;
    apply subst (intersection s) (subsetOf (union s) (λ y, bforall s (λ x, y ∈ x))) (λ u, z ∈ u) (intersection-def s);
    apply subsetOfI (union s) (λ y, bforall s (λ x, y ∈ x)) z
    {  apply exE (λ y, y ∈ s) _ exs;
       assume y yins;
       refine unionI z s y _ yins;
       apply yszy y yins;
    }
    {  apply ballI s (λ x, z ∈ x) yszy;  }
end;

opaque symbol intersectionE z s q : Prf (z ∈ intersection s) → (Prf (z ∈ union s) → (Π y, (Prf (y ∈ s) → Prf (z ∈ y))) → Prf q) → Prf q ≔
begin
    assume z s q zint prvq;
    have zint': Prf (z ∈ subsetOf (union s) (λ y, bforall s (λ x, y ∈ x)))
    {  apply ssubst (intersection s) (subsetOf (union s) (λ y, bforall s (λ x, y ∈ x))) (λ u, z ∈ u) (intersection-def s) zint  };
    apply subsetOfE (union s) (λ y, bforall s (λ x, y ∈ x)) z q zint';
    assume zuns alls;
    apply prvq zuns;
    assume y yins;
    apply bspec s (λ x, z ∈ x) y alls yins
end;

/** Theorems about the empty set **/
opaque symbol emptyE z q : Prf (z ∈ ∅) → Prf q ≔
begin
    assume z q pin;
    have pin': Prf (z ∈ subsetOf infinity (λ _, false))
    {  apply ssubst ∅ (subsetOf infinity (λ _, false)) (λ u, z ∈ u) empty-def pin   };
    apply subsetOfE infinity (λ _, false) z q pin';
    assume _ pfls;
    apply absurd _ pfls
end;

opaque symbol inEmpty z : Prf ((z ∈ ∅) = false) ≔
begin
    assume z;
    apply memBoolean z ∅;
    assume ine;
    apply emptyE z _ ine
end;

opaque symbol isEmpty s : (Π z, Prf (z ∉ s)) → Prf (s = ∅) ≔
begin
    assume s pniz;
    apply extensionality s ∅;
    assume z;
    apply iffI (z ∈ s) (z ∈ ∅)
    {  assume pzs; apply notE (z ∈ s) (z ∈ ∅) (pniz z) pzs  }
    {  assume pemp; apply emptyE z _ pemp  }
end;

opaque symbol subsetOfEmpty p : Prf (subsetOf ∅ p = ∅) ≔
begin
    assume p;
    apply extensionality (subsetOf ∅ p) ∅;
    assume z;
    apply iffI (z ∈ subsetOf ∅ p) (z ∈ ∅)
    {  assume ins; 
       apply subsetOfE ∅ p z (z ∈ ∅) ins;
       assume ine _;
       apply ine
    }
    {  assume ine; 
       apply emptyE z _ ine 
    }
end;

opaque symbol setOfAllEmpty f : Prf (setOfAll ∅ f = ∅) ≔
begin
    assume f;
    apply extensionality (setOfAll ∅ f) ∅;
    assume z;
    apply iffI (z ∈ setOfAll ∅ f) (z ∈ ∅)
    {  assume ins;
       apply setOfAllE ∅ f z (z ∈ ∅) ins;
       assume y ine _;
       apply emptyE y _ ine
    }
    {  assume ine;
       apply emptyE z _ ine
    }
end;

opaque symbol unionEmpty : Prf (union ∅ = ∅) ≔
begin
    apply extensionality (union ∅) ∅;
    assume z;
    apply iffI (z ∈ union ∅) (z ∈ ∅)
    {  assume inu;
       apply unionE z ∅ _ inu;
       assume y _ ine;
       apply emptyE y _ ine
    }
    {  assume ine;
       apply emptyE z _ ine
    }
end;

opaque symbol intersectionEmpty : Prf (intersection ∅ = ∅) ≔
begin
    apply extensionality (intersection ∅) ∅;
    assume z;
    apply iffI (z ∈ intersection ∅) (z ∈ ∅)
    {  assume lhs;
       apply intersectionE z ∅ _ lhs;
       assume zinunemp _;
       apply unionE z ∅ _ zinunemp;
       assume y _ yinemp;
       apply emptyE y _ yinemp
    }
    {  assume zinemp; apply emptyE z _ zinemp  }
end;

opaque symbol emptySubset s : Prf (∅ ⊆ s) ≔
begin
    assume s;
    apply ⊆I ∅ s;
    assume z pine;
    apply emptyE z _ pine
end;

opaque symbol bforallEmpty p : Prf (bforall ∅ p) ≔
begin
    assume p;
    apply ballI ∅ p;
    assume z pine;
    apply emptyE z _ pine
end;

opaque symbol bexistsEmpty p : Prf (not (bexists ∅ p)) ≔
begin
    assume p;
    apply notI (bexists ∅ p);
    assume bex;
    apply bexE ∅ p false bex;
    assume z pine _;
    apply emptyE z _ pine
end;

// The preceding lemmas provide useful rewrite rules
rule _ ∈ ∅ ↪ false;
rule subsetOf ∅ _ ↪ ∅;
rule setOfAll ∅ _ ↪ ∅;
rule union ∅ ↪ ∅;
rule intersection ∅ ↪ ∅;
rule ∅ ⊆ _ ↪ true;
rule bforall ∅ _ ↪ true;
rule bexists ∅ _ ↪ false;

/** Theorems about subset (the powerset constructor). **/
opaque symbol subsetI s t : Prf (s ⊆ t) → Prf (s ∈ subset t) ≔
begin
    assume s t psub;
    have pall: Prf (`forall z, imp (z ∈ s) (z ∈ t))
    {  apply allI (λ z, imp (z ∈ s) (z ∈ t));
       assume z;
       apply impI (z ∈ s) (z ∈ t);
       assume pins;
       apply ⊆D s t z psub pins
    };
    apply iffE (s ∈ subset t) (`forall y, imp (y ∈ s) (y ∈ t)) _ (subset-def t s);
    assume _ pimp;
    apply mp (`forall y, imp (y ∈ s) (y ∈ t)) (s ∈ subset t) pimp pall
end;

opaque symbol subsetE s t : Prf (s ∈ subset t) → Prf (s ⊆ t) ≔
begin
    assume s t psub;
    apply iffE (s ∈ subset t) (`forall y, imp (y ∈ s) (y ∈ t)) _ (subset-def t s);
    assume pimp _;
    have pall: Prf (`forall z, imp (z ∈ s) (z ∈ t))
    {  apply mp (s ∈ subset t) (`forall y, imp (y ∈ s) (y ∈ t)) pimp psub  };
    apply ⊆I s t;
    assume z pins;
    apply mp (z ∈ s) (z ∈ t) (allE (λ z, imp (z ∈ s) (z ∈ t)) z pall) pins
end;

opaque symbol emptyInSubset s : Prf (∅ ∈ subset s) ≔
begin
    assume s;
    apply subsetI ∅ s;
    simplify;
    apply trivial;
end;

opaque symbol selfInSubset s : Prf (s ∈ subset s) ≔
begin
    assume s;
    apply subsetI s s;
    simplify;
    apply trivial;
end;

rule ∅ ∈ subset _ ↪ true;
rule $s ∈ subset $s ↪ true;

/** Theorems about unordered pairs **/
opaque symbol upairE x y z q : Prf (z ∈ upair x y) → (Prf (z = x) → Prf q) → (Prf (z = y) → Prf q) → Prf q ≔
begin
    assume x y z q pip pxq pyq;
    have pso: Prf (z ∈ setOfAll (subset (subset ∅)) (λ z, ite (z = ∅) x y))
    {  apply ssubst (upair x y) (setOfAll (subset (subset ∅)) (λ z, ite (z = ∅) x y)) (λ u, z ∈ u) (upair-def x y) pip  };
    apply setOfAllE (subset (subset ∅)) (λ u, ite (u = ∅) x y) z q pso;
    assume u _ pite;
    apply caseSplit (u = ∅) q
    {  assume uemp;
       apply pxq (iteT (u = ∅) x y (λ v, z = v) pite uemp)
    }
    {  assume unemp;
       apply pyq (iteE (u = ∅) x y (λ v, z = v) pite unemp)
    }
end;

opaque symbol upairI1 x y : Prf (x ∈ upair x y) ≔
begin
    assume x y;
    apply subst (upair x y) (setOfAll (subset (subset ∅)) (λ z, ite (z = ∅) x y)) (λ u, x ∈ u) (upair-def x y);
    apply setOfAll_eqI (subset (subset ∅)) (λ z, ite (z = ∅) x y) x ∅
    {  simplify; apply trivial   }
    {  simplify; apply trivial   }
end;

opaque symbol upairI2 x y : Prf (y ∈ upair x y) ≔
begin
    assume x y;
    apply subst (upair x y) (setOfAll (subset (subset ∅)) (λ z, ite (z = ∅) x y)) (λ u, y ∈ u) (upair-def x y);
    apply setOfAll_eqI (subset (subset ∅)) (λ z, ite (z = ∅) x y) y (subset ∅)
    {  apply iteI (subset ∅ = ∅) x y (λ u, y = u)
       {  assume subempty;
          have abs: Prf (∅ ∈ ∅)
          {  apply ssubst (subset ∅) ∅ (λ u, ∅ ∈ u) subempty;
             simplify; apply trivial 
          };
          apply emptyE ∅ _ abs
       }
       {  assume _; apply refl y }
    }
    {  simplify; apply trivial  }
end;

opaque symbol upairSame x z : Prf (iff (z ∈ upair x x) (z = x)) ≔
begin
    assume x z;
    apply iffI (z ∈ upair x x) (z = x)
    {  assume zpr;
       apply upairE x x z _ zpr 
       {  assume zx; apply zx  }
       {  assume zx; apply zx  }
    }
    {  assume zx;
       apply subst z x (λ u, u ∈ upair x x) zx;
       apply upairI1 x x
    }
end;

rule $x ∈ upair $x _ ↪ true;
rule $y ∈ upair _ $y ↪ true;
rule $z ∈ upair $x $x ↪ $z = $x;

opaque symbol upairCommute x y : Prf (upair x y = upair y x) ≔
begin
    assume x y;
    apply extensionality (upair x y) (upair y x);
    assume z;
    apply iffI (z ∈ upair x y) (z ∈ upair y x)
    {  assume zpr;
       apply upairE x y z _ zpr
       {  assume zx; apply subst z x (λ u, u ∈ upair y x) zx (upairI2 y x)  }
       {  assume zy; apply subst z y (λ u, u ∈ upair y x) zy (upairI1 y x)  }
    }
    {  assume zpr;
       apply upairE y x z _ zpr
       {  assume zy; apply subst z y (λ u, u ∈ upair x y) zy (upairI2 x y)  }
       {  assume zx; apply subst z x (λ u, u ∈ upair x y) zx (upairI1 x y)  }
    }
end;
// Can we now declare `upair' to be a commutative symbol?

/** Theorems about binary union. **/
opaque symbol ∪I1 s t z : Prf (z ∈ s) → Prf (z ∈ s ∪ t) ≔
begin
    assume s t z pins;
    apply subst (s ∪ t) (union (upair s t)) (λ u, z ∈ u) (∪-def s t);
    apply unionI z (upair s t) s pins;
    simplify;
    apply trivial
end;

opaque symbol ∪I2 s t z : Prf (z ∈ t) → Prf (z ∈ s ∪ t) ≔
begin
    assume s t z pint;
    apply subst (s ∪ t) (union (upair s t)) (λ u, z ∈ u) (∪-def s t);
    apply unionI z (upair s t) t pint;
    simplify;
    apply trivial
end;

// classical introduction rule
opaque symbol ∪CI s t z : (Prf (z ∉ t) → Prf (z ∈ s)) → Prf (z ∈ s ∪ t) ≔
begin
    assume s t z pts;
    apply caseSplit (z ∈ t)
    {  assume zt; apply ∪I2 s t z zt  }
    {  assume znt; apply ∪I1 s t z (pts znt)  }
end;

opaque symbol ∪E s t z q : Prf (z ∈ s ∪ t) → (Prf (z ∈ s) → Prf q) → (Prf (z ∈ t) → Prf q) → Prf q ≔
begin
    assume s t z q pcup psq ptq;
    have ppr: Prf (z ∈ union (upair s t))
    {  apply ssubst (s ∪ t) (union (upair s t)) (λ u, z ∈ u) (∪-def s t) pcup  };
    apply unionE z (upair s t) q ppr;
    assume y pzy pypr;
    apply upairE s t y q pypr
    {  assume ys; apply psq; apply ssubst y s (λ u, z ∈ u) ys pzy }
    {  assume yt; apply ptq; apply ssubst y t (λ u, z ∈ u) yt pzy }
end;

opaque symbol ∪IsEmpty s t : Prf (iff (s ∪ t = ∅) (and (s = ∅) (t = ∅))) ≔
begin
    assume s t;
    apply iffI (s ∪ t = ∅) (and (s = ∅) (t = ∅))
    {  assume lhs;
       apply andI (s = ∅) (t = ∅)
       {  apply extensionality s ∅;
          assume z;
          apply iffI (z ∈ s) (z ∈ ∅)
          {  assume zins;
             apply ssubst (s ∪ t) ∅ (λ y, z ∈ y) lhs;
             apply ∪I1 s t z zins;
          }
          {  assume zine; apply emptyE z _ zine;  }
       }
       {  apply extensionality t ∅;
          assume z;
          apply iffI (z ∈ t) (z ∈ ∅)
          {  assume zint;
             apply ssubst (s ∪ t) ∅ (λ y, z ∈ y) lhs;
             apply ∪I2 s t z zint;
          }
          {  assume zine; apply emptyE z _ zine;  }
       }
    }
    {  assume rhs;
       apply extensionality (s ∪ t) ∅;
       assume z;
       apply iffI (z ∈ s ∪ t) (z ∈ ∅)
       {  assume zinu;
          apply ∪E s t z _ zinu
          {  assume zins; 
             apply andE (s = ∅) (t = ∅) _ rhs;
             assume semp _;
             apply ssubst s ∅ (λ y, z ∈ y) semp zins;
          }
          {  assume zint;
             apply andE (s = ∅) (t = ∅) _ rhs;
             assume _ temp;
             apply ssubst t ∅ (λ y, z ∈ y) temp zint;
          }
       }
       {  assume zine; apply emptyE z _ zine;  }
    }
end;

rule $s ∪ $t = ∅ ↪ and ($s = ∅) ($t = ∅);

// Commutativity of binary set union. The following is a purely equational proof,
// alternatively we could have used extensionality and the rules above.
opaque symbol ∪Commute s t : Prf (s ∪ t = t ∪ s) ≔
begin
    assume s t;
    apply subst (s ∪ t) (union (upair s t)) (λ u, u = (t ∪ s)) (∪-def s t);
    apply subst (t ∪ s) (union (upair t s)) (λ u, union (upair s t) = u) (∪-def t s);
    apply subst (upair s t) (upair t s) (λ u, union u = union (upair t s)) (upairCommute s t);
    apply refl (union (upair t s))
end;

opaque symbol ∪Assoc s t u : Prf ((s ∪ t) ∪ u = s ∪ (t ∪ u)) ≔
begin
    assume s t u;
    apply extensionality ((s ∪ t) ∪ u) (s ∪ (t ∪ u));
    assume z;
    apply iffI ( z ∈ (s ∪ t) ∪ u) (z ∈ s ∪ (t ∪ u))
    {  assume inl;
       apply ∪E (s ∪ t) u z _ inl
       {  assume inst; 
          apply ∪E s t z _ inst
          {  assume ins; apply ∪I1 s (t ∪ u) z ins  }
          {  assume int; apply ∪I2 s (t ∪ u) z; apply ∪I1 t u z int  }
       }
       {  assume inu; apply ∪I2 s (t ∪ u) z; apply ∪I2 t u z inu  }
    }
    {  assume inr;
       apply ∪E s (t ∪ u) z _ inr
       {  assume ins; apply ∪I1 (s ∪ t) u z; apply ∪I1 s t z ins  }
       {  assume intu; 
          apply ∪E t u z _ intu
          {  assume int; apply ∪I1 (s ∪ t) u z; apply ∪I2 s t z int  }
          {  assume inu; apply ∪I2 (s ∪ t) u z inu  }
       }
    }
end;

opaque symbol ∪EmptyR s : Prf (s ∪ ∅ = s) ≔
begin
    assume s;
    apply extensionality (s ∪ ∅) s;
    assume z;
    apply iffI (z ∈ s ∪ ∅) (z ∈ s)
    {  assume lhs;
       apply ∪E s ∅ z _ lhs
       {  assume ins; apply ins  }
       {  assume inemp; apply emptyE z _ inemp  }
    }
    {  assume rhs;
       apply ∪I1 s ∅ z rhs
    }
end;

opaque symbol ∪EmptyL s : Prf (s = s ∪ ∅) ≔
begin
    assume s;
    have r: Prf (s ∪ ∅ = s) {  apply ∪EmptyR s  };
    apply subst (s ∪ ∅) s (λ u, s = u) r;
    apply refl s
end;

opaque symbol ∪Idempotent s : Prf (s ∪ s = s) ≔
begin
    assume s;
    apply extensionality (s ∪ s) s;
    assume z;
    apply iffI (z ∈ s ∪ s) (z ∈ s)
    {  assume lhs; 
       apply ∪E s s z (z ∈ s) lhs
       {  assume ins; apply ins  }
       {  assume ins; apply ins  }
    }
    {  assume ins; apply ∪I1 s s z ins  }
end;

rule $s ∪ ∅ ↪ $s;
rule ∅ ∪ $s ↪ $s;
rule $s ∪ $s ↪ $s;

/** Adding an element to a set. */
opaque symbol addEltI1 x s : Prf (x ∈ addElt x s) ≔
begin
    assume x s;
    apply subst (addElt x s) ((upair x x) ∪ s) (λ u, x ∈ u) (addElt-def x s);
    apply ∪I1 (upair x x) s x;
    simplify;
    apply trivial
end;

opaque symbol addEltI2 x s z : Prf (z ∈ s) → Prf (z ∈ addElt x s) ≔
begin
    assume x s z zins;
    apply subst (addElt x s) ((upair x x) ∪ s) (λ u, z ∈ u) (addElt-def x s);
    apply ∪I2 (upair x x) s z zins
end;

opaque symbol addEltE x s z q : Prf (z ∈ addElt x s) → (Prf (z = x) → Prf q) → (Prf (z ∈ s) → Prf q) → Prf q ≔
begin
    assume x s z q zinxs pxq psq;
    have inadd: Prf (z ∈ (upair x x) ∪ s)
    {  apply ssubst (addElt x s) ((upair x x) ∪ s) (λ u, z ∈ u) (addElt-def x s) zinxs  };
    apply ∪E (upair x x) s z q inadd
    {  simplify; assume eqz; apply pxq eqz  }
    {  assume ins; apply psq ins  }
end;

opaque symbol bforallAddElt x s p : Prf (iff (bforall (addElt x s) p ) (and (p x) (bforall s p))) ≔
begin
    assume x s p;
    apply iffI (bforall (addElt x s) p) (and (p x) (bforall s p))
    {  assume lhs;
       apply andI (p x) (bforall s p)
       {  apply bspec (addElt x s) p x lhs; apply addEltI1 x s  }
       {  apply ballI s p; 
          assume z zins;
          apply bspec (addElt x s) p z lhs;
          apply addEltI2 x s z zins;
       }
    }
    {  assume rhs;
       apply ballI (addElt x s) p;
       assume z zinaE;
       apply addEltE x s z _ zinaE
       {  assume zx;
          apply subst z x (λ y, p y) zx;
          apply andD1 (p x) (bforall s p) rhs;
       }
       {  assume zins;
          apply andE (p x) (bforall s p) _ rhs;
          assume _ allsp;
          apply bspec s p z allsp zins;
       }
    }
end;

rule bforall (addElt $x $s) $p ↪ and ($p $x) (bforall $s $p);

/** Theorems about binary intersection. **/
opaque symbol ∩I s t z : Prf (z ∈ s) → Prf (z ∈ t) → Prf (z ∈ (s ∩ t)) ≔
begin
    assume s t z pins pint;
    apply subst (s ∩ t) (subsetOf s (λ z, z ∈ t)) (λ u, z ∈ u) (∩-def s t);
    apply subsetOfI s (λ z, z ∈ t) z pins pint
end;

opaque symbol ∩D1 s t z : Prf (z ∈ s ∩ t) → Prf (z ∈ s) ≔
begin
    assume s t z inst;
    have insub: Prf (z ∈ subsetOf s (λ y, y ∈ t))
    {  apply ssubst (s ∩ t) (subsetOf s (λ z, z ∈ t)) (λ u, z ∈ u) (∩-def s t) inst  };
    apply subsetOfE s (λ y, y ∈ t) z _ insub;
    assume ins _;
    apply ins
end;

opaque symbol ∩D2 s t z : Prf (z ∈ s ∩ t) → Prf (z ∈ t) ≔
begin
    assume s t z inst;
    have insub: Prf (z ∈ subsetOf s (λ y, y ∈ t))
    {  apply ssubst (s ∩ t) (subsetOf s (λ z, z ∈ t)) (λ u, z ∈ u) (∩-def s t) inst  };
    apply subsetOfE s (λ y, y ∈ t) z _ insub;
    assume _ int;
    apply int
end;

opaque symbol ∩E s t z q : Prf (z ∈ s ∩ t) → (Prf (z ∈ s) → Prf (z ∈ t) → Prf q) → Prf q ≔
begin
    assume s t z q inst stq;
    have insub: Prf (z ∈ subsetOf s (λ y, y ∈ t))
    {  apply ssubst (s ∩ t) (subsetOf s (λ z, z ∈ t)) (λ u, z ∈ u) (∩-def s t) inst  };
    apply subsetOfE s (λ y, y ∈ t) z _ insub;
    assume ins int;
    apply stq ins int
end;

opaque symbol ∩Commute s t : Prf (s ∩ t = t ∩ s) ≔
begin
    assume s t;
    apply extensionality (s ∩ t) (t ∩ s);
    assume z;
    apply iffI (z ∈ s ∩ t) (z ∈ t ∩ s)
    {  assume lhs;
       apply ∩E s t z _ lhs;
       assume ins int;
       apply ∩I t s z int ins
    }
    {  assume rhs;
       apply ∩E t s z _ rhs;
       assume int ins;
       apply ∩I s t z ins int
    }
end;

opaque symbol ∩EmptyR s : Prf (s ∩ ∅ = ∅) ≔
begin
    assume s;
    apply extensionality (s ∩ ∅) ∅;
    assume z;
    apply iffI (z ∈ s ∩ ∅) (z ∈ ∅)
    {  assume lhs;
       apply ∩E s ∅ z _ lhs;
       assume _ inemp;
       apply inemp
    }
    {  assume inemp;
       apply emptyE z _ inemp
    }
end;

opaque symbol ∩EmptyL s : Prf (∅ ∩ s = ∅) ≔
begin
    assume s;
    have r: Prf (s ∩ ∅ = ∅) {  apply ∩EmptyR s  };
    apply ssubst (s ∩ ∅) (∅ ∩ s) (λ u, u = ∅) (∩Commute s ∅) r
end;

opaque symbol ∩Idempotent s : Prf (s ∩ s = s) ≔
begin
    assume s;
    apply extensionality (s ∩ s) s;
    assume z;
    apply iffI (z ∈ s ∩ s) (z ∈ s)
    {  assume lhs; apply ∩D1 s s z lhs  }
    {  assume rhs; apply ∩I s s z rhs rhs }
end;

rule $s ∩ ∅ ↪ ∅;
rule ∅ ∩ $s ↪ ∅;
rule $s ∩ $s ↪ $s;

/** Theorems about set difference. **/
opaque symbol ∖I s t z : Prf (z ∈ s) → Prf (z ∉ t) → Prf (z ∈ s ∖ t) ≔
begin
    assume s t z ins nint;
    apply subst (s ∖ t) (subsetOf s (λ y, y ∉ t)) (λ u, z ∈ u) (∖-def s t);
    apply subsetOfI s (λ y, y ∉ t) z ins nint
end;

opaque symbol ∖E s t z q : Prf (z ∈ s ∖ t) → (Prf (z ∈ s) → Prf (z ∉ t) → Prf q) → Prf q ≔
begin
    assume s t z q pind stq;
    have insub: Prf (z ∈ subsetOf s (λ y, y ∉ t))
    {  apply ssubst (s ∖ t) (subsetOf s (λ y, y ∉ t)) (λ u, z ∈ u) (∖-def s t) pind  };
    apply subsetOfE s (λ y, y ∉ t) z _ insub;
    assume ins nint;
    apply stq ins nint
end;

opaque symbol ∖EmptyR s : Prf (s ∖ ∅ = s) ≔
begin
    assume s;
    apply extensionality (s ∖ ∅) s;
    assume z;
    apply iffI (z ∈ s ∖ ∅) (z ∈ s)
    {  assume lhs; 
       apply ∖E s ∅ z _ lhs;
       assume ins _; apply ins
    }
    {  assume ins; 
       apply ∖I s ∅ z ins;
       simplify; apply trivial
    }
end;

opaque symbol ∖EmptyL s : Prf (∅ ∖ s = ∅) ≔
begin
    assume s;
    apply extensionality (∅ ∖ s) ∅;
    assume z;
    apply iffI (z ∈ ∅ ∖ s) (z ∈ ∅)
    {  assume lhs;
       apply ∖E ∅ s z _ lhs;
       assume inemp _; apply inemp
    }
    {  assume inemp; apply emptyE z _ inemp }
end;

opaque symbol ∖Self s : Prf (s ∖ s = ∅) ≔
begin
    assume s;
    apply extensionality (s ∖ s) ∅;
    assume z;
    apply iffI (z ∈ s ∖ s) (z ∈ ∅)
    {  assume lhs;
       apply ∖E s s z _ lhs;
       assume ins notins;
       apply notE (z ∈ s) _ notins ins
    }
    {  assume inemp; apply emptyE z _ inemp  }
end;

rule $s ∖ ∅ ↪ $s;
rule ∅ ∖ $s ↪ ∅;
rule $s ∖ $s ↪ ∅;

/** More facts about generalized set union. **/
opaque symbol unionAddElt s S : Prf (union (addElt s S) = s ∪ (union S)) ≔
begin
    assume s S;
    apply extensionality (union (addElt s S)) (s ∪ (union S));
    assume z;
    apply iffI (z ∈ union (addElt s S)) (z ∈ s ∪ (union S))
    {  assume lhs;
       apply unionE z (addElt s S) _ lhs;
       assume y ziny yinaE;
       apply addEltE s S y _ yinaE
       {  assume ys;
          apply ∪I1 s (union S) z;
          apply ssubst y s (λ u, z ∈ u)ys  ziny
       }
       {  assume yinS;
          apply ∪I2 s (union S) z;
          apply unionI z S y ziny yinS
       }
    }
    {  assume rhs;
       apply ∪E s (union S) z _ rhs
       {  assume zins;
          apply unionI z (addElt s S) s zins;
          apply addEltI1 s S
       }
       {  assume zinu;
          apply unionE z S _ zinu;
          assume y ziny yinS;
          apply unionI z (addElt s S) y ziny;
          apply addEltI2 s S y yinS
       }
    }
end;

opaque symbol unionIsEmpty s : Prf (iff (union s = ∅) (bforall s (λ x, x = ∅))) ≔
begin
    assume s;
    apply iffI (union s = ∅) (bforall s (λ x, x = ∅))
    {  assume unemp;
       apply ballI s (λ x, x = ∅);
       assume z zins;
       apply isEmpty z;
       assume y;
       apply notI (y ∈ z);
       assume yinz;
       have yinu: Prf (y ∈ union s) {  apply unionI y s z yinz zins  };
       have yinemp: Prf (y ∈ ∅) {  apply ssubst (union s) ∅ (λ x, y ∈ x) unemp yinu  };
       apply emptyE y _ yinemp
    }
    {  assume allEmp;
       apply isEmpty (union s);
       assume z;
       apply notI (z ∈ union s);
       assume zinu;
       apply unionE z s _ zinu;
       assume y ziny yins;
       have yemp: Prf (y = ∅) {  apply bspec s (λ x, x = ∅) y allEmp yins  };
       have zinemp: Prf (z ∈ ∅) {  apply ssubst y ∅ (λ x, z ∈ x) yemp ziny  };
       apply emptyE z _ zinemp
    }
end;

rule union (addElt $s $S) ↪ $s ∪ (union $S);
rule (union $s) = ∅ ↪ bforall $s (λ x, x = ∅);

/** Consequences of the foundation axiom. **/
// The following generalizes "x ∈ y ⇒ y ∉ x": choose q ≔ y ∉ x.
opaque symbol inAsym x y q : Prf (x ∈ y) → (Prf (not q) → Prf (y ∈ x)) → Prf q ≔
begin
    assume x y q xy qyx;
    apply ccontr q;
    assume nq;
    have yx: Prf (y ∈ x) {  apply qyx nq  };
    have fnd: Prf (bexists (upair x y) (λ z, bforall z (λ u, u ∉ upair x y)))
    {  apply foundation (upair x y) x; apply upairI1 x y  };
    apply bexE (upair x y) (λ z, bforall z (λ u, u ∉ upair x y)) _ fnd;
    assume z zxy ball;
    apply upairE x y z _ zxy
    {  assume zx;
       have ballx: Prf (bforall x (λ u, u ∉ upair x y))
       {  apply ssubst z x (λ v, bforall v (λ u, u ∉ upair x y)) zx ball  };
       have abs: Prf (y ∉ upair x y)
       {  apply bspec x (λ u, u ∉ upair x y) y ballx yx  };
       apply notE (y ∈ upair x y) _ abs (upairI2 x y)
    }
    {  assume zy;
       have bally: Prf (bforall y (λ u, u ∉ upair x y))
       {  apply ssubst z y (λ v, bforall v (λ u, u ∉ upair x y)) zy ball  };
       have abs: Prf (x ∉ upair x y)
       {  apply bspec y (λ u, u ∉ upair x y) x bally xy  };
       apply notE (x ∈ upair x y) _ abs (upairI1 x y)
    }
end;

// simple corollary: no set contains itself
opaque symbol inIrrefl x q: Prf (x ∈ x) → Prf q ≔
begin
    assume x q xinx;
    apply inAsym x x q xinx;
    assume _;
    apply xinx
end;

// therefore, no set contains everything
opaque symbol noSetContainsEverything s : Prf (`exists x, x ∉ s) ≔
begin
    assume s;
    have sns: Prf (s ∉ s)
    {  apply notI (s ∈ s);
       assume sins;
       apply inIrrefl s false sins
    };
    apply exI (λ x, x ∉ s) s sns
end;

// The following lemma justifies a standard TLA+ idiom for defining null values.
opaque symbol chooseNotIn s : Prf ((`choose x, x ∉ s) ∉ s) ≔
begin
    assume s;
    apply chooseI2Ex (λ x, x ∉ s) (λ x, x ∉ s) (noSetContainsEverything s);
    assume x nins;
    apply nins
end;


