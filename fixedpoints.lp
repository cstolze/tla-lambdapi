/********************************************************************
 The Knaster-Tarski fixed-point theorems in TLA+.

 Author: Stephan Merz
 Copyright Inria 2022
 MIT License
*******************************************************************/

require open tla.predicatelogic;
require open tla.settheory;

/** Monotonic operators on set D. */
symbol monotonic D f ≔ 
  and (f D ⊆ D)
      (bforall (subset D)
         (λ S, bforall (subset D)
            (λ T, imp (S ⊆ T) (f S ⊆ f T))));

opaque symbol monotonicDomain D f : Prf (monotonic D f) → Prf (f D ⊆ D) ≔
begin
    simplify monotonic;
    assume D f mono;
    apply andD1 (f D ⊆ D) (bforall (subset D) (λ S, bforall (subset D) (λ T, imp (S ⊆ T) (f S ⊆ f T)))) mono;
end;

opaque symbol monotonicSubset D f S T : Prf (monotonic D f) → Prf (S ⊆ T) → Prf (T ⊆ D) → Prf (f S ⊆ f T) ≔
begin
    simplify monotonic;
    assume D f S T mono ST TD;
    have TsD: Prf (T ∈ subset D) {  apply subsetI T D TD };
    have SsD: Prf (S ∈ subset D)
    {  apply subsetI S D; apply ⊆-trans S T D ST TD  };
    refine mp (S ⊆ T) (f S ⊆ f T) _ ST;
    refine bspec (subset D) (λ T, imp (S ⊆ T) (f S ⊆ f T)) T _ TsD;
    refine bspec (subset D) (λ S, bforall (subset D) (λ T, imp (S ⊆ T) (f S ⊆ f T))) S _ SsD;
    apply andD2 (f D ⊆ D) (bforall (subset D) (λ S, bforall (subset D) (λ T, imp (S ⊆ T) (f S ⊆ f T)))) mono;
end;

opaque symbol ∪-monotonic D f S T : Prf (monotonic D f) → Prf (S ⊆ D) → Prf (T ⊆ D) → Prf (f S ∪ f T ⊆ f (S ∪ T)) ≔
begin
    assume D f S T mono SD TD;
    apply ⊆I (f S ∪ f T) (f (S ∪ T));
    assume z lhs;
    have STD: Prf (S ∪ T ⊆ D)
    {  apply ⊆I (S ∪ T) D;
       assume y yinst;
       apply ∪E S T y _ yinst
       {  assume yins; apply ⊆D S D y SD yins;  }
       {  assume yint; apply ⊆D T D y TD yint;  }
    };
    apply ∪E (f S) (f T) z _ lhs
    {  assume zinfS;
       refine ⊆D (f S) (f (S ∪ T)) z _ zinfS;
       refine monotonicSubset D f S (S ∪ T) mono _ STD;
       apply ⊆I S (S ∪ T);
       assume y yins;
       apply ∪I1 S T y yins;
    }
    {  assume zinfT;
       refine ⊆D (f T) (f (S ∪ T)) z _ zinfT;
       refine monotonicSubset D f T (S ∪ T) mono _ STD;
       apply ⊆I T (S ∪ T);
       assume y yint;
       apply ∪I2 S T y yint;
    }
end;

opaque symbol ∩-monotonic D f S T : Prf (monotonic D f) → Prf (S ⊆ D) → Prf (T ⊆ D) → Prf (f (S ∩ T) ⊆ f S ∩ f T) ≔
begin
    assume D f S T mono SD TD;
    have STS: Prf (f (S ∩ T) ⊆ f S)
    {  refine monotonicSubset D f (S ∩ T) S mono _ SD;
       apply ⊆I (S ∩ T) S;
       assume z zinst;
       apply ∩D1 S T z zinst;
    };
    have STT: Prf (f (S ∩ T) ⊆ f T)
    {  refine monotonicSubset D f (S ∩ T) T mono _ TD;
       apply ⊆I (S ∩ T) T;
       assume z zinst;
       apply ∩D2 S T z zinst;
    };
    apply ⊆I (f (S ∩ T)) (f S ∩ f T);
    assume z lhs;
    apply ∩I (f S) (f T) z
    {  apply ⊆D (f (S ∩ T)) (f S) z STS lhs; }
    {  apply ⊆D (f (S ∩ T)) (f T) z STT lhs; }
end;

/** Least fixed point: we will usually assume that f is monotonic. */
symbol lfp D f ≔ intersection (subsetOf (subset D) (λ S, f S ⊆ S));

// The least fixed point is contained in each pre-fixed point ...
opaque symbol lfpLB D f S : Prf (f S ⊆ S) → Prf (S ⊆ D) → Prf (lfp D f ⊆ S) ≔
begin
    assume D f S prefp SD;
    apply ⊆I (lfp D f) S;
    simplify lfp;
    assume z lhs;
    apply intersectionE z (subsetOf (subset D) (λ S, f S ⊆ S)) _ lhs;
    assume _ allSD;
    apply allSD S;
    refine subsetOfI (subset D) (λ S, f S ⊆ S) S _ prefp;
    apply subsetI S D SD;
end;

// ... and it is the largest such set.
opaque symbol lfpGLB D f S : Prf (f D ⊆ D) → (Π T, Prf (T ⊆ D) → Prf (f T ⊆ T) → Prf (S ⊆ T)) → Prf (S ⊆ lfp D f) ≔
begin
    assume D f S fD Slb;
    apply ⊆I S (lfp D f);
    assume z zinS;
    simplify lfp;
    apply intersectionI z (subsetOf (subset D) (λ T, f T ⊆ T))
    {  assume y yprefp;
       apply subsetOfE (subset D) (λ T, f T ⊆ T) y _ yprefp;
       assume yD fy;
       refine ⊆D S y z _ zinS;
       refine Slb y _ fy;
       apply subsetE y D yD;
    }
    {  apply exI (λ y, y ∈ subsetOf (subset D) (λ T, f T ⊆ T)) D;
       refine subsetOfI (subset D) (λ T, f T ⊆ T) D _ fD;
       apply subsetI D D;
       simplify; apply trivial;
    }
end;

opaque symbol lfpSubsetDomain D f : Prf (lfp D f ⊆ D) ≔
begin
    assume D f;
    apply ⊆I (lfp D f) D;
    simplify lfp;
    assume z zinlfp;
    apply intersectionE z (subsetOf (subset D) (λ S, f S ⊆ S)) _ zinlfp;
    assume zinu _;
    apply unionE z (subsetOf (subset D) (λ S, f S ⊆ S)) _ zinu;
    assume T zinT Tprefp;
    apply subsetOfE (subset D) (λ S, f S ⊆ S) T _ Tprefp;
    assume TD _;
    refine ⊆D T D z _ zinT;
    apply subsetE T D TD;
end;

// The lfp operator is monotonic.
opaque symbol lfpMono D f g : Prf (g D ⊆ D) → (Π S, Prf (S ⊆ D) → Prf (f S ⊆ g S)) → Prf (lfp D f ⊆ lfp D g) ≔
begin
    assume D f g gD fg;
    apply lfpGLB D g (lfp D f) gD;
    assume T TD gT;
    refine lfpLB D f T _ TD;
    refine ⊆-trans (f T) (g T) T _ gT;
    apply fg T TD;
end;

// If f is monotonic then lfp is a pre-fixed point ...
opaque symbol lfpPreFP D f : Prf (monotonic D f) → Prf (f (lfp D f) ⊆ lfp D f) ≔
begin
    assume D f mono;
    apply lfpGLB D f (f (lfp D f)) (monotonicDomain D f mono);
    assume T TD fT;
    refine ⊆-trans (f (lfp D f)) (f T) T _ fT;
    refine monotonicSubset D f (lfp D f) T mono _ TD;
    apply lfpLB D f T fT TD;
end;

// ... as well as a post-fixed point.
opaque symbol lfpPostFP D f : Prf (monotonic D f) → Prf (lfp D f ⊆ f (lfp D f)) ≔
begin
    assume D f mono;
    apply lfpLB D f (f (lfp D f))
    {  apply monotonicSubset D f (f (lfp D f)) (lfp D f) mono (lfpPreFP D f mono) (lfpSubsetDomain D f);  }
    {  apply ⊆-trans (f (lfp D f)) (lfp D f) D (lfpPreFP D f mono) (lfpSubsetDomain D f);  }
end;

// Therefore, it is a fixed point.
opaque symbol lfpFixedPoint D f : Prf (monotonic D f) → Prf (f (lfp D f) = lfp D f) ≔
begin
    assume D f mono;
    apply ⊆-antisym (f (lfp D f)) (lfp D f) (lfpPreFP D f mono) (lfpPostFP D f mono);
end;

// And in fact, smaller than any other fixed point.
opaque symbol lfpLeastFixedPoint D f S : Prf (S ⊆ D) → Prf (f S = S) → Prf (lfp D f ⊆ S) ≔
begin
    assume D f S SD fS;
    refine lfpLB D f S _ SD;
    apply subst (f S) S (λ T, T ⊆ S) fS (⊆-refl S);
end;

/** Dually, greatest fixed points as the union of post-fixed points. */
symbol gfp D f ≔ union (subsetOf (subset D) (λ S, S ⊆ f S));

// The greatest fixed point contains each post-fixed point ...
opaque symbol gfpUB D f S : Prf (S ⊆ f S) → Prf (S ⊆ D) → Prf (S ⊆ gfp D f) ≔
begin
    assume D f S postfp SD;
    apply ⊆I S (gfp D f);
    assume z zinS;
    simplify gfp;
    apply unionI z (subsetOf (subset D) (λ S, S ⊆ f S)) S zinS;
    refine subsetOfI (subset D) (λ S, S ⊆ f S) S _ postfp;
    apply subsetI S D SD;
end;

// ... and it is the smallest such set.
opaque symbol gfpLUB D f S : Prf (f D ⊆ D) → (Π T, Prf (T ⊆ D) → Prf (T ⊆ f T) → Prf (T ⊆ S)) → Prf (gfp D f ⊆ S) ≔
begin
    assume D f S fD Sub;
    apply ⊆I (gfp D f) S;
    simplify gfp;
    assume z zingfp;
    apply unionE z (subsetOf (subset D) (λ T, T ⊆ f T)) _ zingfp;
    assume T zinT Tinsub;
    refine ⊆D T S z _ zinT;
    apply subsetOfE (subset D) (λ T, T ⊆ f T) T _ Tinsub;
    assume TD fT;
    refine Sub T _ fT;
    apply subsetE T D TD;
end;

opaque symbol gfpSubsetDomain D f : Prf (gfp D f ⊆ D) ≔
begin
    assume D f;
    apply ⊆I (gfp D f) D;
    simplify gfp;
    assume z zingfp;
    apply unionE z (subsetOf (subset D) (λ T, T ⊆ f T)) _ zingfp;
    assume T zinT Tinsub;
    apply subsetOfE (subset D) (λ T, T ⊆ f T) T _ Tinsub;
    assume TD _;
    refine ⊆D T D z _ zinT;
    apply subsetE T D TD;
end;

// The gfp operator is monotonic.
opaque symbol gfpMono D f g : Prf (g D ⊆ D) → (Π S, Prf (S ⊆ D) → Prf (f S ⊆ g S)) → Prf (gfp D f ⊆ gfp D g) ≔
begin
    assume D f g gD fg;
    apply gfpLUB D f (gfp D g)
    {  refine ⊆-trans (f D) (g D) D _ gD;
       apply fg D;
       apply ⊆-refl D;
    }
    {  assume T TD fT;
       refine gfpUB D g T _ TD;
       apply ⊆-trans T (f T) (g T) fT;
       apply fg T TD;
    }
end;

// If f is monotonic then gfp is a post-fixed point ...
opaque symbol gfpPostFP D f : Prf (monotonic D f) → Prf (gfp D f ⊆ f (gfp D f)) ≔
begin
    assume D f mono;
    apply gfpLUB D f (f (gfp D f)) (monotonicDomain D f mono);
    assume T TD fT;
    apply ⊆-trans T (f T) (f (gfp D f)) fT;
    refine monotonicSubset D f T (gfp D f) mono _ (gfpSubsetDomain D f);
    apply gfpUB D f T fT TD;
end;

// ... as well as a pre-fixed point.
opaque symbol gfpPreFP D f : Prf (monotonic D f) → Prf (f (gfp D f) ⊆ gfp D f) ≔
begin
    assume D f mono;
    have fgfpD: Prf (f (gfp D f) ⊆ D)
    {  refine ⊆-trans (f (gfp D f)) (f D) D _ (monotonicDomain D f mono);
       apply monotonicSubset D f (gfp D f) D mono (gfpSubsetDomain D f) (⊆-refl D);
    };
    refine gfpUB D f (f (gfp D f)) _ fgfpD;
    apply monotonicSubset D f (gfp D f) (f (gfp D f)) mono (gfpPostFP D f mono) fgfpD;
end;

// Therefore, it is a fixed point.
opaque symbol gfpFixedPoint D f : Prf (monotonic D f) → Prf (f (gfp D f) = gfp D f) ≔
begin
    assume D f mono;
    apply ⊆-antisym (f (gfp D f)) (gfp D f) (gfpPreFP D f mono) (gfpPostFP D f mono);
end;

// And in fact, it is larger than any other fixed point.
opaque symbol gfpGreatestFixedPoint D f S : Prf (S ⊆ D) → Prf (f S = S) → Prf (S ⊆ gfp D f) ≔
begin
    assume D f S SD fS;
    refine gfpUB D f S _ SD;
    apply subst (f S) S (λ T, S ⊆ T) fS (⊆-refl S);
end;

