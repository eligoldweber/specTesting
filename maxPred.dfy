
module basic {

    predicate predMaxEx(a:int,b:int)
    {
        (a >= b && b > 100)
        // a >= b
    }

    predicate basePredMaxEx(a:int,b:int)
    {
        // a >= b
         (a >= b && b > 100)
    }

    lemma {:timeLimitMultiplier 2}  isStronger()
    ensures forall a,b :: predMaxEx(a,b) ==> basePredMaxEx(a,b)
    {
    }
}

module maxExample{

    predicate maxSpec(a:int,b:int,c:int)
    {
        c >= a
        && c >= b
    }

    // predicate maxSpec_BASE(a:int,b:int,c:int)
    // {
    //     c >= a
    //     && c >= b
    // }

    // lemma isStronger()
    // ensures forall a,b,c :: maxSpec(a,b,c) ==> maxSpec_BASE(a,b,c)
    // {
    // }

    // lemma isSame_maxSpec()
    // ensures (forall a,b,c :: maxSpec(a,b,c) <==> maxSpec_BASE(a,b,c))
    // {
    // }

    lemma max(a:int,b:int) returns (c:int)
        ensures maxSpec(a,b,c)
    {
        if(a > b){
            c := a + 100;
        }else{
            c := b + 100;
        }
    }

}

module correctMaxExample{

    predicate maxSpec(a:int,b:int,c:int)
    {
        c >= a
        && c >= b
        && (c == b || c ==a)
    }

    predicate maxSpecBase(a:int,b:int,c:int)
    {
        c >= a
        && c >= b
        && (c == b || c ==a)
    }

    lemma {:timeLimitMultiplier 2}  isStronger()
    ensures forall a,b,c :: maxSpec(a,b,c) ==> maxSpecBase(a,b,c)
    {
    }

    lemma max(a:int,b:int) returns (c:int)
        ensures maxSpec(a,b,c)
    {
        if(a > b){
            c := a;
        }else{
            c := b;
        }
    }

}