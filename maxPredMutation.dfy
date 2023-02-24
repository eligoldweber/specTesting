
module basic {

    predicate predMaxEx(a:int,b:int)
    {
        (a >= b && b > 100)
    }
    // lemma isSame_predMaxEx()
    // ensures (forall a,b :: predMaxEx(a,b) <==> predMaxEx_BASE(a,b))
    // {
    // }
}

module maxExample{

    predicate maxSpec(a:int,b:int,c:int)
    {
        c >= a
        && c >= b
    }

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
