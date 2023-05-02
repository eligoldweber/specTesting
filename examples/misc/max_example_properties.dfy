module correctMaxExample {
    lemma maxExample(a:int,b:int) returns (c:int)
        requires a < 100 && b < 100
        ensures c >= a
        ensures c >= b
        ensures c == a || c == b


    lemma maxExample_Other_Assertion(a:int,b:int)
        requires a < 100 && b < 100
    {
            var result := maxExample(a,b);
            var result' := maxExample(a,b);
            assert result < 100;
    }
}

module wrongMaxExample {
    lemma maxExample(a:int,b:int) returns (c:int)
        requires a < 100 && b < 100
        ensures c >= a + 1
        ensures c >= b + 1
        ensures c == a + 1 || c == b + 1


    lemma maxExample_Other_Assertion(a:int,b:int)
        requires a < 100 && b < 100
    {
        var result := maxExample(a,b);
        assert result < 100;
    }
}

module wrongMaxExample2 {
    lemma maxExample(a:int,b:int) returns (c:int)
        requires a < 100 && b < 100
        ensures c >= a
        ensures c >= b

    lemma maxExample_Other_Assertion(a:int,b:int)
        requires a < 100 && b < 100
    {
        var result := maxExample(a,b);
        assert result < 100;
    }
}