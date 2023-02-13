


datatype Constants = Constants(capacity:int)
datatype CokeMachine = CokeMachine(numCokes:int)

predicate  predMaxEx(a:int,b:int,c:int)
{
  && c > a
  && c >= b
} 

// predicate pred<T(==)>(a:T,b:T)
// {
//     a == b
// }

// predicate divides(factor:nat, candidate:nat)
//   requires 1<=factor
// {
//   candidate % factor == 0
// }

// predicate StateTrans<C,V>(c:C,v:V,v':V)
// {
//   true
// }

// lemma isPredSM_ND<C,V>(c:C,v:V,v':V,v'':V)
//   requires StateTrans(c,v,v')
//   requires StateTrans(c,v,v'')
// //   ensures v' == v''
// //   {}

// predicate Purchase(c:Constants, v:CokeMachine, v':CokeMachine) 
// {
//     && v.numCokes > 0
//     && v'.numCokes == v.numCokes - 1
// }

// predicate PurchaseND(c:Constants, v:CokeMachine, v':CokeMachine) 
// {
//     && v.numCokes > 0
//     && v'.numCokes <= v.numCokes - 1
// }

// predicate pre<T>(a:T){
// 	true
// }

// predicate post<T>(a:T){
// 	true
// }



lemma {:extern} maxExample(a:int,b:int) returns (c:int)
	requires a > 0
  	ensures c > a
	ensures c > b


// lemma is_maxExample_ND(a:int,b:int)
//         requires a > 0
// {
//         var result := maxExample(a,b);
//         var result' := maxExample(a,b);
//         assert result == result';
// }

lemma maxExampleD(a:int,b:int) returns (c:int)
	ensures c >= a
	ensures c >= b
	ensures c == a || c == b

lemma is_maxExampleD_ND(a:int,b:int)
{
        var result := maxExampleD(a,b);
        var result' := maxExampleD(a,b);
        assert result == result';
}

// lemma isMaxExampleNDD(a:int,b:int)
// {
// 	var c := maxExampleD(a,b);
// 	var c' := maxExampleD(a,b);
// 	assert c == c';
// }

// lemma lemmaOrMethodThatReturnsAValue<T>(a:T) returns (b:T)
//     requires pre(a)
//     ensures post(b)

//   lemma isLemmaND<T>(a:T,a':T) returns (result:bool)
//     requires pre(a) && pre(a')
//     requires a == a'
//     // ensures result
//   {
//     var b := lemmaOrMethodThatReturnsAValue(a);
//     var b' := lemmaOrMethodThatReturnsAValue(a');
//     // return b == b';
//   }

//     predicate convertedPredicate<T>(a:T,b:T)
//     requires pre(a)
//   {
//     post(b)

//   }

//     lemma isConvertedLemmaorMethodND<T>(a:T,b:T,b':T)
//     requires pre(a)
//     requires convertedPredicate(a,b)
//     requires convertedPredicate(a,b')
//     // ensures b == b'
//     // {}
  