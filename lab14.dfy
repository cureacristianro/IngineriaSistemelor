method identic6 (x: array <int >, n: int ) returns ( rez : bool )
ensures rez == ( forall i :: 0 <= i < n == > x[i] == x[i + 1])
{
    var i := 0;
    rez := true ;
    while i < n {
        if x[i] != x[i +1] {
            rez := false ;
        }
        i := i + 1;
    }
    return rez;
}