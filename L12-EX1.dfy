method Triple (x: int ) returns (r: int)
requires x % 2 == 0
ensures r == 3 * x
{
    var y := 2 * x;
    r := x + y; 
    //assert r == 3 * x;
    //assert r == 10 *x;
    //assert r < 5;
    //assert false;
}

method Caller()
{
    var result := Triple(18);
    assert result < 100;
}

method Index(n: int) returns (i: int)
requires 1 <= n
ensures 0 <= i < n
{
    i := 0;
}

method Min(x: int , y: int ) returns (m: int )
ensures m <= x && m <= y
{
   if x <= y {
        m := x;
    } else {
        m := y;
    }
}

method Minfake (x: int , y: int) returns (m: int )
ensures m <= x && m <= y
{
    if x <= y {
        m := x - 10;
    } else {    
        m := y - 20;
    }
}

function Average (a: int , b: int) : int
requires 0 <= a && 0 <= b
{
    (a + b) / 2
}

predicate IsEven (x: int ) {
    x % 2 == 0
}