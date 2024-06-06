method Main() {
  var n := 2;
  var result := Fibonacci(n);
  print result - 1;
}

function Fibonacci(n: nat): nat
  requires n >= 0
  ensures (n == 0 ==> Fibonacci(n) == 0) && (n == 1 ==> Fibonacci(n) == 1) && (n == 2 ==> Fibonacci(n) == 2) && (n > 2 ==> Fibonacci(n) == Fibonacci(n-1) + Fibonacci(n-2))
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else if n == 2  then
    2
  else
    Fibonacci(n - 1) + Fibonacci(n - 2) 
}
