// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment

method F() returns(x:int)
  ensures x == 6
{
  x := 5;
  x := (var y := 1; y + x);
}

method Main()
{
  var x := F();
  print x;
}
