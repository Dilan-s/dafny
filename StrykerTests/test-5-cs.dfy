// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Seed: 525348262
// This is a RANDOMLY GENERATED PROGRAM.
// Fuzzer: dafny
// Version: dafny, xsmith 2.0.5 (38f1d83), in Racket 8.6 (vm-type chez-scheme)
// Options: --with-print-constrained true --timeout 300 --dafny-syntax true
// Seed: 525348262
// 

function safeDivide (a : int, b : int) : int {
  if b == 0 then 0 else a / b
}

function safeSeqRef<T> (s : seq<T>, i : int, default : T) : T {
  if 0 <= i < |s| then s[i] else default
}

function safeSeqSet<T> (s : seq<T>, i : int, val : T) : seq<T> {
  if 0 <= i < |s| then s[i := val] else s
}

function safeSeqTake<T> (s : seq<T>, x : int) : seq<T> {
  if 0 <= x <= |s| then s[..x] else s
}

function safeSeqDrop<T> (s : seq<T>, x : int) : seq<T> {
  if 0 <= x <= |s| then s[x..] else s
}

function safeSeqSubseq<T> (s : seq<T>, x : int, y : int) : seq<T> {
  if 0 <= x <= y <= |s| then s[x..y] else s
}

function safeSeqSlice1Colon<T> (s : seq<T>, x : int) : seq<seq<T>> {
  if 0 <= x <= |s| then s[x:] else [s]
}

function safeSeqSlice2<T> (s : seq<T>, x : int, y: int) : seq<seq<T>> {
  if 0 <= x && 0 <= y && x + y <= |s| then s[x:y] else [s]
}

function safeSeqSlice3<T> (s : seq<T>, x : int, y : int, z : int) : seq<seq<T>> {
  if 0 <= x && 0 <= y && 0 <= z && x + y + z <= |s| then s[x:y:z] else [s]
}

function safeSeqSlice3Colon<T> (s : seq<T>, x : int, y : int, z : int) : seq<seq<T>> {
  if 0 <= x && 0 <= y && 0 <= z && x + y + z <= |s| then s[x:y:z:] else [s]
}

function lengthNormalize (x : int) : nat {
  (if x < 0 then -x else x) % 50
}
function lift_28 (arg_30 : seq<bool>) : set<((), ())>
{
  var lift_34 := ();
  var lift_33 := ();
  var lift_32 := (lift_33, lift_34);
  var lift_31 := {lift_32};
  lift_31
}

method lift_1 (arg_5 : int)
  returns (arg_6 : int, arg_7 : int)
  requires (true)
  ensures (true)
{
  arg_6 := -1461099075;
  arg_7 := 928655322;
  {
    var lift_17 := '$';
    var lift_16 := lift_17;
    var lift_15 := false;
    var lift_14 := arg_7;
    var lift_13 := true;
    var lift_12 := 'm';
    var lift_11 := (arg_7, lift_12, lift_13);
    var lift_10 := lift_11;
    var lift_9 := -453596626;
    var lift_8 := (lift_9, lift_10, {lift_14, arg_5, 29926087});
    print arg_5, "\n";
    print arg_5, "\n";
    lift_8 := lift_8;
    lift_15 := lift_15;
    lift_16 := lift_17;
  }
}

method Main () {
  var lift_51 := 1616341135;
  var lift_50 := false;
  var lift_49 := lift_50;
  var lift_48 := lift_49;
  var lift_47 := 834046964;
  var lift_46 := ('=', lift_47);
  var lift_45 := (lift_46, lift_48);
  var lift_44 := lift_45;
  var lift_43 := false;
  var lift_42 := 200922073;
  var lift_41 := '@';
  var lift_40 := (lift_41, lift_42);
  var lift_39 := (lift_40, lift_43);
  var lift_38 := multiset{lift_39};
  var lift_37 := false;
  var lift_27 := ();
  var lift_25 := ();
  var lift_24 := lift_25;
  var lift_19 := -404610058;
  var lift_18 := lift_19;
  var methoddefvar_3, methoddefvar_4 := lift_1(lift_18);
  {
    var lift_36 := [lift_37, lift_37, lift_37];
    var lift_35 := lift_36;
    var lift_26 := (lift_27, lift_27);
    var lift_23 := ();
    var lift_22 := ();
    var lift_21 := (lift_22, lift_22);
    var lift_20 := {lift_21, (lift_23, lift_24), lift_21, lift_21, lift_26};
    lift_20 := lift_28(lift_35);
    lift_38 := (lift_38[lift_44 := lengthNormalize(lift_51)]);
  }
}


