// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Seed: 1236520955
// This is a RANDOMLY GENERATED PROGRAM.
// Fuzzer: dafny
// Version: dafny, xsmith 2.0.5 (38f1d83), in Racket 8.6 (vm-type chez-scheme)
// Options: --with-print-constrained true --timeout 300 --dafny-syntax true
// Seed: 1236520955
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
method lift_19 ()
  returns (arg_23 : int, arg_24 : int)
  requires (true)
  ensures (true)
{
  arg_23 := 906180123;
  arg_24 := 447678772;
  {
    var lift_86 := -1164118734;
    var lift_85 := multiset{lift_86, lift_86, arg_24, arg_23};
    var lift_84 := 'N';
    var lift_83 := arg_23;
    var lift_82 := lift_83;
    var lift_81 := 'a';
    var lift_80 := (lift_81, lift_81, arg_24);
    var lift_79 := 'L';
    var lift_78 := (
      lift_79,
      lift_80,
      multiset{arg_23, -1461672629, arg_23, lift_82}
    );
    var lift_77 := lift_78;
    var lift_76 := lift_77;
    var lift_75 := lift_76;
    var lift_74 := multiset{
      lift_75,
      (lift_84, lift_80, lift_85),
      lift_76,
      lift_77,
      lift_77
    };
    var lift_73 := [lift_74, lift_74, lift_74, lift_74];
    var lift_72 := 1204798250;
    var lift_71 := multiset{arg_24, arg_23, arg_23, arg_24, lift_72};
    var lift_70 := 1965867921;
    var lift_69 := '*';
    var lift_68 := lift_69;
    var lift_67 := lift_68;
    var lift_66 := (lift_67, lift_69, lift_70);
    var lift_65 := 'x';
    var lift_64 := (lift_65, lift_66, lift_71);
    var lift_63 := lift_64;
    var lift_62 := lift_63;
    var lift_61 := multiset{arg_24};
    var lift_60 := 104477877;
    var lift_59 := 'v';
    var lift_58 := (lift_59, lift_59, lift_60);
    var lift_57 := 'V';
    var lift_56 := lift_57;
    var lift_55 := lift_56;
    var lift_54 := (lift_55, lift_58, lift_61);
    var lift_53 := -505430447;
    var lift_52 := multiset{-1845820028, lift_53, arg_24, arg_24};
    var lift_51 := 'm';
    var lift_50 := lift_51;
    var lift_49 := (lift_50, lift_51, arg_24);
    var lift_48 := lift_49;
    var lift_47 := ('i', lift_48, lift_52);
    var lift_46 := multiset{lift_47, lift_54, lift_62, lift_63, lift_54};
    var lift_45 := lift_46;
    var lift_44 := -1109361036;
    var lift_43 := multiset{arg_24, lift_44, -1246306405, arg_24};
    var lift_42 := lift_43;
    var lift_41 := '=';
    var lift_40 := (lift_41, lift_41, arg_24);
    var lift_39 := lift_40;
    var lift_38 := '>';
    var lift_37 := (lift_38, lift_39, lift_42);
    var lift_36 := -528817896;
    var lift_35 := multiset{lift_36};
    var lift_34 := 'O';
    var lift_33 := 'z';
    var lift_32 := (lift_33, lift_34, 994754534);
    var lift_31 := ':';
    var lift_30 := (lift_31, lift_32, lift_35);
    var lift_29 := multiset{lift_30, lift_37};
    var lift_28 := [lift_29, lift_29, lift_45];
    var lift_27 := ();
    var lift_26 := lift_27;
    var lift_25 := (lift_26, lift_27);
    lift_25 := lift_25;
    print arg_23, "\n";
    lift_28 := lift_73;
    print lift_44, "\n";
    print lift_36, "\n";
  }
}

method lift_7 ()
  returns (arg_10 : int)
  requires (true)
  ensures (true)
{
  arg_10 := 724139921;
  {
    var lift_13 := -1383937187;
    var lift_12 := ();
    var lift_11 := lift_12;
    lift_11 := ();
    print 501005663, "\n";
    print arg_10, "\n";
    print lift_13, "\n";
    print arg_10, "\n";
  }
}

method lift_1 ()
  returns (arg_5 : int, arg_6 : int)
  requires (true)
  ensures (true)
{
  arg_5 := 1312479647;
  arg_6 := -1820392960;
  {
    print arg_6, "\n";
    print arg_5, "\n";
  }
}

method Main () {
  var lift_16 := 1839361883;
  var lift_15 := [lift_16];
  var lift_14 := lift_15;
  var methoddefvar_3, methoddefvar_4 := lift_1();
  {
    var lift_18 := true;
    var lift_17 := [lift_16];
    var methoddefvar_9 := lift_7();
    {
      print methoddefvar_3, "\n";
      lift_14 := lift_17;
      lift_18 := true;
    }
    var methoddefvar_21, methoddefvar_22 := lift_19();
    {
      print methoddefvar_21, "\n";
      print methoddefvar_21, "\n";
    }
  }
}


