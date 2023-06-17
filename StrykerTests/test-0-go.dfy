// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Seed: 1863456124
// This is a RANDOMLY GENERATED PROGRAM.
// Fuzzer: dafny
// Version: dafny, xsmith 2.0.5 (38f1d83), in Racket 8.6 (vm-type chez-scheme)
// Options: --with-print-constrained true --timeout 300 --dafny-syntax true
// Seed: 1863456124
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
function lift_159 (
  arg_161 : (bool, int, char),
  arg_162 : char,
  arg_163 : set<char>
) : set<(char, bool, bool)>
{
  var lift_168 := 'a';
  var lift_167 := (lift_168, true, false);
  var lift_166 := lift_167;
  var lift_165 := lift_166;
  var lift_164 := {lift_165};
  lift_164
}

function lift_133 (arg_135 : char, arg_136 : (int, int)) : seq<multiset<int>>
{
  var lift_137 := (var tmpData : seq<multiset<int>> := []; tmpData);
  lift_137
}

method lift_120 (arg_123 : int)
  returns (arg_124 : int)
  requires (true)
  ensures (true)
{
  arg_124 := 1213831273;
  {
    var lift_126 := 'a';
    var lift_125 := 1389140263;
    print lift_125, "\n";
    lift_126 := 'I';
  }
}

method lift_113 (arg_117 : int)
  returns (arg_118 : int, arg_119 : int)
  requires (true)
  ensures (true)
{
  arg_118 := -1946390912;
  arg_119 := 367476816;
  {
    print arg_117, "\n";
  }
}

method lift_10 (arg_14 : int)
  returns (arg_15 : int, arg_16 : int)
  requires (true)
  ensures (true)
{
  arg_15 := 1354938043;
  arg_16 := 1831824122;
  {
    var lift_21 := 'D';
    var lift_20 := multiset{lift_21};
    var lift_19 := 'p';
    var lift_18 := lift_19;
    var lift_17 := multiset{lift_18};
    lift_17 := lift_20;
  }
}

method Main () {
  var lift_177 := '_';
  var lift_176 := lift_177;
  var lift_175 := lift_176;
  var lift_174 := 1188772172;
  var lift_173 := lift_174;
  var lift_172 := lift_173;
  var lift_171 := true;
  var lift_170 := (lift_171, lift_172, lift_175);
  var lift_169 := lift_170;
  var lift_158 := false;
  var lift_157 := 'C';
  var lift_156 := (lift_157, lift_158, lift_158);
  var lift_155 := {lift_156};
  var lift_154 := lift_155;
  var lift_153 := false;
  var lift_152 := true;
  var lift_151 := false;
  var lift_150 := 'C';
  var lift_149 := (lift_150, lift_151, lift_152);
  var lift_148 := {
    lift_149,
    lift_149,
    (lift_150, lift_153, lift_151),
    (lift_150, lift_153, lift_152),
    lift_149
  };
  var lift_147 := multiset{lift_148, lift_154};
  var lift_146 := true;
  var lift_145 := ('f', lift_146, lift_146);
  var lift_143 := {'$', '<'};
  var lift_142 := |lift_143|;
  var lift_141 := -1807175950;
  var lift_140 := -1799686701;
  var lift_139 := (lift_140, lift_141);
  var lift_138 := lift_139;
  var lift_132 := (var tmpData : multiset<int> := multiset{}; tmpData);
  var lift_131 := -973476513;
  var lift_130 := 1932605294;
  var lift_129 := multiset{lift_130, lift_131, lift_130};
  var lift_112 := false;
  var lift_111 := [lift_112, lift_112];
  var lift_110 := lift_111;
  var lift_109 := lift_110;
  var lift_108 := ();
  var lift_107 := lift_108;
  var lift_106 := lift_107;
  var lift_105 := true;
  var lift_104 := (lift_105, true);
  var lift_103 := (lift_104, lift_106, lift_109);
  var lift_99 := 'e';
  var lift_98 := lift_99;
  var lift_97 := -1678145155;
  var lift_96 := (lift_97, lift_98);
  var lift_95 := lift_96;
  var lift_94 := lift_95;
  var lift_93 := 'G';
  var lift_92 := lift_93;
  var lift_91 := lift_92;
  var lift_90 := 413617695;
  var lift_89 := (lift_90, lift_91);
  var lift_88 := 'u';
  var lift_87 := 'u';
  var lift_86 := lift_87;
  var lift_85 := 837650773;
  var lift_84 := lift_85;
  var lift_83 := (lift_84, lift_86);
  var lift_82 := multiset{lift_83, lift_83, lift_83, lift_83};
  var lift_81 := lift_82;
  var lift_80 := {
    lift_81,
    lift_81,
    multiset{(lift_84, lift_88), (786032023, lift_86), lift_89, lift_94},
    multiset{lift_83, lift_89, lift_96}
  };
  var lift_79 := -384595699;
  var lift_78 := lift_79;
  var lift_77 := {lift_78, 1932378897, lift_79};
  var lift_76 := lift_77;
  var lift_75 := lift_76;
  var lift_74 := 1523871371;
  var lift_73 := lift_74;
  var lift_72 := lift_73;
  var lift_71 := -783763637;
  var lift_70 := {lift_71, lift_72, lift_74};
  var lift_69 := 1883078382;
  var lift_68 := multiset{{lift_69}, lift_70, lift_75};
  var lift_64 := (var tmpData : multiset<bool> := multiset{}; tmpData);
  var lift_62 := true;
  var lift_61 := '!';
  var lift_60 := (lift_61, lift_62);
  var lift_58 := 'M';
  var lift_57 := lift_58;
  var lift_56 := (true, false);
  var lift_55 := (lift_56, lift_57);
  var lift_54 := lift_55;
  var lift_53 := 'L';
  var lift_52 := false;
  var lift_51 := (false, lift_52);
  var lift_50 := multiset{(lift_51, lift_53), lift_54};
  var lift_49 := 'c';
  var lift_48 := false;
  var lift_47 := lift_48;
  var lift_46 := false;
  var lift_45 := lift_46;
  var lift_44 := (lift_45, lift_47);
  var lift_43 := (lift_44, lift_49);
  var lift_39 := 't';
  var lift_38 := 'e';
  var lift_37 := 289521226;
  var lift_36 := lift_37;
  var lift_35 := (lift_36, '+', lift_38);
  var lift_34 := (lift_35, lift_39);
  var lift_33 := lift_34;
  var lift_32 := 'D';
  var lift_31 := -1530162173;
  var lift_30 := (lift_31, lift_32, 'o');
  var lift_28 := 'o';
  var lift_27 := -1256798407;
  var lift_26 := (lift_27, lift_28, lift_28);
  var lift_25 := (lift_26, '+');
  var lift_6 := false;
  var lift_5 := lift_6;
  var lift_4 := [lift_5, lift_6];
  var lift_3 := lift_4;
  var lift_2 := -1448354796;
  {
    var lift_67 := lift_68;
    var lift_66 := lift_67;
    var lift_41 := ();
    var lift_29 := (lift_30, lift_28);
    var lift_24 := {lift_25, lift_25, lift_29, lift_33};
    var lift_9 := ();
    var lift_8 := lift_9;
    var lift_7 := {lift_8};
    var lift_1 := lift_2;
    print lift_1, "\n";
    print (multiset(lift_3)[(lift_7 <= {lift_8, lift_8})] as int), "\n";
    var methoddefvar_12, methoddefvar_13 := lift_10(|lift_3|);
    {
      var lift_102 := (lift_51, lift_8, [lift_46, true]);
      var lift_101 := {lift_82};
      var lift_65 := (lift_66, lift_80);
      var lift_59 := lift_60;
      var lift_42 := (multiset{lift_43, lift_43}, (lift_32, false));
      var lift_40 := {
        ((methoddefvar_12, 'M', lift_38), lift_32),
        lift_25,
        lift_34,
        lift_34,
        lift_34
      };
      var lift_23 := false;
      {
        var lift_22 := '/';
        lift_22 := '%';
        lift_23 := lift_23;
      }
      {
        lift_24 := lift_40;
        print lift_31, "\n";
        print lift_31, "\n";
        lift_41 := lift_9;
      }
      if (lift_6) {
        var lift_63 := lift_64;
        lift_42 := (lift_50, lift_59);
        print lift_27, "\n";
        lift_63 := lift_64;
      } else {
        var lift_100 := (lift_68, lift_101);
        lift_65 := lift_100;
        lift_102 := lift_103;
      }
      var methoddefvar_115, methoddefvar_116 := lift_113(lift_72);
      {
        print 1066796399, "\n";
      }
      {
        print lift_84, "\n";
      }
    }
  }
  var methoddefvar_122 := lift_120(lift_25.0.0);
  {
    var lift_128 := [lift_129, lift_132, lift_132, lift_132];
    var lift_127 := lift_128;
    lift_127 := lift_133(lift_57, lift_138);
    print (multiset{lift_90, 1589659599}[lift_72] as int), "\n";
  }
  lift_142 := lift_138.0;
  {
    var lift_144 := {lift_145, lift_145, lift_145};
    print 
      ((multiset{
        {('E', lift_45, lift_45)},
        lift_144,
        {lift_145, lift_145},
        lift_144
      } - lift_147 - lift_147)[lift_159(lift_169, lift_38, lift_143)] as int),
      "\n";
  }
}


