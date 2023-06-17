// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Seed: 1719292042
// This is a RANDOMLY GENERATED PROGRAM.
// Fuzzer: dafny
// Version: dafny, xsmith 2.0.5 (38f1d83), in Racket 8.6 (vm-type chez-scheme)
// Options: --with-print-constrained true --timeout 300 --dafny-syntax true
// Seed: 1719292042
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
method lift_235 ()
  returns (arg_239 : int, arg_240 : int)
  requires (true)
  ensures (true)
{
  arg_239 := -1490463126;
  arg_240 := 303691014;
  {
    print arg_239, "\n";
    print arg_239, "\n";
  }
}

method lift_176 ()
  returns (arg_180 : int, arg_181 : int)
  requires (true)
  ensures (true)
{
  arg_180 := -1023126430;
  arg_181 := -1422964131;
  {
    var lift_183 := -672634485;
    var lift_182 := -2115796218;
    print lift_182, "\n";
    print arg_181, "\n";
    print lift_183, "\n";
  }
}

method lift_134 (arg_138 : int, arg_139 : int)
  returns (arg_140 : int, arg_141 : int)
  requires (true)
  ensures (true)
{
  arg_140 := 1898656691;
  arg_141 := -966816427;
  {
    var lift_153 := ();
    var lift_152 := lift_153;
    var lift_151 := lift_152;
    var lift_150 := lift_151;
    var lift_149 := [lift_150, lift_150, lift_151];
    var lift_148 := true;
    var lift_147 := lift_148;
    var lift_146 := {lift_147, true};
    var lift_145 := lift_146;
    var lift_144 := true;
    var lift_143 := {lift_144};
    var lift_142 := [
      lift_143,
      lift_145,
      lift_143,
      lift_143,
      {lift_147, lift_147, lift_144, true, lift_147}
    ];
    print arg_140, "\n";
    print arg_141, "\n";
    lift_142 := lift_142;
    print arg_138, "\n";
    lift_149 := lift_149;
  }
}

method lift_128 (arg_131 : int)
  returns (arg_132 : int)
  requires (true)
  ensures (true)
{
  arg_132 := 1609449090;
  {
    var lift_133 := true;
    print arg_132, "\n";
    lift_133 := false;
  }
}

method lift_121 (arg_124 : int, arg_125 : int, arg_126 : int)
  returns (arg_127 : int)
  requires (true)
  ensures (true)
{
  arg_127 := -1164242263;
  {
    print -797660814, "\n";
  }
}

method lift_41 (arg_45 : int, arg_46 : int)
  returns (arg_47 : int, arg_48 : int)
  requires (true)
  ensures (true)
{
  arg_47 := -456719755;
  arg_48 := 795180751;
  {
    var lift_49 := 'a';
    lift_49 := 'q';
  }
}

function lift_34 (arg_36 : ()) : char
{
  var lift_37 := 'S';
  lift_37
}

method lift_1 (arg_4 : int)
  returns (arg_5 : int)
  requires (true)
  ensures (true)
{
  arg_5 := -255342025;
  {
    var lift_6 := -1347488226;
    print lift_6, "\n";
  }
}

method Main () {
  var lift_276 := ();
  var lift_275 := (-169420038, lift_276);
  var lift_274 := ();
  var lift_273 := -1415921061;
  var lift_272 := (lift_273, lift_274);
  var lift_271 := {lift_272, lift_272, lift_272, lift_275};
  var lift_269 := false;
  var lift_268 := lift_269;
  var lift_267 := 'J';
  var lift_266 := (lift_267, lift_268);
  var lift_265 := 'j';
  var lift_264 := (2027404983, true, lift_265);
  var lift_263 := (lift_264, lift_266);
  var lift_259 := 1080753042;
  var lift_258 := (-684566782, lift_259);
  var lift_255 := '+';
  var lift_254 := (lift_255, false);
  var lift_253 := true;
  var lift_252 := lift_253;
  var lift_251 := lift_252;
  var lift_250 := 'K';
  var lift_249 := lift_250;
  var lift_248 := (lift_249, lift_251);
  var lift_247 := (lift_248, lift_252, lift_254);
  var lift_233 := 'Q';
  var lift_232 := 'T';
  var lift_231 := lift_232;
  var lift_230 := lift_231;
  var lift_229 := lift_230;
  var lift_228 := (lift_229, true);
  var lift_227 := -131285135;
  var lift_226 := 'Q';
  var lift_225 := false;
  var lift_224 := (lift_225, lift_226, lift_227);
  var lift_223 := (lift_224, lift_228);
  var lift_217 := true;
  var lift_216 := -1345452334;
  var lift_215 := -1780658226;
  var lift_214 := -1629748401;
  var lift_213 := [lift_214, lift_215, lift_214, lift_216];
  var lift_212 := ();
  var lift_211 := multiset{lift_212, ()};
  var lift_210 := 'W';
  var lift_209 := [lift_210, 'e', '&', lift_210, lift_210];
  var lift_208 := (lift_209, lift_211, lift_213);
  var lift_203 := (true, 'v');
  var lift_196 := -1031455850;
  var lift_195 := false;
  var lift_194 := (lift_195, lift_195, lift_196);
  var lift_193 := (true, lift_194);
  var lift_192 := lift_193;
  var lift_186 := ();
  var lift_185 := lift_186;
  var lift_184 := multiset{(), lift_185, lift_185, lift_185, lift_186};
  var lift_175 := (var tmpData : seq<seq<bool>> := []; tmpData);
  var lift_174 := lift_175;
  var lift_173 := '|';
  var lift_172 := 1857416626;
  var lift_171 := (lift_172, lift_173);
  var lift_170 := false;
  var lift_169 := lift_170;
  var lift_168 := 720633593;
  var lift_167 := lift_168;
  var lift_166 := (lift_167, lift_167, lift_169);
  var lift_165 := (lift_166, lift_171, lift_174);
  var lift_162 := (var tmpData : seq<seq<bool>> := []; tmpData);
  var lift_161 := 'l';
  var lift_160 := true;
  var lift_159 := lift_160;
  var lift_158 := lift_159;
  var lift_157 := (lift_158, lift_161);
  var lift_156 := (lift_157, lift_162);
  var lift_155 := lift_156.1;
  var lift_154 := 643771785;
  var lift_119 := (var tmpData : seq<char> := []; tmpData);
  var lift_118 := true;
  var lift_117 := false;
  var lift_116 := (lift_117, lift_118);
  var lift_115 := (lift_116, lift_119);
  var lift_114 := 547405030;
  var lift_113 := false;
  var lift_112 := lift_113;
  var lift_111 := 'c';
  var lift_110 := lift_111;
  var lift_109 := 2042213169;
  var lift_108 := (lift_109, lift_110, lift_112);
  var lift_102 := ();
  var lift_101 := ();
  var lift_100 := {lift_101, (), lift_102};
  var lift_99 := lift_100;
  var lift_98 := lift_99;
  var lift_88 := ();
  var lift_87 := [lift_88];
  var lift_86 := lift_87;
  var lift_80 := 2108055399;
  var lift_79 := -439045946;
  var lift_78 := 'n';
  var lift_77 := lift_78;
  var lift_76 := lift_77;
  var lift_75 := (lift_76, lift_79, lift_80);
  var lift_73 := 'M';
  var lift_72 := 'g';
  var lift_71 := 1486004737;
  var lift_70 := (lift_71, true, lift_72);
  var lift_69 := (lift_70, lift_73);
  var lift_68 := lift_69;
  var lift_67 := lift_68;
  var lift_66 := 'u';
  var lift_65 := true;
  var lift_64 := -1467014360;
  var lift_63 := (lift_64, lift_65, lift_66);
  var lift_62 := (lift_63, lift_66);
  var lift_61 := {lift_62, lift_62, lift_67};
  var lift_60 := -565487413;
  var lift_59 := true;
  var lift_58 := (lift_59, ('T', lift_60, lift_60), lift_61);
  var lift_56 := false;
  var lift_55 := lift_56;
  var lift_54 := lift_55;
  var lift_53 := 'o';
  var lift_52 := (lift_53, lift_54);
  var lift_51 := lift_52;
  var lift_40 := ();
  var lift_39 := lift_40;
  var lift_38 := lift_39;
  var lift_27 := ();
  var lift_25 := true;
  var lift_24 := false;
  var lift_23 := (lift_24, lift_25, lift_24);
  var lift_22 := true;
  var lift_21 := true;
  var lift_20 := lift_21;
  var lift_19 := (lift_20, lift_22, lift_22);
  var lift_18 := 'V';
  var lift_17 := multiset{lift_18};
  var lift_16 := lift_17;
  var lift_15 := (var tmpData : multiset<char> := multiset{}; tmpData);
  var lift_14 := [lift_15, lift_15, lift_16];
  var lift_7 := -1434158739;
  var methoddefvar_3 := lift_1(lift_7);
  {
    var lift_33 := (var tmpData : seq<(char, bool)> := []; tmpData);
    var lift_30 := -1761639540;
    var lift_29 := ();
    var lift_26 := lift_27;
    var lift_13 := lift_14;
    var lift_10 := true;
    var lift_9 := '|';
    var lift_8 := 'i';
    lift_8 := lift_9;
    {
      var lift_32 := lift_33;
      var lift_12 := -2050074454;
      print lift_7, "\n";
      print lift_7, "\n";
      if (lift_10) {
        var lift_11 := multiset{lift_9};
        print 483587787, "\n";
        lift_11 := lift_11;
        print lift_12, "\n";
        lift_13 := lift_14;
        print -1657565823, "\n";
      } else {
        print lift_12, "\n";
        lift_19 := lift_23;
      }
      {
        var lift_28 := ();
        print lift_12, "\n";
        lift_26 := lift_28;
        print lift_7, "\n";
        print lift_7, "\n";
      }
      if (lift_20) {
        print lift_12, "\n";
        print lift_7, "\n";
        lift_29 := lift_26;
      } else {
        var lift_31 := -1843230215;
        print methoddefvar_3, "\n";
        print lift_30, "\n";
        lift_31 := lift_12;
        lift_32 := lift_33;
        print lift_30, "\n";
      }
    }
  }
  {
    var lift_164 := lift_165;
    var lift_163 := lift_164;
    var lift_107 := multiset{lift_108, lift_108, lift_108};
    var lift_106 := (lift_107, lift_78, -206397487);
    var lift_105 := (var tmpData : multiset<(int, char, bool)> := multiset{}; tmpData);
    var lift_104 := lift_105;
    var lift_92 := ['s', lift_77, 'H'];
    var lift_89 := lift_86;
    var lift_83 := 581415018;
    var lift_82 := (var tmpData : set<((int, bool, char), char)> := {}; tmpData);
    var lift_57 := {'l'};
    var lift_50 := (lift_18, lift_20);
    print (lift_34(lift_38) as int), "\n";
    var methoddefvar_43, methoddefvar_44 := lift_41(
      (
        "fa",
        (
          {
            multiset{('N', lift_22), (lift_18, false), ('k', lift_22), lift_50},
            multiset{lift_51, lift_51}
          },
          "~/^hyqY/DVa~/W_/ve"
        ),
        lift_7
      ).2,
      |lift_57|
    );
    {
      var lift_81 := lift_82;
      {
        var lift_74 := (lift_56, lift_75, lift_81);
        lift_58 := lift_74;
        print lift_60, "\n";
        print lift_79, "\n";
        print lift_83, "\n";
      }
      var methoddefvar_84, methoddefvar_85 := lift_41(
        -525858628,
        methoddefvar_44
      );
      {
        print lift_80, "\n";
        lift_86 := lift_89;
      }
    }
    {
      var lift_91 := (lift_55, lift_92, ('%', false, lift_60));
      var lift_90 := lift_91;
      if (lift_23.2) {
        var lift_97 := ();
        var lift_95 := multiset{lift_83, lift_64, lift_60, lift_64, lift_64};
        print lift_80, "\n";
        lift_90 := lift_91;
        var methoddefvar_93, methoddefvar_94 := lift_41(lift_60, lift_79);
        {
          var lift_96 := (lift_97, lift_98);
          lift_95 := multiset{lift_60, methoddefvar_93, methoddefvar_93};
          lift_96 := lift_96;
          print lift_83, "\n";
          print lift_83, "\n";
        }
      } else {
        var lift_120 := lift_113;
        var lift_103 := (lift_104, lift_73, lift_79);
        {
          lift_103 := lift_106;
          lift_114 := lift_79;
          lift_115 := lift_115;
          print lift_71, "\n";
          lift_120 := lift_22;
        }
        var methoddefvar_123 := lift_121(lift_79, lift_60, lift_7);
        {
          print lift_60, "\n";
          print lift_79, "\n";
          print -333394999, "\n";
        }
        var methoddefvar_130 := lift_128(lift_83);
        {
          print lift_80, "\n";
          print 404349855, "\n";
        }
        print lift_71, "\n";
      }
      var methoddefvar_136, methoddefvar_137 := lift_134(lift_60, lift_109);
      {
        lift_154 := lift_7;
        print lift_7, "\n";
      }
    }
    lift_155 := safeSeqDrop(
      lift_163.2,
      |(var tmpData : set<bool> := {}; tmpData)|
    );
  }
  var methoddefvar_178, methoddefvar_179 := lift_176();
  {
    var lift_270 := (lift_264, lift_254);
    var lift_257 := (lift_7, lift_258);
    var lift_256 := lift_257;
    var lift_222 := ('u', lift_170);
    var lift_221 := (false, 'M', lift_80);
    var lift_219 := multiset{false, lift_65, lift_118, true, lift_195};
    var lift_204 := {lift_38, lift_38, lift_27, lift_102};
    var lift_202 := (lift_54, lift_111);
    var lift_191 := lift_192;
    var lift_190 := (lift_21, lift_25, lift_7);
    var lift_189 := (lift_118, lift_190);
    print 
      (multiset{
        multiset{()},
        multiset{lift_88, ()},
        lift_184,
        lift_184
      }[lift_184] as int),
      "\n";
    if ((lift_158 ==> lift_25)) {
      var lift_218 := multiset{lift_160, lift_55, lift_22};
      var lift_207 := lift_208;
      var lift_206 := lift_207;
      var lift_201 := [lift_202, lift_203];
      var lift_200 := (var tmpData : seq<(bool, char)> := []; tmpData);
      var lift_199 := (var tmpData : multiset<multiset<bool>> := multiset{}; tmpData);
      var lift_198 := lift_199;
      var methoddefvar_187 := lift_1(lift_64);
      {
        var lift_188 := {lift_189, lift_191, lift_192, lift_189};
        print methoddefvar_178, "\n";
        lift_188 := lift_188;
        print -1037186758, "\n";
      }
      var methoddefvar_197 := lift_121(760928686, lift_172, lift_172);
      {
        lift_198 := lift_199;
        lift_200 := lift_201;
        print 217857784, "\n";
        print lift_154, "\n";
      }
      if (lift_160) {
        var lift_205 := lift_109;
        print 299431747, "\n";
        print lift_80, "\n";
        lift_204 := lift_99;
        lift_205 := lift_167;
      } else {
        lift_206 := lift_207;
        lift_217 := true;
      }
      {
        var lift_234 := -500189220;
        var lift_220 := (lift_221, lift_222);
        print -1093377167, "\n";
        lift_218 := lift_219;
        lift_220 := lift_223;
        lift_233 := lift_173;
        lift_234 := lift_167;
      }
      print lift_79, "\n";
    } else {
      var lift_261 := {lift_21, lift_252, lift_21, lift_59, true};
      var lift_260 := (lift_219, lift_21, lift_261);
      var lift_246 := (lift_222, lift_160, lift_222);
      var lift_245 := {
        (lift_52, lift_169, lift_222),
        lift_246,
        lift_247,
        lift_247,
        lift_247
      };
      var lift_244 := lift_245;
      var lift_243 := lift_244;
      print methoddefvar_178, "\n";
      var methoddefvar_237, methoddefvar_238 := lift_235();
      {
        print methoddefvar_237, "\n";
        print methoddefvar_237, "\n";
      }
      {
        var lift_242 := (lift_228, lift_38, lift_243);
        var lift_241 := ();
        lift_241 := ();
        print lift_64, "\n";
        lift_242 := lift_242;
        lift_256 := lift_257;
        lift_260 := lift_260;
      }
    }
    var methoddefvar_262 := lift_128(lift_154);
    {
      lift_263 := lift_270;
      lift_271 := {lift_272, (lift_215, lift_102)};
      print lift_227, "\n";
    }
  }
}


