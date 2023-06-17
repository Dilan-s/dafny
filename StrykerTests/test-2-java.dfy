// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Seed: 1213835412
// This is a RANDOMLY GENERATED PROGRAM.
// Fuzzer: dafny
// Version: dafny, xsmith 2.0.5 (38f1d83), in Racket 8.6 (vm-type chez-scheme)
// Options: --with-print-constrained true --timeout 300 --dafny-syntax true
// Seed: 1213835412
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
method lift_280 (arg_284 : int, arg_285 : int)
  returns (arg_286 : int, arg_287 : int)
  requires (true)
  ensures (true)
{
  arg_286 := -228986504;
  arg_287 := 1670497343;
  {
    var lift_290 := true;
    var lift_289 := lift_290;
    var lift_288 := lift_289;
    print arg_285, "\n";
    lift_288 := lift_290;
  }
}

method lift_256 ()
  returns (arg_260 : int, arg_261 : int)
  requires (true)
  ensures (true)
{
  arg_260 := -350542558;
  arg_261 := -1917663327;
  {
    var lift_278 := 't';
    var lift_277 := 'o';
    var lift_276 := '<';
    var lift_275 := {lift_276, lift_276, lift_276, lift_277, lift_276};
    var lift_274 := false;
    var lift_273 := lift_274;
    var lift_272 := false;
    var lift_271 := '~';
    var lift_270 := lift_271;
    var lift_269 := 'b';
    var lift_268 := (
      [lift_269, lift_269, '-', lift_270],
      multiset{lift_272, lift_273, lift_273, lift_274}
    );
    var lift_267 := false;
    var lift_266 := multiset{lift_267, lift_267};
    var lift_265 := lift_266;
    var lift_264 := lift_265;
    var lift_263 := "Ag";
    var lift_262 := (lift_263, lift_264);
    lift_262 := lift_268;
    lift_275 := {lift_271, lift_276, lift_277, lift_276, lift_276};
    lift_278 := lift_277;
  }
}

method lift_231 (arg_235 : int, arg_236 : int, arg_237 : int)
  returns (arg_238 : int, arg_239 : int)
  requires (true)
  ensures (true)
{
  arg_238 := -1679743314;
  arg_239 := -342001446;
  {
    var lift_254 := '*';
    var lift_253 := (var tmpData : set<()> := {}; tmpData);
    var lift_252 := lift_253;
    var lift_251 := lift_252;
    var lift_250 := (lift_251, arg_239, lift_254);
    var lift_249 := true;
    var lift_248 := true;
    var lift_247 := lift_248;
    var lift_246 := lift_247;
    var lift_245 := lift_246;
    var lift_244 := (arg_239, lift_245);
    var lift_243 := lift_244;
    var lift_242 := true;
    var lift_241 := (1137317234, lift_242);
    var lift_240 := [lift_241, lift_243, lift_243, (arg_237, lift_249)];
    lift_240 := [(arg_236, lift_245), lift_241, lift_243, (arg_238, lift_249)];
    lift_250 := lift_250;
    print arg_239, "\n";
  }
}

method lift_186 (arg_189 : int, arg_190 : int)
  returns (arg_191 : int)
  requires (true)
  ensures (true)
{
  arg_191 := -1554585348;
  {
    var lift_199 := (arg_189, arg_190);
    var lift_198 := lift_199;
    var lift_197 := lift_198;
    var lift_196 := -1135706984;
    var lift_195 := (1718096528, lift_196);
    var lift_194 := 'b';
    var lift_193 := 790412537;
    var lift_192 := -663691704;
    print lift_192, "\n";
    lift_193 := lift_193;
    lift_194 := lift_194;
    lift_195 := lift_197;
  }
}

method lift_178 (arg_181 : int)
  returns (arg_182 : int)
  requires (true)
  ensures (true)
{
  arg_182 := -511046219;
  {
    var lift_183 := -225309092;
    lift_183 := arg_181;
  }
}

method lift_140 (arg_144 : int, arg_145 : int, arg_146 : int)
  returns (arg_147 : int, arg_148 : int)
  requires (true)
  ensures (true)
{
  arg_147 := -350112788;
  arg_148 := 634223346;
  {
    var lift_150 := 'a';
    var lift_149 := lift_150;
    lift_149 := lift_149;
    print -1758031070, "\n";
    print -1526783068, "\n";
    print arg_145, "\n";
  }
}

method lift_110 (arg_114 : int)
  returns (arg_115 : int, arg_116 : int)
  requires (true)
  ensures (true)
{
  arg_115 := 591103691;
  arg_116 := 362864685;
  {
    var lift_119 := ();
    var lift_118 := lift_119;
    var lift_117 := arg_114;
    lift_117 := arg_115;
    print arg_114, "\n";
    lift_118 := lift_119;
  }
}

method lift_51 (arg_54 : int)
  returns (arg_55 : int)
  requires (true)
  ensures (true)
{
  arg_55 := -1836622860;
  {
    var lift_56 := arg_55;
    print arg_55, "\n";
    print arg_55, "\n";
    print lift_56, "\n";
  }
}

function lift_23 (
  arg_25 : int,
  arg_26 : multiset<(int, (), (int, char, int))>
) : int
{
  
  arg_25
}

method lift_16 (arg_20 : int)
  returns (arg_21 : int, arg_22 : int)
  requires (true)
  ensures (true)
{
  arg_21 := 1770779750;
  arg_22 := 1752597383;
  {
    print -839629199, "\n";
    print arg_21, "\n";
  }
}

method Main () {
  var lift_308 := 'c';
  var lift_307 := lift_308;
  var lift_306 := '&';
  var lift_305 := '<';
  var lift_304 := multiset{lift_305, lift_306, lift_307};
  var lift_299 := true;
  var lift_298 := true;
  var lift_297 := lift_298;
  var lift_296 := (lift_297, lift_299);
  var lift_295 := (lift_296, lift_299);
  var lift_230 := 'T';
  var lift_229 := 'D';
  var lift_228 := {lift_229, lift_229, lift_229, lift_230};
  var lift_220 := -939532487;
  var lift_219 := lift_220;
  var lift_218 := lift_219;
  var lift_217 := 'F';
  var lift_216 := (lift_217, lift_218);
  var lift_215 := lift_216;
  var lift_214 := 'A';
  var lift_213 := '-';
  var lift_212 := {'e', lift_213, lift_214};
  var lift_211 := lift_212;
  var lift_205 := true;
  var lift_204 := 949355980;
  var lift_203 := 't';
  var lift_202 := (lift_203, lift_204, lift_205);
  var lift_176 := ();
  var lift_175 := lift_176;
  var lift_174 := '~';
  var lift_173 := (lift_174, lift_175, ());
  var lift_172 := ();
  var lift_171 := 'R';
  var lift_170 := (lift_171, (), lift_172);
  var lift_169 := {lift_170, (lift_171, lift_172, lift_172), lift_173};
  var lift_168 := lift_169;
  var lift_165 := ();
  var lift_164 := ();
  var lift_163 := ('O', lift_164, lift_165);
  var lift_160 := false;
  var lift_159 := lift_160;
  var lift_158 := 2019522868;
  var lift_157 := {lift_158};
  var lift_154 := 912265791;
  var lift_151 := -1462571543;
  var lift_139 := (var tmpData : string := []; tmpData);
  var lift_136 := 'R';
  var lift_135 := true;
  var lift_134 := [lift_135];
  var lift_133 := true;
  var lift_132 := (lift_133, lift_134, lift_136);
  var lift_128 := ();
  var lift_127 := lift_128;
  var lift_126 := 'p';
  var lift_125 := lift_126;
  var lift_124 := 'Y';
  var lift_123 := ({'k', lift_124, lift_125, lift_125}, lift_125, lift_127);
  var lift_121 := (var tmpData : multiset<multiset<multiset<int>>> := multiset{}; tmpData);
  var lift_109 := ();
  var lift_108 := ();
  var lift_107 := multiset{lift_108};
  var lift_106 := lift_107;
  var lift_105 := lift_106;
  var lift_104 := -707242265;
  var lift_103 := 1639721478;
  var lift_102 := [lift_103, lift_103, lift_103, lift_104];
  var lift_101 := false;
  var lift_100 := 1200095666;
  var lift_99 := lift_100;
  var lift_98 := '?';
  var lift_97 := lift_98;
  var lift_96 := (lift_97, lift_99, lift_101);
  var lift_95 := lift_96;
  var lift_94 := (lift_95, 1366582909, lift_102);
  var lift_93 := lift_94;
  var lift_92 := lift_93;
  var lift_90 := 1759439010;
  var lift_89 := [lift_90, 1103419027, lift_90, lift_90];
  var lift_88 := lift_89;
  var lift_87 := true;
  var lift_86 := -1120038480;
  var lift_85 := 'h';
  var lift_84 := (lift_85, lift_86, lift_87);
  var lift_83 := lift_84;
  var lift_79 := true;
  var lift_78 := lift_79;
  var lift_77 := 'X';
  var lift_76 := '!';
  var lift_75 := [lift_76, lift_77, lift_77];
  var lift_72 := ();
  var lift_71 := lift_72;
  var lift_70 := lift_71;
  var lift_69 := lift_70;
  var lift_68 := -216205803;
  var lift_67 := 'C';
  var lift_66 := (lift_67, lift_68);
  var lift_62 := (var tmpData : set<int> := {}; tmpData);
  var lift_50 := 'X';
  var lift_49 := '\'';
  var lift_48 := 52825181;
  var lift_47 := lift_48;
  var lift_46 := multiset{lift_47, lift_47, lift_47};
  var lift_45 := (lift_46, (lift_49, lift_50, lift_47));
  var lift_44 := true;
  var lift_43 := lift_44;
  var lift_42 := 'w';
  var lift_40 := 'G';
  var lift_39 := multiset{lift_40, '-'};
  var lift_38 := lift_39;
  var lift_37 := lift_38;
  var lift_35 := -174326613;
  var lift_34 := lift_35;
  var lift_33 := lift_34;
  var lift_32 := (lift_33, 'Z', lift_35);
  var lift_31 := ();
  var lift_30 := 458765497;
  var lift_29 := lift_30;
  var lift_28 := (lift_29, lift_31, lift_32);
  var lift_15 := (var tmpData : seq<bool> := []; tmpData);
  var lift_14 := -976485232;
  var lift_13 := -1842058890;
  var lift_12 := false;
  var lift_11 := lift_12;
  var lift_10 := true;
  var lift_9 := [lift_10, lift_10, lift_10, lift_10, lift_11];
  var lift_8 := 'D';
  var lift_7 := false;
  var lift_6 := lift_7;
  var lift_5 := false;
  var lift_4 := (lift_5, lift_6, lift_8);
  var lift_3 := '<';
  var lift_2 := true;
  var lift_1 := (lift_2, true, lift_3);
  if ((((lift_1 !in {lift_1, lift_1, lift_4}) in lift_9) !in safeSeqRef(
    safeSeqSlice3Colon(
      [lift_6, lift_2, lift_6, true],
      lift_13,
      lift_13,
      lift_14
    ),
    (lift_3 as int),
    lift_15
  ))) {
    var lift_36 := ();
    var lift_27 := multiset{lift_28, (679624841, lift_36, lift_32), lift_28};
    var methoddefvar_18, methoddefvar_19 := lift_16(lift_23(lift_13, lift_27));
    {
      var lift_41 := lift_8;
      if (lift_5) {
        print 425440873, "\n";
        print lift_34, "\n";
        print lift_35, "\n";
        lift_37 := lift_38;
        print lift_29, "\n";
      } else {
        lift_41 := lift_3;
        lift_42 := lift_42;
        print lift_14, "\n";
        lift_43 := lift_44;
        print 911458964, "\n";
      }
    }
  } else {
    var lift_82 := (lift_83, lift_30, lift_88);
    var lift_80 := multiset{lift_47, lift_34, lift_14, lift_14};
    var lift_63 := (lift_48, lift_35);
    var lift_61 := (lift_62, lift_63, lift_31);
    print lift_45.1.2, "\n";
    var methoddefvar_53 := lift_51(lift_33);
    {
      var lift_81 := multiset{lift_35, 733924575};
      var lift_74 := (lift_66, lift_69, lift_75);
      var lift_73 := "hApnC@hjJ/$G;ESiLm";
      var lift_65 := lift_66;
      var lift_59 := {lift_37, lift_39, lift_37};
      var methoddefvar_57, methoddefvar_58 := lift_16(lift_34);
      {
        var lift_64 := (lift_65, lift_69, lift_73);
        var lift_60 := lift_61;
        lift_59 := lift_59;
        lift_60 := lift_61;
        lift_64 := lift_74;
      }
      lift_78 := lift_78;
      if (lift_11) {
        print lift_14, "\n";
        print lift_47, "\n";
        lift_80 := lift_81;
      } else {
        var lift_91 := lift_92;
        lift_82 := lift_91;
        lift_105 := multiset{lift_71, lift_71, lift_108, lift_108, lift_109};
        print lift_90, "\n";
      }
      var methoddefvar_112, methoddefvar_113 := lift_110(lift_99);
      {
        var lift_120 := lift_9;
        lift_120 := [lift_5, lift_5, lift_10, lift_44];
      }
      lift_121 := lift_121;
    }
  }
  {
    var lift_227 := (lift_33, lift_87, true);
    var lift_226 := (lift_11, (lift_220, lift_227), lift_228);
    var lift_224 := (-1769234982, lift_78, lift_12);
    var lift_207 := ((lift_171, lift_14, lift_2), lift_108, lift_62);
    var lift_185 := "baYVX:BAXo";
    var lift_153 := [(), lift_108, lift_109];
    var lift_152 := [lift_72, lift_70];
    var lift_138 := [lift_139, lift_75, lift_75, lift_75];
    var lift_137 := (lift_127, lift_101, lift_14);
    var lift_131 := [lift_34, lift_90, -538760473];
    var lift_130 := [-1944091341, lift_86];
    var lift_129 := (lift_100, lift_130, (lift_43, lift_69));
    var lift_122 := lift_123.2;
    lift_122 := lift_129.2.1;
    lift_131 := safeSeqDrop(safeSeqDrop(lift_131, 1456539556), |lift_89|);
    print lift_30, "\n";
    if (safeSeqRef(
      lift_132.1,
      lift_137.2,
      ("fvV&UDLMN/fhX~S$H?DIQvH?JPfgxIQlJ" !in lift_138)
    )) {
      var methoddefvar_142, methoddefvar_143 := lift_140(
        lift_34,
        lift_35,
        lift_68
      );
      {
        print lift_48, "\n";
        lift_151 := lift_90;
      }
      lift_152 := lift_153;
      lift_154 := |lift_106|;
    } else {
      var lift_225 := lift_226;
      var lift_223 := (lift_34, lift_224);
      var lift_210 := (lift_96, lift_72, lift_62);
      var lift_208 := {lift_100, lift_30};
      var lift_200 := {-2040981964, -31149482, lift_35, lift_100, lift_103};
      var lift_184 := (var tmpData : set<set<int>> := {}; tmpData);
      var lift_166 := (lift_67, (), ());
      var methoddefvar_155, methoddefvar_156 := lift_110(lift_151);
      {
        lift_157 := lift_62;
        print -445987060, "\n";
        print lift_29, "\n";
      }
      {
        var lift_209 := multiset{lift_210, lift_210};
        var lift_206 := lift_207;
        var lift_201 := multiset{
          (lift_202, lift_72, lift_62),
          lift_206,
          (lift_83, lift_164, lift_208),
          (lift_84, lift_172, lift_200)
        };
        var lift_167 := (lift_168, lift_124);
        {
          var lift_177 := -1587708018;
          var lift_162 := {(lift_126, lift_108, lift_70), lift_163, lift_166};
          var lift_161 := (lift_162, lift_49);
          lift_159 := lift_12;
          print lift_14, "\n";
          lift_161 := lift_167;
          lift_177 := lift_29;
        }
        var methoddefvar_180 := lift_178(lift_90);
        {
          print 1330276774, "\n";
          lift_184 := lift_184;
          lift_185 := lift_139;
        }
        var methoddefvar_188 := lift_186(lift_34, lift_99);
        {
          print lift_47, "\n";
        }
        if (lift_44) {
          print 373232117, "\n";
          lift_200 := lift_157;
          lift_201 := lift_209;
          lift_211 := lift_212;
          lift_215 := lift_215;
        } else {
          print lift_99, "\n";
          print lift_204, "\n";
          print lift_151, "\n";
          print lift_90, "\n";
        }
      }
      var methoddefvar_221, methoddefvar_222 := lift_110(lift_47);
      {
        print lift_68, "\n";
        print lift_30, "\n";
      }
      lift_223 := lift_225.1;
      var methoddefvar_233, methoddefvar_234 := lift_231(
        lift_100,
        lift_48,
        lift_99
      );
      {
        var lift_255 := false;
        print lift_47, "\n";
        lift_255 := false;
      }
    }
  }
  var methoddefvar_258, methoddefvar_259 := lift_256();
  {
    var lift_300 := false;
    var lift_294 := lift_295;
    var lift_293 := (lift_11, lift_101);
    var lift_292 := (lift_293, lift_160);
    var lift_291 := lift_292;
    var lift_279 := {lift_175, lift_176, lift_172, lift_72, lift_69};
    print 
      (
        lift_47,
        (multiset{lift_8, lift_230}, ()),
        (var tmpData : multiset<set<set<int>>> := multiset{}; tmpData)
      ).0,
      "\n";
    if ((lift_279 == lift_279)) {
      var methoddefvar_282, methoddefvar_283 := lift_280(
        methoddefvar_259,
        lift_13
      );
      {
        lift_291 := lift_294;
        lift_300 := lift_2;
      }
    } else {
      var lift_309 := {lift_10};
      var lift_302 := ();
      var lift_301 := [lift_43];
      print lift_29, "\n";
      if (lift_2) {
        print lift_47, "\n";
        print lift_35, "\n";
        lift_301 := lift_9;
      } else {
        var lift_303 := ();
        lift_302 := lift_165;
        print lift_100, "\n";
        lift_303 := lift_172;
        lift_304 := lift_37;
      }
      if (lift_133) {
        print lift_99, "\n";
        lift_309 := lift_309;
      } else {
        print lift_34, "\n";
      }
    }
  }
}


