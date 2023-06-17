// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Seed: 485991151
// This is a RANDOMLY GENERATED PROGRAM.
// Fuzzer: dafny
// Version: dafny, xsmith 2.0.5 (38f1d83), in Racket 8.6 (vm-type chez-scheme)
// Options: --with-print-constrained true --timeout 300 --dafny-syntax true
// Seed: 485991151
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
method lift_495 (arg_498 : int, arg_499 : int)
  returns (arg_500 : int)
  requires (true)
  ensures (true)
{
  arg_500 := -741397081;
  {
    print -830782586, "\n";
  }
}

function lift_476 (
  arg_478 : (bool, int),
  arg_479 : set<bool>,
  arg_480 : char
) : ((), (bool, bool, char))
{
  var lift_485 := '+';
  var lift_484 := false;
  var lift_483 := lift_484;
  var lift_482 := (lift_483, lift_484, lift_485);
  var lift_481 := ((), lift_482);
  lift_481
}

function lift_396 (
  arg_398 : multiset<char>,
  arg_399 : char,
  arg_400 : int
) : char
{
  
  arg_399
}

function lift_390 (
  arg_392 : int,
  arg_393 : bool,
  arg_394 : seq<multiset<multiset<multiset<bool>>>>,
  arg_395 : (bool, ())
) : ((multiset<char>, char, int) -> char)
{
  
  lift_396
}

function lift_359 (arg_361 : int, arg_362 : (int, int, int)) : set<(bool, int)>
{
  var lift_374 := -1456797540;
  var lift_373 := false;
  var lift_372 := lift_373;
  var lift_371 := (lift_372, 1264021420);
  var lift_370 := lift_371;
  var lift_369 := lift_370;
  var lift_368 := 1125853293;
  var lift_367 := true;
  var lift_366 := (lift_367, lift_368);
  var lift_365 := {
    lift_366,
    lift_369,
    lift_370,
    lift_369,
    (lift_372, lift_374)
  };
  var lift_364 := lift_365;
  var lift_363 := lift_364;
  lift_363
}

method lift_289 (arg_292 : int)
  returns (arg_293 : int)
  requires (true)
  ensures (true)
{
  arg_293 := 457967740;
  {
    var lift_312 := ();
    var lift_311 := ();
    var lift_310 := ();
    var lift_309 := [lift_310, lift_310, lift_311, lift_310, ()];
    var lift_308 := ();
    var lift_307 := lift_308;
    var lift_306 := (var tmpData : seq<()> := []; tmpData);
    var lift_305 := {
      lift_306,
      lift_306,
      [lift_307, lift_308, lift_307],
      lift_309,
      [lift_311, (), lift_307, lift_312]
    };
    var lift_304 := ();
    var lift_303 := ();
    var lift_302 := lift_303;
    var lift_301 := [lift_302];
    var lift_300 := ();
    var lift_299 := ();
    var lift_298 := [lift_299, lift_299, (), lift_300, lift_299];
    var lift_297 := lift_298;
    var lift_296 := {lift_297, lift_298, lift_301, [(), lift_304]};
    var lift_295 := 'G';
    var lift_294 := lift_295;
    lift_294 := 'k';
    print arg_292, "\n";
    print -1602207259, "\n";
    lift_296 := lift_305;
  }
}

method lift_267 ()
  returns (arg_271 : int, arg_272 : int)
  requires (true)
  ensures (true)
{
  arg_271 := -164583537;
  arg_272 := 1623344795;
  {
    var lift_275 := arg_272;
    var lift_274 := 'P';
    var lift_273 := 'U';
    lift_273 := lift_274;
    lift_275 := arg_271;
  }
}

function lift_258 (
  arg_260 : multiset<(int, char)>,
  arg_261 : (),
  arg_262 : char,
  arg_263 : bool
) : int
{
  var lift_265 := 37695965;
  var lift_264 := lift_265;
  lift_264
}

method lift_249 (arg_253 : int, arg_254 : int)
  returns (arg_255 : int, arg_256 : int)
  requires (true)
  ensures (true)
{
  arg_255 := -1453876725;
  arg_256 := -681777698;
  {
    var lift_257 := ();
    print -280522562, "\n";
    lift_257 := lift_257;
    print arg_256, "\n";
  }
}

function lift_216 () : set<()>
{
  var lift_218 := ();
  {lift_218}
}

method lift_140 (arg_143 : int)
  returns (arg_144 : int)
  requires (true)
  ensures (true)
{
  arg_144 := -564133442;
  {
    var lift_158 := '>';
    var lift_157 := true;
    var lift_156 := ((lift_157, lift_158), arg_144, (arg_143, 1413209513));
    var lift_155 := lift_156;
    var lift_154 := lift_155;
    var lift_153 := lift_154;
    var lift_152 := 1898695268;
    var lift_151 := (arg_144, lift_152);
    var lift_150 := lift_151;
    var lift_149 := '=';
    var lift_148 := false;
    var lift_147 := (lift_148, lift_149);
    var lift_146 := (lift_147, arg_144, lift_150);
    var lift_145 := -1028760420;
    print lift_145, "\n";
    lift_146 := lift_153;
    print arg_143, "\n";
  }
}

method lift_106 (arg_109 : int)
  returns (arg_110 : int)
  requires (true)
  ensures (true)
{
  arg_110 := -962656033;
  {
    var lift_112 := false;
    var lift_111 := false;
    lift_111 := lift_112;
    print arg_109, "\n";
  }
}

method lift_87 (arg_91 : int)
  returns (arg_92 : int, arg_93 : int)
  requires (true)
  ensures (true)
{
  arg_92 := -1648736445;
  arg_93 := -1331432950;
  {
    var lift_96 := ();
    var lift_95 := ();
    var lift_94 := ();
    lift_94 := lift_94;
    lift_95 := lift_96;
  }
}

method lift_65 ()
  returns (arg_68 : int)
  requires (true)
  ensures (true)
{
  arg_68 := -499276658;
  {
    var lift_70 := true;
    var lift_69 := true;
    print arg_68, "\n";
    lift_69 := lift_69;
    lift_70 := lift_70;
  }
}

method lift_50 (arg_53 : int, arg_54 : int, arg_55 : int)
  returns (arg_56 : int)
  requires (true)
  ensures (true)
{
  arg_56 := 537499400;
  {
    var lift_58 := false;
    var lift_57 := lift_58;
    print arg_56, "\n";
    print -1878918217, "\n";
    lift_57 := lift_58;
    print arg_54, "\n";
  }
}

function lift_21 (
  arg_23 : (int, int),
  arg_24 : multiset<(bool, bool, (char, bool, bool))>,
  arg_25 : int
) : int
{
  var lift_26 := 854334017;
  lift_26
}

method Main () {
  var lift_560 := ();
  var lift_559 := ();
  var lift_558 := {lift_559, lift_559, lift_560};
  var lift_557 := true;
  var lift_556 := 221950431;
  var lift_555 := (lift_556, lift_557, lift_558);
  var lift_554 := lift_555;
  var lift_553 := -1768016467;
  var lift_552 := (lift_553, lift_553);
  var lift_551 := lift_552;
  var lift_550 := false;
  var lift_549 := 'R';
  var lift_548 := 1336453517;
  var lift_547 := lift_548;
  var lift_546 := lift_547;
  var lift_545 := (lift_546, lift_549, lift_550);
  var lift_544 := (lift_545, '\'', lift_551);
  var lift_543 := lift_544.2.1;
  var lift_542 := '>';
  var lift_541 := (lift_542, lift_542);
  var lift_540 := false;
  var lift_539 := true;
  var lift_538 := lift_539;
  var lift_537 := [lift_538, lift_539, lift_540];
  var lift_534 := -300974285;
  var lift_533 := lift_534;
  var lift_532 := lift_533;
  var lift_531 := ();
  var lift_530 := (lift_531, lift_532, lift_532);
  var lift_528 := 'c';
  var lift_527 := -1494195350;
  var lift_526 := false;
  var lift_525 := (lift_526, lift_527);
  var lift_524 := -797689391;
  var lift_523 := '<';
  var lift_522 := (lift_523, lift_524);
  var lift_521 := (
    lift_522,
    [lift_524, lift_524, lift_524, lift_524],
    lift_525
  );
  var lift_514 := 1183493735;
  var lift_513 := lift_514;
  var lift_512 := {lift_513};
  var lift_511 := lift_512;
  var lift_510 := lift_511;
  var lift_509 := false;
  var lift_508 := true;
  var lift_507 := multiset{lift_508, lift_509};
  var lift_506 := (lift_507, lift_510, lift_508);
  var lift_505 := lift_506;
  var lift_502 := false;
  var lift_492 := true;
  var lift_491 := true;
  var lift_490 := lift_491;
  var lift_489 := {lift_490, lift_492};
  var lift_488 := 910630860;
  var lift_487 := false;
  var lift_486 := (lift_487, lift_488);
  var lift_475 := -1265691853;
  var lift_474 := lift_475;
  var lift_473 := "CC??;DSd|?:EDfWuprv~IH@:K<pX=u~$JBD*PAo";
  var lift_472 := lift_473;
  var lift_471 := [lift_472, "\"C!Gu|a<~Rgvk"];
  var lift_470 := (lift_471, lift_474);
  var lift_469 := -1301399904;
  var lift_468 := 't';
  var lift_467 := lift_468;
  var lift_466 := lift_467;
  var lift_465 := 1168430071;
  var lift_464 := (lift_465, 'r');
  var lift_463 := 604684537;
  var lift_462 := safeSeqSlice3Colon(
    safeSeqDrop((var tmpData : seq<char> := []; tmpData), lift_463),
    lift_464.0,
    (lift_466 as int),
    ('E', lift_469, false).1
  );
  var lift_460 := (var tmpData : seq<(int, char)> := []; tmpData);
  var lift_459 := '-';
  var lift_458 := 1393056491;
  var lift_457 := (lift_458, lift_459, -1635092057);
  var lift_456 := 239586628;
  var lift_455 := lift_456;
  var lift_454 := (-854059366, lift_455);
  var lift_453 := (lift_454, lift_457);
  var lift_452 := 'k';
  var lift_451 := 'Y';
  var lift_450 := lift_451;
  var lift_449 := multiset{lift_450, lift_452};
  var lift_446 := true;
  var lift_445 := 1244756725;
  var lift_444 := lift_445;
  var lift_443 := (lift_444, "=u/un%~T%+xTI_OXDZnBgUa><:K:/pT", lift_446);
  var lift_442 := '-';
  var lift_441 := lift_442;
  var lift_440 := {lift_441, lift_442};
  var lift_439 := false;
  var lift_438 := "<peT'ybmZw&D~RgQBCVw'BY^G:uVFvSnMPnQ:n";
  var lift_437 := false;
  var lift_436 := (lift_437, (), lift_438);
  var lift_435 := -1673459758;
  var lift_434 := '&';
  var lift_433 := lift_434;
  var lift_432 := lift_433;
  var lift_431 := multiset{lift_432, lift_434, lift_433, lift_434, lift_434};
  var lift_430 := (var tmpData : seq<(((int, bool, seq<multiset<multiset<multiset<bool>>>>, (bool, ())) -> ((multiset<char>, char, int) -> char)), ((), seq<char>, (char, string, ())))> := []; tmpData);
  var lift_429 := (
    (lift_430, lift_431, (lift_435, lift_436, {true, lift_437, lift_439})),
    (),
    lift_440
  );
  var lift_428 := '!';
  var lift_427 := lift_428;
  var lift_426 := lift_427;
  var lift_425 := false;
  var lift_424 := (lift_425, lift_425, lift_426);
  var lift_423 := ();
  var lift_422 := (lift_423, lift_424);
  var lift_421 := multiset{lift_422, lift_422};
  var lift_420 := '|';
  var lift_419 := false;
  var lift_418 := ();
  var lift_417 := (lift_418, (true, lift_419, lift_420));
  var lift_416 := 'U';
  var lift_415 := true;
  var lift_414 := (lift_415, false, lift_416);
  var lift_413 := lift_414;
  var lift_412 := ();
  var lift_411 := lift_412;
  var lift_410 := (lift_411, lift_413);
  var lift_409 := [multiset{lift_410, lift_417, lift_417}, lift_421];
  var lift_408 := (lift_409, lift_429);
  var lift_406 := ();
  var lift_405 := "N'sm?Dy^m|NusSUVqNqatgyq/;UnexW'B+b@qYi";
  var lift_404 := ('J', lift_405, lift_406);
  var lift_403 := (var tmpData : seq<char> := []; tmpData);
  var lift_402 := ();
  var lift_401 := (lift_402, lift_403, lift_404);
  var lift_389 := (lift_390, lift_401);
  var lift_388 := lift_389;
  var lift_380 := (var tmpData : set<(bool, int)> := {}; tmpData);
  var lift_379 := -1106807565;
  var lift_378 := lift_379;
  var lift_377 := 1554905960;
  var lift_376 := (lift_377, 1487575888, lift_378);
  var lift_375 := lift_376;
  var lift_355 := [true];
  var lift_351 := 'x';
  var lift_350 := '<';
  var lift_349 := (lift_350, lift_351);
  var lift_348 := {lift_349};
  var lift_347 := lift_348;
  var lift_346 := multiset{lift_347, lift_348, lift_347};
  var lift_344 := 1792743660;
  var lift_343 := [lift_344, -626018055];
  var lift_342 := 1085980867;
  var lift_341 := lift_342;
  var lift_340 := 1749217885;
  var lift_339 := (lift_340, lift_341);
  var lift_338 := true;
  var lift_337 := 370671337;
  var lift_336 := ((lift_337, lift_338, lift_338), lift_339, lift_343);
  var lift_335 := 1158851498;
  var lift_334 := -1485996507;
  var lift_333 := [lift_334, lift_335, lift_335, lift_334];
  var lift_332 := 1967557049;
  var lift_331 := -1058550714;
  var lift_330 := -1785825932;
  var lift_329 := (lift_330, lift_331);
  var lift_328 := lift_329;
  var lift_327 := lift_328;
  var lift_326 := 66241179;
  var lift_325 := lift_326;
  var lift_324 := (lift_325, true, false);
  var lift_323 := (
    lift_324,
    lift_327,
    [lift_331, 2019760233, lift_331, lift_330, lift_332]
  );
  var lift_322 := {
    lift_323,
    (lift_324, lift_327, lift_333),
    lift_323,
    lift_336
  };
  var lift_319 := false;
  var lift_318 := true;
  var lift_317 := false;
  var lift_316 := multiset{lift_317, lift_318, lift_317, lift_319, lift_319};
  var lift_314 := 'd';
  var lift_313 := lift_314;
  var lift_287 := -503715433;
  var lift_286 := lift_287;
  var lift_285 := lift_286;
  var lift_284 := lift_285;
  var lift_283 := lift_284;
  var lift_282 := 1319760945;
  var lift_281 := {lift_282, lift_282, lift_283, lift_282};
  var lift_276 := ();
  var lift_266 := (var tmpData : multiset<(int, char)> := multiset{}; tmpData);
  var lift_248 := true;
  var lift_247 := lift_248;
  var lift_246 := '/';
  var lift_245 := lift_246;
  var lift_244 := (lift_245, lift_247, lift_248);
  var lift_243 := lift_244;
  var lift_242 := true;
  var lift_241 := false;
  var lift_240 := (lift_241, lift_242, lift_243);
  var lift_239 := true;
  var lift_238 := '_';
  var lift_237 := lift_238;
  var lift_236 := true;
  var lift_235 := (lift_236, lift_236, (lift_237, lift_236, lift_239));
  var lift_234 := multiset{lift_235, lift_235, lift_235, lift_240, lift_235};
  var lift_231 := 'r';
  var lift_230 := 1258029701;
  var lift_229 := (lift_230, lift_231);
  var lift_228 := lift_229;
  var lift_227 := {(lift_228, lift_231)};
  var lift_215 := '>';
  var lift_214 := false;
  var lift_213 := true;
  var lift_212 := (lift_213, lift_214, lift_215);
  var lift_209 := 'o';
  var lift_208 := false;
  var lift_207 := (true, lift_208, lift_209);
  var lift_206 := lift_207;
  var lift_205 := ();
  var lift_204 := (lift_205, lift_206);
  var lift_203 := lift_204;
  var lift_202 := ':';
  var lift_201 := false;
  var lift_200 := false;
  var lift_199 := (lift_200, lift_201, lift_202);
  var lift_198 := ();
  var lift_197 := lift_198;
  var lift_196 := (lift_197, lift_199);
  var lift_195 := multiset{lift_196, lift_203, lift_196, lift_203};
  var lift_192 := 'L';
  var lift_191 := 1211541058;
  var lift_190 := lift_191;
  var lift_189 := 'w';
  var lift_188 := (lift_189, lift_190, lift_191);
  var lift_187 := multiset{lift_188, (lift_192, lift_191, 654593067), lift_188};
  var lift_186 := 1922970358;
  var lift_185 := "tcT+W$";
  var lift_184 := (lift_185, lift_186, lift_187);
  var lift_183 := ();
  var lift_182 := ();
  var lift_181 := lift_182;
  var lift_180 := {lift_181, lift_183, lift_181};
  var lift_179 := ();
  var lift_178 := lift_179;
  var lift_177 := ();
  var lift_176 := {lift_177, lift_177, lift_178, lift_177, lift_177};
  var lift_175 := multiset{
    lift_176,
    {lift_177, lift_177, lift_178},
    lift_176,
    (var tmpData : set<()> := {}; tmpData),
    lift_180
  };
  var lift_174 := -1160124970;
  var lift_173 := 162457689;
  var lift_172 := lift_173;
  var lift_171 := multiset{lift_172, lift_174, lift_173, lift_173};
  var lift_170 := lift_171;
  var lift_169 := false;
  var lift_168 := -883444486;
  var lift_167 := ((lift_168, lift_169), false, lift_170);
  var lift_165 := ();
  var lift_164 := {lift_165};
  var lift_138 := 'q';
  var lift_137 := lift_138;
  var lift_136 := (lift_137, lift_138);
  var lift_135 := 1189279466;
  var lift_134 := '"';
  var lift_133 := (-495949124, lift_134, lift_135);
  var lift_132 := (lift_133, lift_136);
  var lift_131 := lift_132;
  var lift_130 := multiset{lift_131, lift_132, lift_132};
  var lift_128 := 'j';
  var lift_127 := (lift_128, lift_128);
  var lift_126 := 1685165448;
  var lift_125 := 'T';
  var lift_124 := -2146099399;
  var lift_123 := (lift_124, lift_125, lift_126);
  var lift_122 := (lift_123, lift_127);
  var lift_121 := lift_122;
  var lift_120 := multiset{lift_121, (lift_123, lift_127), lift_121};
  var lift_119 := lift_120;
  var lift_117 := true;
  var lift_116 := lift_117;
  var lift_115 := lift_116;
  var lift_114 := [lift_115, lift_116];
  var lift_104 := 1044690835;
  var lift_103 := false;
  var lift_102 := 1292728354;
  var lift_101 := [lift_102];
  var lift_100 := lift_101;
  var lift_99 := (lift_100, lift_103, multiset{lift_104});
  var lift_98 := lift_99;
  var lift_97 := lift_98;
  var lift_86 := -1212967085;
  var lift_85 := true;
  var lift_84 := 1748536307;
  var lift_83 := ((lift_84, lift_85), true, lift_86);
  var lift_80 := true;
  var lift_79 := -113041689;
  var lift_78 := (lift_79, 1793926314, lift_80);
  var lift_77 := lift_78;
  var lift_76 := lift_77;
  var lift_74 := false;
  var lift_64 := false;
  var lift_63 := lift_64;
  var lift_62 := lift_63;
  var lift_61 := multiset{lift_62, lift_64, true, lift_64, lift_63};
  var lift_49 := -793094878;
  var lift_48 := true;
  var lift_47 := (lift_48, lift_49, lift_49);
  var lift_46 := ();
  var lift_45 := lift_46;
  var lift_43 := 'i';
  var lift_42 := true;
  var lift_41 := -1396049808;
  var lift_40 := (lift_41, lift_42, lift_43);
  var lift_39 := false;
  var lift_38 := 1810059537;
  var lift_37 := (lift_38, 'O', lift_39);
  var lift_36 := (lift_37, lift_40);
  var lift_35 := true;
  var lift_34 := 'X';
  var lift_33 := lift_34;
  var lift_32 := true;
  var lift_31 := (lift_32, false, (lift_33, lift_35, true));
  var lift_30 := lift_31;
  var lift_29 := lift_30;
  var lift_28 := 182103302;
  var lift_27 := (-52744090, lift_28);
  var lift_20 := '*';
  var lift_19 := 558900521;
  var lift_18 := (lift_19, lift_20, true);
  var lift_17 := lift_18;
  var lift_16 := lift_17;
  var lift_15 := lift_16;
  var lift_14 := false;
  var lift_13 := lift_14;
  var lift_12 := lift_13;
  var lift_11 := lift_12;
  var lift_10 := lift_11;
  var lift_9 := lift_10;
  var lift_8 := 'U';
  var lift_7 := lift_8;
  var lift_6 := -1403313696;
  var lift_5 := [
    (lift_6, lift_7, lift_9),
    lift_15,
    lift_16,
    (lift_6, lift_8, lift_9)
  ];
  var lift_4 := true;
  var lift_3 := lift_4;
  var lift_2 := lift_3;
  var lift_1 := true;
  if (safeSeqRef(
    ({lift_1, lift_2}, lift_5, 90380224).1,
    lift_21(lift_27, multiset{lift_29, lift_30, lift_31}, lift_19),
    lift_36.0
  ).2) {
    var lift_345 := (lift_346, lift_284);
    var lift_288 := (var tmpData : set<int> := {}; tmpData);
    var lift_279 := (lift_64, lift_13);
    var lift_278 := (lift_198, lift_279);
    var lift_233 := [lift_234, lift_234];
    var lift_232 := lift_233;
    var lift_226 := (lift_205, lift_104, lift_178);
    var lift_225 := lift_226;
    var lift_224 := (-1397893174, lift_173);
    var lift_211 := (lift_179, lift_212);
    var lift_166 := lift_167;
    var lift_139 := (-1965989143, 1259825062, lift_38);
    var lift_129 := (lift_130, (), lift_139);
    var lift_118 := -1152178663;
    var lift_60 := 'X';
    var lift_59 := {true, lift_13, lift_39, lift_12};
    var lift_44 := (lift_45, lift_47);
    if (lift_44.1.0) {
      var lift_105 := (false, lift_1);
      var lift_82 := lift_83;
      var lift_81 := multiset{lift_63, lift_42, lift_9, lift_35, true};
      var methoddefvar_52 := lift_50(lift_6, lift_19, lift_49);
      {
        lift_59 := lift_59;
        print lift_6, "\n";
        lift_60 := lift_43;
      }
      print |lift_61|, "\n";
      var methoddefvar_67 := lift_65();
      {
        var lift_75 := (lift_76, lift_81);
        var lift_73 := {lift_6, lift_49, lift_49, -497313317, lift_38};
        var lift_72 := lift_73;
        var lift_71 := [lift_72, lift_72];
        lift_71 := [lift_73, lift_73];
        lift_74 := lift_62;
        lift_75 := lift_75;
      }
      print lift_82.2, "\n";
      var methoddefvar_89, methoddefvar_90 := lift_87(-1922976023);
      {
        print lift_6, "\n";
        lift_97 := lift_97;
        print lift_79, "\n";
        lift_105 := (lift_11, lift_13);
      }
    } else {
      var lift_160 := ((lift_118, lift_79, lift_32), lift_45);
      var lift_113 := lift_114;
      var methoddefvar_108 := lift_106(lift_19);
      {
        lift_113 := lift_113;
        lift_118 := lift_86;
        print 1797570666, "\n";
      }
      print |lift_100|, "\n";
      lift_119 := lift_129.0;
      print (lift_60 as int), "\n";
      {
        var lift_210 := multiset{lift_211};
        var lift_194 := (lift_134, -979217439, lift_186);
        var lift_193 := multiset{
          lift_188,
          lift_188,
          lift_188,
          lift_188,
          lift_194
        };
        var lift_162 := ();
        var lift_161 := [(), lift_162, lift_46, lift_46];
        var lift_159 := lift_33;
        var methoddefvar_142 := lift_140(-1294638428);
        {
          lift_159 := lift_8;
          lift_160 := lift_160;
          lift_161 := lift_161;
          print lift_19, "\n";
        }
        if (lift_2) {
          var lift_163 := (lift_162, lift_164, lift_8);
          lift_163 := lift_163;
          lift_166 := lift_167;
        } else {
          lift_175 := lift_175;
          lift_184 := (lift_185, lift_86, lift_193);
          print lift_6, "\n";
          print lift_173, "\n";
          print -1172117653, "\n";
        }
        print lift_6, "\n";
        {
          lift_195 := lift_210;
          print lift_173, "\n";
        }
      }
    }
    print |lift_216()|, "\n";
    print 
      lift_21(
        ((
          arg_219 : seq<int>,
          arg_220 : bool,
          arg_221 : ((), int, ()),
          arg_222 : set<((int, char), char)>,
          arg_223 : bool
        ) => lift_224)(lift_100, true, lift_225, lift_227, false),
        safeSeqRef(lift_232, lift_172, lift_234),
        (lift_33 as int)
      ),
      "\n";
    var methoddefvar_251, methoddefvar_252 := lift_249(
      |"Kr~%>k<M?VLv%boxGkn-_~*FpXCJq/+"|,
      lift_258(lift_266, lift_178, lift_209, lift_3)
    );
    {
      var methoddefvar_269, methoddefvar_270 := lift_267();
      {
        print lift_118, "\n";
        print lift_38, "\n";
        lift_276 := lift_197;
        print lift_79, "\n";
        print lift_135, "\n";
      }
      var methoddefvar_277 := lift_65();
      {
        var lift_280 := -897126328;
        print lift_79, "\n";
        lift_278 := lift_278;
        lift_280 := methoddefvar_277;
        lift_281 := lift_288;
      }
      var methoddefvar_291 := lift_289(lift_41);
      {
        lift_313 := lift_43;
        print lift_41, "\n";
        print lift_79, "\n";
        print lift_286, "\n";
      }
      var methoddefvar_315 := lift_140(-2090614256);
      {
        lift_316 := lift_316;
        print lift_126, "\n";
      }
      var methoddefvar_320, methoddefvar_321 := lift_267();
      {
        var lift_357 := multiset{
          [lift_214, lift_35, lift_35, lift_116],
          lift_114,
          lift_114,
          lift_355,
          lift_114
        };
        var lift_356 := lift_357;
        var lift_354 := [lift_74];
        var lift_353 := multiset{lift_354, lift_355};
        var lift_352 := {lift_353, lift_353, lift_356};
        lift_322 := lift_322;
        lift_345 := lift_345;
        lift_352 := lift_352;
      }
    }
  } else {
    var lift_448 := ['a', lift_20, 'w', lift_237, lift_351];
    var lift_447 := (lift_230, lift_185, lift_236);
    var lift_407 := lift_408;
    var lift_358 := lift_359(-1085373354, lift_375);
    lift_358 := (((), lift_358).1 * (lift_358 * lift_380 * lift_358) * lift_359(
      lift_378,
      (lift_6, lift_326, -747885647)
    ));
    print 
      (
        lift_258,
        (
          (
            [
              (
                [
                  (var tmpData : multiset<((), (bool, bool, char))> := multiset{}; tmpData),
                  lift_195,
                  lift_195
                ],
                (
                  (
                    [
                      (
                        ((
                          arg_381 : int,
                          arg_382 : bool,
                          arg_383 : seq<multiset<multiset<multiset<bool>>>>,
                          arg_384 : (bool, ())
                        ) => ((
                          arg_385 : multiset<char>,
                          arg_386 : char,
                          arg_387 : int
                        ) => ';')),
                        ((), "JZP*||uHnYE+q|BYYw", ('Y', "x<", ()))
                      ),
                      lift_388
                    ],
                    multiset{'O', lift_189},
                    (
                      -433051797,
                      (true, (), "\"V&asAGJxZ%<jiSisT=QicrLnnJ?fqvWdNT"),
                      (var tmpData : set<bool> := {}; tmpData)
                    )
                  ),
                  (),
                  (var tmpData : set<char> := {}; tmpData)
                )
              ),
              lift_407
            ],
            (
              multiset{[lift_173, lift_28, lift_126]},
              (),
              (
                'm',
                multiset{
                  (2130696568, (var tmpData : string := []; tmpData), lift_318),
                  lift_443,
                  lift_447,
                  (lift_173, lift_448, false)
                }
              )
            )
          ),
          multiset{
            (var tmpData : multiset<char> := multiset{}; tmpData),
            lift_431,
            lift_431,
            multiset{lift_420},
            lift_449
          },
          (
            multiset{
              ((lift_79, lift_38), lift_133),
              (lift_339, lift_123),
              lift_453
            },
            (
              'j',
              (
                (() => 572213210),
                multiset{
                  multiset{lift_318, lift_12, lift_425, lift_439, lift_80}
                }
              )
            ),
            multiset{lift_411, lift_182, lift_197}
          )
        )
      ).0(
        multiset(lift_460),
        (),
        ("VRGfW~/<VD/vwwVz<BdL+-LCifpctx$qR%", 'u', ()).1,
        (lift_317 || lift_236)
      ),
      "\n";
    print lift_47.1, "\n";
    var methoddefvar_461 := lift_65();
    {
      print lift_124, "\n";
    }
  }
  lift_462 := safeSeqTake(
    lift_470.0,
    ((lift_195[lift_204 := lengthNormalize(lift_377)])[lift_476(
      lift_486,
      lift_489,
      lift_238
    )] as int)
  );
  var methoddefvar_493, methoddefvar_494 := lift_267();
  {
    var lift_536 := lift_355;
    var lift_535 := (lift_165, 1245409671, lift_341);
    var lift_518 := ["z^Rj~tMead+_Ss/x=GTu^", lift_403];
    var lift_504 := lift_61;
    var lift_503 := (
      lift_504,
      {lift_126, 761178365, lift_102, lift_475},
      false
    );
    print safeSeqRef(lift_333, 1693048011, lift_84), "\n";
    {
      var lift_501 := lift_168;
      var methoddefvar_497 := lift_495(lift_455, lift_174);
      {
        lift_501 := lift_474;
      }
      print lift_475, "\n";
    }
    if ((lift_419 && true)) {
      {
        lift_502 := lift_116;
        print lift_458, "\n";
        print lift_341, "\n";
        lift_503 := lift_505;
        print lift_455, "\n";
      }
      if (lift_487) {
        print lift_190, "\n";
        print lift_84, "\n";
      } else {
        print methoddefvar_493, "\n";
      }
      var methoddefvar_515 := lift_289(lift_284);
      {
        print lift_173, "\n";
        print lift_488, "\n";
        print lift_79, "\n";
        print lift_331, "\n";
      }
      var methoddefvar_516 := lift_495(lift_19, lift_488);
      {
        var lift_517 := {lift_468, lift_314};
        lift_517 := lift_517;
        print lift_287, "\n";
        print lift_474, "\n";
        print lift_456, "\n";
        print lift_282, "\n";
      }
      lift_518 := lift_518;
    } else {
      var methoddefvar_519 := lift_50(lift_38, 606774161, lift_334);
      {
        var lift_520 := lift_318;
        print lift_173, "\n";
        lift_520 := lift_201;
      }
      if (lift_85) {
        lift_521 := lift_521;
        print lift_284, "\n";
      } else {
        lift_528 := lift_245;
      }
    }
    var methoddefvar_529 := lift_495(lift_326, lift_282);
    {
      lift_530 := lift_535;
      lift_536 := lift_537;
    }
    lift_541 := lift_541;
  }
  lift_543 := |(lift_554.2 * (
    false,
    multiset{lift_411},
    lift_558
  ).2 * safeSeqRef([lift_180], lift_533, lift_558))|;
}


