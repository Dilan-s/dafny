// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Seed: 1623337200
// This is a RANDOMLY GENERATED PROGRAM.
// Fuzzer: dafny
// Version: dafny, xsmith 2.0.5 (38f1d83), in Racket 8.6 (vm-type chez-scheme)
// Options: --with-print-constrained true --timeout 300 --dafny-syntax true
// Seed: 1623337200
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
method lift_645 (arg_649 : int)
  returns (arg_650 : int, arg_651 : int)
  requires (true)
  ensures (true)
{
  arg_650 := -1882852884;
  arg_651 := -1944827628;
  {
    var lift_653 := multiset{arg_650};
    var lift_652 := multiset{arg_651};
    lift_652 := lift_653;
  }
}

method lift_605 (arg_608 : int, arg_609 : int)
  returns (arg_610 : int)
  requires (true)
  ensures (true)
{
  arg_610 := -27788400;
  {
    var lift_640 := '&';
    var lift_639 := lift_640;
    var lift_638 := true;
    var lift_637 := 'D';
    var lift_636 := true;
    var lift_635 := (lift_636, lift_637, false);
    var lift_634 := false;
    var lift_633 := (lift_634, lift_635);
    var lift_632 := lift_633;
    var lift_631 := multiset{lift_632};
    var lift_630 := false;
    var lift_629 := ('f', lift_630, lift_630);
    var lift_628 := (lift_629, lift_631);
    var lift_627 := 'T';
    var lift_626 := false;
    var lift_625 := (lift_626, lift_627, lift_626);
    var lift_624 := lift_625;
    var lift_623 := (false, lift_624);
    var lift_622 := lift_623;
    var lift_621 := multiset{lift_622, lift_623, lift_622};
    var lift_620 := lift_621;
    var lift_619 := lift_620;
    var lift_618 := true;
    var lift_617 := lift_618;
    var lift_616 := lift_617;
    var lift_615 := lift_616;
    var lift_614 := ('P', true, lift_615);
    var lift_613 := lift_614;
    var lift_612 := (lift_613, lift_619);
    var lift_611 := lift_612;
    lift_611 := lift_628;
    lift_638 := true;
    print arg_610, "\n";
    print arg_610, "\n";
    lift_639 := lift_639;
  }
}

method lift_563 (arg_566 : int)
  returns (arg_567 : int)
  requires (true)
  ensures (true)
{
  arg_567 := -1989868219;
  {
    var lift_591 := '&';
    var lift_590 := 'T';
    var lift_589 := 'G';
    var lift_588 := {'E', lift_589, lift_590, lift_591, lift_590};
    var lift_587 := lift_588;
    var lift_586 := multiset{lift_587, lift_587, lift_587, lift_588, lift_587};
    var lift_585 := lift_586;
    var lift_584 := lift_585;
    var lift_583 := '?';
    var lift_582 := lift_583;
    var lift_581 := {lift_582, lift_583};
    var lift_580 := lift_581;
    var lift_579 := 'q';
    var lift_578 := lift_579;
    var lift_577 := 'i';
    var lift_576 := {lift_577, 'z', 'r'};
    var lift_575 := multiset{
      lift_576,
      {lift_578, lift_578, lift_577},
      lift_576,
      lift_580,
      lift_581
    };
    var lift_574 := ();
    var lift_573 := arg_567;
    var lift_572 := [lift_573];
    var lift_571 := {arg_567, arg_567, -67099989, arg_567, arg_567};
    var lift_570 := lift_571;
    var lift_569 := [2068697129, -200420204, arg_566, arg_566, 2116395930];
    var lift_568 := (lift_569, {arg_567}, lift_569);
    lift_568 := (lift_569, lift_570, lift_572);
    lift_574 := lift_574;
    lift_575 := lift_584;
    print lift_573, "\n";
  }
}

function lift_517 (
  arg_519 : multiset<()>,
  arg_520 : char,
  arg_521 : (char, bool),
  arg_522 : (int, bool, bool)
) : multiset<string>
{
  var lift_523 := (var tmpData : multiset<string> := multiset{}; tmpData);
  lift_523
}

method lift_468 ()
  returns (arg_472 : int, arg_473 : int)
  requires (true)
  ensures (true)
{
  arg_472 := 957337587;
  arg_473 := 160402250;
  {
    print arg_473, "\n";
  }
}

function lift_407 (
  arg_409 : (char, char),
  arg_410 : multiset<()>
) : ((), multiset<(multiset<char>, (char, char))>, set<()>)
{
  var lift_413 := (var tmpData : set<()> := {}; tmpData);
  var lift_412 := (var tmpData : multiset<(multiset<char>, (char, char))> := multiset{}; tmpData);
  var lift_411 := ();
  (lift_411, lift_412, lift_413)
}

method lift_349 ()
  returns (arg_353 : int, arg_354 : int)
  requires (true)
  ensures (true)
{
  arg_353 := 1858899402;
  arg_354 := 1270089761;
  {
    var lift_360 := 'X';
    var lift_359 := lift_360;
    var lift_358 := lift_359;
    var lift_357 := lift_358;
    var lift_356 := 'c';
    var lift_355 := multiset{lift_356, lift_357, lift_357, 'd'};
    lift_355 := lift_355;
  }
}

method lift_308 ()
  returns (arg_311 : int)
  requires (true)
  ensures (true)
{
  arg_311 := 228948369;
  {
    var lift_319 := false;
    var lift_318 := lift_319;
    var lift_317 := (arg_311, lift_318);
    var lift_316 := lift_317;
    var lift_315 := true;
    var lift_314 := (14221765, lift_315);
    var lift_313 := 688949316;
    var lift_312 := 1384591253;
    print arg_311, "\n";
    lift_312 := lift_312;
    print lift_313, "\n";
    lift_314 := lift_316;
  }
}

method lift_281 (arg_285 : int)
  returns (arg_286 : int, arg_287 : int)
  requires (true)
  ensures (true)
{
  arg_286 := 558287847;
  arg_287 := 1658479750;
  {
    var lift_306 := '_';
    var lift_305 := 'Y';
    var lift_304 := multiset{lift_305, lift_306, lift_306, lift_306, lift_306};
    var lift_303 := lift_304;
    var lift_302 := 'z';
    var lift_301 := (arg_286, arg_286, true);
    var lift_300 := ((arg_286, arg_287, 'N'), lift_301, lift_302);
    var lift_299 := 'O';
    var lift_298 := false;
    var lift_297 := lift_298;
    var lift_296 := (arg_287, arg_286, lift_297);
    var lift_295 := 'T';
    var lift_294 := lift_295;
    var lift_293 := ((arg_286, 136646028, lift_294), lift_296, lift_299);
    var lift_292 := "Athn%tz>:R@z\"-U:;vB&mlKImvh^y=x<_@<";
    var lift_291 := '<';
    var lift_290 := 'k';
    var lift_289 := [lift_290, lift_291, 'j'];
    var lift_288 := (56727590, 'F', lift_289);
    lift_288 := (arg_285, lift_291, lift_292);
    lift_293 := lift_300;
    lift_303 := lift_304;
  }
}

method lift_248 (arg_251 : int)
  returns (arg_252 : int)
  requires (true)
  ensures (true)
{
  arg_252 := -2045651301;
  {
    var lift_264 := ();
    var lift_263 := ();
    var lift_262 := {lift_263, lift_263, lift_264};
    var lift_261 := lift_262;
    var lift_260 := '$';
    var lift_259 := true;
    var lift_258 := lift_259;
    var lift_257 := lift_258;
    var lift_256 := (lift_257, lift_260, arg_251);
    var lift_255 := ('d', arg_251);
    var lift_254 := (lift_255, lift_256);
    var lift_253 := ();
    lift_253 := lift_253;
    print arg_252, "\n";
    lift_254 := lift_254;
    lift_261 := lift_261;
  }
}

method lift_235 (arg_238 : int, arg_239 : int)
  returns (arg_240 : int)
  requires (true)
  ensures (true)
{
  arg_240 := -1830979060;
  {
    var lift_244 := 'G';
    var lift_243 := 'F';
    var lift_242 := arg_239;
    var lift_241 := -881438665;
    print lift_241, "\n";
    print lift_242, "\n";
    print lift_242, "\n";
    lift_243 := lift_244;
  }
}

method lift_149 (arg_152 : int)
  returns (arg_153 : int)
  requires (true)
  ensures (true)
{
  arg_153 := 615938016;
  {
    var lift_154 := ();
    lift_154 := lift_154;
    print 1086944362, "\n";
  }
}

method lift_141 ()
  returns (arg_144 : int)
  requires (true)
  ensures (true)
{
  arg_144 := 1044476650;
  {
    var lift_147 := (var tmpData : multiset<seq<char>> := multiset{}; tmpData);
    var lift_146 := arg_144;
    var lift_145 := lift_146;
    lift_145 := lift_146;
    print lift_146, "\n";
    print arg_144, "\n";
    lift_147 := lift_147;
    print arg_144, "\n";
  }
}

method lift_104 (arg_108 : int, arg_109 : int)
  returns (arg_110 : int, arg_111 : int)
  requires (true)
  ensures (true)
{
  arg_110 := -1515326527;
  arg_111 := -1175645455;
  {
    var lift_136 := 'e';
    var lift_135 := lift_136;
    var lift_134 := (lift_135, 'M');
    var lift_133 := ();
    var lift_132 := '-';
    var lift_131 := lift_132;
    var lift_130 := multiset{lift_131, '_', 'W', lift_131, lift_132};
    var lift_129 := (lift_130, lift_133, lift_134);
    var lift_128 := lift_129;
    var lift_127 := multiset{lift_128};
    var lift_126 := true;
    var lift_125 := false;
    var lift_124 := '<';
    var lift_123 := (lift_124, lift_124);
    var lift_122 := ();
    var lift_121 := 'l';
    var lift_120 := lift_121;
    var lift_119 := lift_120;
    var lift_118 := multiset{lift_119, 't', lift_121, lift_119};
    var lift_117 := lift_118;
    var lift_116 := (lift_117, lift_122, lift_123);
    var lift_115 := multiset{lift_116};
    var lift_114 := true;
    var lift_113 := [lift_114, lift_114];
    var lift_112 := (lift_113, lift_115, lift_125);
    lift_112 := ([lift_126, lift_114, lift_126], lift_127, lift_126);
    print arg_111, "\n";
    print -1592363897, "\n";
  }
}

method lift_56 ()
  returns (arg_60 : int, arg_61 : int)
  requires (true)
  ensures (true)
{
  arg_60 := -1724492823;
  arg_61 := 948084177;
  {
    var lift_63 := ();
    var lift_62 := ();
    print arg_60, "\n";
    lift_62 := lift_63;
  }
}

method lift_1 (arg_5 : int, arg_6 : int, arg_7 : int)
  returns (arg_8 : int, arg_9 : int)
  requires (true)
  ensures (true)
{
  arg_8 := 1329751087;
  arg_9 := 1601057590;
  {
    var lift_16 := (true, arg_9);
    var lift_15 := false;
    var lift_14 := (lift_15, arg_7);
    var lift_13 := ((), arg_5);
    var lift_12 := ();
    var lift_11 := lift_12;
    var lift_10 := (lift_11, arg_5);
    lift_10 := lift_13;
    print arg_7, "\n";
    lift_14 := lift_16;
  }
}

method Main () {
  var lift_664 := ();
  var lift_663 := lift_664;
  var lift_662 := multiset{lift_663, (), lift_664, (), lift_663};
  var lift_661 := (var tmpData : set<bool> := {}; tmpData);
  var lift_660 := (lift_661, lift_662);
  var lift_657 := ();
  var lift_654 := '@';
  var lift_602 := -941803781;
  var lift_600 := false;
  var lift_599 := lift_600;
  var lift_598 := -546443123;
  var lift_597 := lift_598;
  var lift_596 := (lift_597, lift_599);
  var lift_595 := 'n';
  var lift_594 := (
    lift_595,
    (var tmpData : seq<bool> := []; tmpData),
    lift_596
  );
  var lift_593 := lift_594;
  var lift_561 := 'C';
  var lift_560 := lift_561;
  var lift_559 := multiset{lift_560, lift_561};
  var lift_558 := lift_559;
  var lift_557 := 'E';
  var lift_556 := 'C';
  var lift_555 := [
    multiset{lift_556, lift_557, lift_556, lift_557, lift_556},
    lift_558,
    multiset{lift_561, lift_556, lift_561, lift_561},
    lift_559
  ];
  var lift_553 := 'o';
  var lift_552 := false;
  var lift_551 := (lift_552, lift_553);
  var lift_550 := true;
  var lift_549 := true;
  var lift_548 := [lift_549, lift_549, lift_549, lift_550];
  var lift_547 := lift_548;
  var lift_546 := (lift_547, lift_551);
  var lift_544 := '^';
  var lift_543 := false;
  var lift_542 := lift_543;
  var lift_541 := (lift_542, lift_544);
  var lift_534 := true;
  var lift_533 := (true, lift_534);
  var lift_528 := true;
  var lift_527 := lift_528;
  var lift_526 := 400838686;
  var lift_525 := lift_526;
  var lift_524 := (lift_525, lift_527, false);
  var lift_516 := 'X';
  var lift_515 := lift_516;
  var lift_514 := true;
  var lift_513 := lift_514;
  var lift_512 := {lift_513, lift_514, lift_513, lift_514};
  var lift_511 := lift_512;
  var lift_510 := (lift_511, lift_515);
  var lift_509 := false;
  var lift_508 := {lift_509, lift_509};
  var lift_507 := (lift_508, 'd');
  var lift_506 := '!';
  var lift_505 := false;
  var lift_504 := {lift_505};
  var lift_503 := (lift_504, lift_506);
  var lift_502 := '\'';
  var lift_501 := lift_502;
  var lift_500 := false;
  var lift_499 := true;
  var lift_498 := false;
  var lift_497 := {lift_498, lift_498, lift_499, lift_500, false};
  var lift_496 := {
    (lift_497, lift_501),
    lift_503,
    lift_507,
    lift_507,
    lift_510
  };
  var lift_491 := '@';
  var lift_490 := 'l';
  var lift_489 := (lift_490, lift_491);
  var lift_488 := false;
  var lift_487 := multiset{lift_488, true};
  var lift_486 := -690043881;
  var lift_485 := (var tmpData : set<multiset<int>> := {}; tmpData);
  var lift_484 := (lift_485, lift_486, (lift_487, lift_489));
  var lift_483 := lift_484.2;
  var lift_482 := false;
  var lift_481 := true;
  var lift_480 := [lift_481, false, lift_481, lift_481, lift_482];
  var lift_479 := -1162870272;
  var lift_478 := -1181069246;
  var lift_477 := (lift_478, -1818502962);
  var lift_476 := lift_477;
  var lift_475 := (lift_476, (-937578422, lift_479, lift_480));
  var lift_467 := 2016939266;
  var lift_466 := lift_467;
  var lift_465 := 'd';
  var lift_464 := (lift_465, lift_466, lift_465);
  var lift_462 := -1736218409;
  var lift_461 := ('J', lift_462, 'R');
  var lift_460 := 's';
  var lift_459 := ((lift_460, lift_460), lift_461, lift_462);
  var lift_458 := 1542104908;
  var lift_457 := lift_458;
  var lift_456 := 'T';
  var lift_455 := (lift_456, lift_457, lift_456);
  var lift_449 := false;
  var lift_448 := lift_449;
  var lift_447 := 'P';
  var lift_446 := (lift_447, lift_448);
  var lift_445 := false;
  var lift_444 := ';';
  var lift_443 := (lift_444, lift_445);
  var lift_442 := lift_443;
  var lift_441 := 'E';
  var lift_440 := lift_441;
  var lift_439 := (lift_440, true);
  var lift_438 := {lift_439, lift_442, lift_446, lift_442};
  var lift_437 := ();
  var lift_436 := multiset{lift_437, lift_437, lift_437};
  var lift_435 := '\'';
  var lift_434 := lift_435;
  var lift_433 := lift_434;
  var lift_432 := (lift_433, lift_434, lift_436);
  var lift_429 := 'u';
  var lift_428 := ('"', lift_429);
  var lift_427 := 59065108;
  var lift_426 := true;
  var lift_425 := (lift_426, '!', lift_427);
  var lift_424 := false;
  var lift_423 := lift_424;
  var lift_422 := {lift_423, lift_424};
  var lift_421 := (lift_422, lift_425);
  var lift_420 := 'A';
  var lift_419 := (false, lift_420, 1526380408);
  var lift_418 := (var tmpData : set<bool> := {}; tmpData);
  var lift_417 := (lift_418, lift_419);
  var lift_416 := {lift_417, lift_421};
  var lift_415 := (var tmpData : set<set<char>> := {}; tmpData);
  var lift_414 := (lift_415, lift_416, lift_428);
  var lift_406 := (var tmpData : set<()> := {}; tmpData);
  var lift_405 := '*';
  var lift_404 := '"';
  var lift_403 := (lift_404, lift_405);
  var lift_402 := lift_403;
  var lift_401 := lift_402;
  var lift_400 := '>';
  var lift_399 := multiset{'X', lift_400};
  var lift_398 := (lift_399, lift_401);
  var lift_397 := ';';
  var lift_396 := lift_397;
  var lift_395 := (lift_396, lift_396);
  var lift_394 := lift_395;
  var lift_393 := 'e';
  var lift_392 := lift_393;
  var lift_391 := multiset{lift_392, lift_393};
  var lift_390 := (lift_391, lift_394);
  var lift_389 := ();
  var lift_388 := (lift_389, multiset{lift_390, lift_390, lift_398}, lift_406);
  var lift_387 := lift_388;
  var lift_386 := [lift_387];
  var lift_385 := lift_386;
  var lift_381 := false;
  var lift_380 := -2110998681;
  var lift_379 := false;
  var lift_378 := (lift_379, lift_380);
  var lift_377 := 'L';
  var lift_376 := (lift_377, lift_378, lift_381);
  var lift_371 := 1882776402;
  var lift_370 := -796876201;
  var lift_369 := (lift_370, lift_371);
  var lift_348 := false;
  var lift_346 := -88701428;
  var lift_345 := (lift_346, -1323922375, -185238549);
  var lift_344 := 1953491336;
  var lift_343 := lift_344;
  var lift_342 := lift_343;
  var lift_341 := false;
  var lift_340 := lift_341;
  var lift_339 := (lift_340, lift_342);
  var lift_338 := (lift_339, lift_345);
  var lift_335 := -820734445;
  var lift_334 := -328421958;
  var lift_333 := lift_334;
  var lift_332 := (lift_333, lift_334, lift_335);
  var lift_331 := false;
  var lift_330 := lift_331;
  var lift_329 := (lift_330, 1191985704);
  var lift_328 := (lift_329, lift_332);
  var lift_327 := -1130311173;
  var lift_326 := lift_327;
  var lift_325 := lift_326;
  var lift_324 := lift_325;
  var lift_323 := (lift_324, lift_327, -1911072083);
  var lift_322 := lift_323;
  var lift_276 := -2085702830;
  var lift_275 := 2071059576;
  var lift_274 := true;
  var lift_273 := (lift_274, lift_275, lift_276);
  var lift_272 := lift_273;
  var lift_271 := 1946672460;
  var lift_270 := true;
  var lift_269 := (lift_270, lift_271, lift_271);
  var lift_268 := lift_269;
  var lift_267 := (var tmpData : seq<bool> := []; tmpData);
  var lift_266 := (lift_267, lift_268);
  var lift_247 := ();
  var lift_234 := true;
  var lift_233 := 1856566576;
  var lift_232 := 'R';
  var lift_231 := 321882843;
  var lift_230 := lift_231;
  var lift_229 := '&';
  var lift_228 := (lift_229, lift_230);
  var lift_227 := true;
  var lift_226 := ('=', lift_227);
  var lift_225 := lift_226;
  var lift_224 := (lift_225, '$', lift_228);
  var lift_223 := (
    {lift_224, (lift_226, lift_229, (lift_232, lift_233))},
    lift_227
  );
  var lift_222 := lift_223;
  var lift_217 := -1875793327;
  var lift_216 := lift_217;
  var lift_215 := ('D', lift_216);
  var lift_214 := lift_215;
  var lift_212 := true;
  var lift_211 := '~';
  var lift_210 := (lift_211, lift_212);
  var lift_205 := '_';
  var lift_204 := ();
  var lift_203 := -508619643;
  var lift_202 := [lift_203, 1387282739, lift_203, -17411237];
  var lift_201 := (lift_202, lift_204, lift_205);
  var lift_200 := lift_201;
  var lift_197 := false;
  var lift_196 := [true, lift_197, lift_197];
  var lift_195 := true;
  var lift_194 := 812809443;
  var lift_193 := (lift_194, 'I', lift_195);
  var lift_192 := -680779301;
  var lift_191 := '@';
  var lift_190 := lift_191;
  var lift_189 := ((lift_190, true, lift_192), lift_193, lift_196);
  var lift_188 := true;
  var lift_187 := false;
  var lift_186 := lift_187;
  var lift_185 := [lift_186, lift_188, lift_188];
  var lift_184 := false;
  var lift_183 := 'g';
  var lift_182 := 1224244042;
  var lift_181 := (lift_182, lift_183, lift_184);
  var lift_180 := 1709185592;
  var lift_179 := lift_180;
  var lift_178 := false;
  var lift_177 := ('U', lift_178, lift_179);
  var lift_176 := (lift_177, lift_181, lift_185);
  var lift_175 := {lift_176, lift_189, lift_176, lift_189};
  var lift_174 := false;
  var lift_173 := 'T';
  var lift_172 := false;
  var lift_171 := (lift_172, lift_173, lift_174);
  var lift_170 := lift_171;
  var lift_169 := (var tmpData : set<bool> := {}; tmpData);
  var lift_166 := 'V';
  var lift_165 := true;
  var lift_164 := lift_165;
  var lift_163 := (lift_164, lift_166, false);
  var lift_162 := false;
  var lift_161 := true;
  var lift_160 := {lift_161, lift_162};
  var lift_159 := (lift_160, (), lift_163);
  var lift_140 := 'd';
  var lift_139 := lift_140;
  var lift_103 := ();
  var lift_102 := lift_103;
  var lift_101 := [lift_102];
  var lift_100 := lift_101;
  var lift_99 := lift_100;
  var lift_98 := ();
  var lift_97 := lift_98;
  var lift_93 := true;
  var lift_92 := '\'';
  var lift_91 := 1962479111;
  var lift_90 := (lift_91, lift_92, lift_93);
  var lift_89 := lift_90;
  var lift_88 := -1010478782;
  var lift_87 := 'X';
  var lift_86 := lift_87;
  var lift_85 := lift_86;
  var lift_84 := lift_85;
  var lift_83 := lift_84;
  var lift_82 := lift_83;
  var lift_81 := (lift_82, true, lift_88);
  var lift_80 := lift_81;
  var lift_79 := true;
  var lift_78 := true;
  var lift_77 := [lift_78, lift_78, lift_79];
  var lift_76 := lift_77;
  var lift_75 := false;
  var lift_74 := '&';
  var lift_73 := -1224210742;
  var lift_72 := (lift_73, lift_74, lift_75);
  var lift_71 := -698658255;
  var lift_70 := lift_71;
  var lift_69 := lift_70;
  var lift_68 := lift_69;
  var lift_67 := true;
  var lift_66 := ('$', lift_67, lift_68);
  var lift_65 := (lift_66, lift_72, lift_76);
  var lift_64 := {lift_65, lift_65, (lift_80, lift_89, [lift_67])};
  var lift_54 := true;
  var lift_53 := lift_54;
  var lift_52 := lift_53;
  var lift_51 := (var tmpData : seq<bool> := []; tmpData);
  var lift_50 := 1132637547;
  var lift_49 := lift_50;
  var lift_48 := (lift_49, lift_51, lift_52);
  var lift_46 := -1478376610;
  var lift_45 := lift_46;
  var lift_44 := 'S';
  var lift_43 := (lift_44, lift_44, lift_45);
  var lift_42 := lift_43;
  var lift_41 := "qT&;V/\"oTSF";
  var lift_40 := (lift_41, lift_42);
  var lift_39 := 'H';
  var lift_38 := {lift_39};
  var lift_37 := false;
  var lift_36 := -154464950;
  var lift_35 := true;
  var lift_34 := (lift_35, lift_36);
  var lift_33 := (lift_34, lift_37, lift_38);
  var lift_32 := lift_33;
  var lift_31 := 'z';
  var lift_30 := 'y';
  var lift_29 := '/';
  var lift_28 := lift_29;
  var lift_27 := lift_28;
  var lift_26 := multiset{
    {lift_27, lift_28, lift_30},
    {lift_29, lift_30, lift_27, lift_30, lift_31}
  };
  var lift_25 := 'B';
  var lift_24 := lift_25;
  var lift_23 := 1297973882;
  var lift_22 := lift_23;
  var lift_21 := (lift_22, [lift_24], 650674313);
  var lift_20 := -1308768273;
  var lift_19 := lift_20;
  var lift_18 := {lift_19, lift_19};
  var lift_17 := -1375036934;
  var methoddefvar_3, methoddefvar_4 := lift_1(
    safeSeqRef(
      [1870629457, lift_17, 1469735523, lift_17],
      |lift_18|,
      lift_21.2
    ),
    (lift_26[lift_32.2] as int),
    lift_40.1.2
  );
  {
    var lift_265 := lift_266;
    var lift_246 := -1589886597;
    var lift_245 := ();
    var lift_221 := (lift_139, lift_54);
    var lift_220 := (lift_221, lift_24, lift_215);
    var lift_219 := (lift_205, lift_35);
    var lift_218 := (lift_219, '~', lift_214);
    var lift_209 := (lift_83, lift_194);
    var lift_168 := {lift_75, lift_37, lift_165};
    var lift_167 := (lift_168, lift_103, lift_163);
    var lift_158 := multiset{lift_159, lift_167, (lift_169, (), lift_170)};
    var lift_157 := lift_158;
    var lift_156 := (-101213419, lift_75, lift_37);
    var lift_155 := (lift_156, lift_73, lift_157);
    var lift_137 := {false};
    var lift_96 := lift_97;
    var lift_95 := [lift_96, (), lift_98, lift_96];
    var lift_47 := lift_48;
    if (lift_47.2) {
      var lift_94 := lift_95;
      var lift_55 := false;
      lift_55 := lift_35;
      var methoddefvar_58, methoddefvar_59 := lift_56();
      {
        lift_64 := (var tmpData : set<((char, bool, int), (int, char, bool), seq<bool>)> := {}; tmpData);
        print lift_23, "\n";
        lift_94 := lift_99;
      }
      var methoddefvar_106, methoddefvar_107 := lift_104(lift_46, lift_50);
      {
        var lift_138 := {lift_67};
        lift_137 := lift_138;
        print methoddefvar_3, "\n";
        print 601396746, "\n";
        print methoddefvar_107, "\n";
      }
      lift_139 := lift_29;
    } else {
      var lift_148 := true;
      var methoddefvar_143 := lift_141();
      {
        print lift_17, "\n";
        lift_148 := lift_78;
        print methoddefvar_4, "\n";
        print lift_91, "\n";
        print lift_69, "\n";
      }
      var methoddefvar_151 := lift_149(lift_91);
      {
        print -1661855421, "\n";
        print lift_45, "\n";
        print lift_69, "\n";
      }
      lift_155 := lift_155;
    }
    if ((lift_64 > lift_175)) {
      print lift_70, "\n";
    } else {
      var lift_208 := ((lift_25, true), lift_29, lift_209);
      var methoddefvar_198, methoddefvar_199 := lift_56();
      {
        var lift_213 := lift_214;
        var lift_207 := {
          lift_208,
          (lift_210, lift_83, lift_213),
          lift_218,
          lift_220
        };
        var lift_206 := (lift_207, lift_195);
        lift_200 := lift_201;
        lift_206 := lift_222;
        lift_234 := false;
        print lift_17, "\n";
        print lift_230, "\n";
      }
      var methoddefvar_237 := lift_235(lift_231, lift_71);
      {
        print -2053163443, "\n";
        lift_245 := lift_97;
      }
      {
        lift_246 := lift_179;
      }
      lift_247 := lift_96;
      var methoddefvar_250 := lift_248(lift_179);
      {
        var lift_278 := ":>oEBJKXJS&_H^\"$bPP!W^<=kyq!Lm";
        var lift_277 := (lift_49, lift_41, lift_85);
        lift_265 := (lift_267, lift_272);
        lift_277 := (lift_45, lift_278, lift_39);
      }
    }
    print |lift_168|, "\n";
  }
  {
    var lift_454 := (lift_428, lift_455, lift_216);
    var lift_431 := lift_432;
    var lift_430 := lift_431;
    var lift_384 := lift_385;
    var lift_383 := safeSeqRef(lift_384, lift_19, lift_387);
    var lift_382 := false;
    var lift_362 := {lift_97, lift_97, lift_247, ()};
    var lift_361 := (var tmpData : set<()> := {}; tmpData);
    var lift_347 := [lift_188];
    var lift_336 := lift_328;
    var lift_321 := (lift_195, -591790159);
    var lift_320 := {
      (lift_34, (lift_70, lift_194, lift_233)),
      (lift_321, lift_322),
      lift_328,
      lift_336,
      lift_336
    };
    var lift_307 := false;
    var lift_280 := [
      lift_76,
      lift_267,
      [lift_184, lift_172],
      lift_196,
      lift_77
    ];
    var lift_279 := lift_280;
    if (safeSeqRef(
      safeSeqRef(lift_279, lift_20, lift_267),
      (-2122745768, 'b', 1054912697).2,
      (lift_161 <== lift_274)
    )) {
      var lift_363 := ();
      var lift_337 := (lift_329, lift_332);
      var methoddefvar_283, methoddefvar_284 := lift_281(lift_20);
      {
        lift_307 := lift_164;
      }
      print safeSeqRef(lift_202, lift_182, lift_179), "\n";
      {
        var methoddefvar_310 := lift_308();
        {
          lift_320 := {lift_337, lift_338};
          lift_347 := (var tmpData : seq<bool> := []; tmpData);
          lift_348 := lift_195;
          print lift_49, "\n";
          print lift_230, "\n";
        }
        var methoddefvar_351, methoddefvar_352 := lift_349();
        {
          lift_361 := lift_362;
          print lift_73, "\n";
          lift_363 := lift_97;
          print lift_91, "\n";
        }
        {
          var lift_364 := '/';
          lift_364 := lift_82;
          print lift_182, "\n";
          print lift_70, "\n";
        }
        print lift_91, "\n";
        if (lift_270) {
          print lift_271, "\n";
          print lift_230, "\n";
          print lift_73, "\n";
        } else {
          print lift_346, "\n";
          print lift_73, "\n";
          print lift_88, "\n";
        }
      }
    } else {
      var lift_375 := ('!', (lift_79, -470290187), lift_93);
      var lift_374 := ();
      var lift_373 := ();
      var lift_368 := multiset{(lift_91, lift_325), lift_369};
      var lift_365 := 'a';
      lift_365 := lift_90.1;
      var methoddefvar_366, methoddefvar_367 := lift_349();
      {
        lift_368 := (var tmpData : multiset<(int, int)> := multiset{}; tmpData);
      }
      var methoddefvar_372 := lift_235(lift_73, lift_73);
      {
        lift_373 := lift_374;
        lift_375 := lift_376;
        print lift_179, "\n";
        lift_382 := lift_187;
      }
    }
    lift_383 := lift_407(lift_414.2, lift_430.2);
    {
      var lift_463 := lift_459;
      var lift_453 := {lift_454, lift_459, lift_454, lift_463, lift_459};
      var lift_452 := [(), lift_102, lift_204, lift_204];
      var lift_451 := (lift_399, lift_361);
      print lift_322.0, "\n";
      if (lift_223.1) {
        var lift_450 := {('-', lift_445)};
        {
          lift_438 := lift_450;
          lift_451 := lift_451;
          lift_452 := [lift_102, lift_437, (), lift_98, ()];
        }
      } else {
        {
          print 1573893499, "\n";
          print 918974095, "\n";
          print lift_230, "\n";
        }
        lift_453 := {
          (lift_402, lift_464, lift_334),
          (lift_394, lift_455, lift_335),
          lift_459
        };
      }
    }
  }
  var methoddefvar_470, methoddefvar_471 := lift_468();
  {
    var lift_474 := -409093381;
    lift_474 := (multiset{[(), lift_97], [lift_389]}[lift_99] as int);
  }
  if ((((lift_53 || lift_270) ==> (lift_203 > lift_192)) in lift_475.1.2)) {
    lift_483 := lift_483;
  } else {
    var lift_643 := {
      [
        {lift_449, lift_499, true},
        lift_508,
        {true, lift_552, lift_445, lift_162},
        lift_508,
        lift_160
      ]
    };
    var lift_592 := lift_593;
    var lift_545 := lift_546;
    var lift_540 := lift_541;
    var lift_539 := (lift_77, lift_540);
    var lift_536 := {lift_191, lift_166, lift_392, lift_433, '|'};
    print (lift_210.0 as int), "\n";
    print (lift_404 as int), "\n";
    if ((((
      arg_492 : bool,
      arg_493 : set<(set<bool>, char)>,
      arg_494 : (),
      arg_495 : int
    ) => "$q")(lift_341, lift_496, lift_389, -1232009888) in lift_517(
      lift_436,
      lift_139,
      lift_210,
      lift_524
    ))) {
      var methoddefvar_529, methoddefvar_530 := lift_281(lift_346);
      {
        print lift_380, "\n";
        print lift_275, "\n";
        print lift_466, "\n";
        print -1364505792, "\n";
      }
    } else {
      var lift_642 := '|';
      var lift_604 := [lift_76, lift_267, [lift_341], lift_547];
      var lift_603 := [
        lift_547,
        lift_185,
        [lift_37, lift_67, lift_534],
        lift_196,
        lift_185
      ];
      var lift_601 := [lift_481, lift_481, lift_549, lift_542];
      var lift_562 := false;
      var lift_538 := lift_539;
      {
        var lift_537 := false;
        var lift_532 := (lift_380, lift_533);
        var lift_531 := (var tmpData : seq<bool> := []; tmpData);
        if (lift_162) {
          lift_531 := lift_480;
          print lift_479, "\n";
        } else {
          var lift_535 := {'w'};
          lift_532 := lift_532;
          lift_535 := lift_536;
          lift_537 := lift_348;
          print lift_478, "\n";
          print 338990326, "\n";
        }
        print lift_233, "\n";
        print lift_231, "\n";
        print lift_467, "\n";
        if (lift_227) {
          var lift_554 := (var tmpData : seq<multiset<char>> := []; tmpData);
          print -2067969059, "\n";
          lift_538 := lift_545;
          print lift_342, "\n";
          lift_554 := lift_555;
          print lift_324, "\n";
        } else {
          lift_562 := lift_513;
          print 1398150369, "\n";
          print lift_346, "\n";
        }
      }
      var methoddefvar_565 := lift_563(lift_346);
      {
        lift_592 := (
          lift_429,
          [lift_197, false, lift_93, lift_379, lift_52],
          (-533698480, lift_195)
        );
        print lift_370, "\n";
        lift_601 := lift_267;
        lift_602 := lift_46;
        print lift_326, "\n";
      }
      lift_603 := lift_604;
      var methoddefvar_607 := lift_605(lift_344, lift_325);
      {
        var lift_641 := {lift_97, lift_204, lift_437};
        print lift_45, "\n";
        lift_641 := {(), lift_98, ()};
        print lift_427, "\n";
        lift_642 := lift_429;
      }
    }
    {
      print 
        safeSeqRef((var tmpData : seq<int> := []; tmpData), lift_370, lift_525),
        "\n";
      {
        {
          var lift_644 := (var tmpData : set<seq<set<bool>>> := {}; tmpData);
          lift_643 := lift_644;
          print -1158248401, "\n";
        }
      }
      print |lift_496|, "\n";
      {
        var methoddefvar_647, methoddefvar_648 := lift_645(lift_346);
        {
          print lift_478, "\n";
          print lift_231, "\n";
        }
        lift_654 := lift_556;
      }
    }
    var methoddefvar_655, methoddefvar_656 := lift_1(
      lift_34.1,
      lift_269.2,
      |lift_99|
    );
    {
      lift_657 := lift_389;
      var methoddefvar_658, methoddefvar_659 := lift_1(
        lift_427,
        lift_526,
        -2024105175
      );
      {
        lift_660 := (lift_160, lift_662);
      }
    }
  }
}


