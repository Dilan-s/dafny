// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_3(DT_1_3_1: T_1, DT_1_3_2: T_2, DT_1_3_3: T_2, DT_1_3_4: T_2) | DT_1_4(DT_1_4_1: T_2, DT_1_4_2: T_1, DT_1_4_3: T_2, DT_1_4_4: T_2)
datatype DT_2 = DT_2_1 | DT_2_2(DT_2_2_1: bool, DT_2_2_2: real)
datatype DT_3<T_3> = DT_3_1 | DT_3_2
datatype DT_4 = DT_4_1 | DT_4_2(DT_4_2_1: int, DT_4_2_2: real, DT_4_2_3: bool, DT_4_2_4: int) | DT_4_3(DT_4_3_1: int, DT_4_3_2: real, DT_4_3_3: int, DT_4_3_4: bool)
method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_5(p_m_method_5_1: int, p_m_method_5_2: int, p_m_method_5_3: int, p_m_method_5_4: int) returns (ret_1: real)
	requires ((p_m_method_5_4 == 0) && (p_m_method_5_1 == 12) && (p_m_method_5_3 == 0) && (p_m_method_5_2 == 18)) || ((p_m_method_5_4 == 28) && (p_m_method_5_1 == 12) && (p_m_method_5_3 == 28) && (p_m_method_5_2 == 18));
	ensures (((p_m_method_5_4 == 0) && (p_m_method_5_1 == 12) && (p_m_method_5_3 == 0) && (p_m_method_5_2 == 18)) ==> ((-28.00 < ret_1 < -27.80))) && (((p_m_method_5_4 == 28) && (p_m_method_5_1 == 12) && (p_m_method_5_3 == 28) && (p_m_method_5_2 == 18)) ==> ((-28.00 < ret_1 < -27.80)));
{
	var v_seq_5: seq<int> := [0, 10];
	var v_int_31: int := 4;
	var v_seq_215: seq<int> := v_seq_5;
	var v_int_329: int := v_int_31;
	var v_int_330: int := safe_index_seq(v_seq_215, v_int_329);
	v_int_31 := v_int_330;
	var v_int_32: int, v_int_33: int, v_int_34: int, v_int_35: int, v_int_36: int := (if (false) then (0) else (28)), (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_31]) else (2)), p_m_method_5_3, p_m_method_5_1, (match 5 {
		case 14 => 19
		case _ => -18
	});
	if (5 in {-13}) {
		
	}
	assert ((v_int_34 == 28) && (p_m_method_5_4 == 28) && (p_m_method_5_2 == 18)) || ((v_int_34 == 0) && (p_m_method_5_4 == 0) && (p_m_method_5_2 == 18));
	expect ((v_int_34 == 28) && (p_m_method_5_4 == 28) && (p_m_method_5_2 == 18)) || ((v_int_34 == 0) && (p_m_method_5_4 == 0) && (p_m_method_5_2 == 18));
	assert ((v_int_32 == 28) && (v_int_35 == 12) && (p_m_method_5_3 == 28) && (p_m_method_5_4 == 28) && (v_int_34 == 28)) || ((v_int_32 == 28) && (v_int_35 == 12) && (p_m_method_5_3 == 0) && (p_m_method_5_4 == 0) && (v_int_34 == 0));
	expect ((v_int_32 == 28) && (v_int_35 == 12) && (p_m_method_5_3 == 28) && (p_m_method_5_4 == 28) && (v_int_34 == 28)) || ((v_int_32 == 28) && (v_int_35 == 12) && (p_m_method_5_3 == 0) && (p_m_method_5_4 == 0) && (v_int_34 == 0));
	assert ((v_seq_5 == [0, 10]));
	expect ((v_seq_5 == [0, 10]));
	var v_map_2: map<int, real> := map[11 := 25.15, 8 := 21.41, 17 := 18.19];
	var v_int_37: int := 21;
	print "v_map_2", " ", (v_map_2 == map[17 := 18.19, 8 := 21.41, 11 := 25.15]), " ", "v_int_35", " ", v_int_35, " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_seq_5", " ", v_seq_5, " ", "v_int_32", " ", v_int_32, " ", "v_int_37", " ", v_int_37, " ", "v_int_36", " ", v_int_36, " ", "p_m_method_5_4", " ", p_m_method_5_4, " ", "p_m_method_5_3", " ", p_m_method_5_3, " ", "v_int_31", " ", v_int_31, " ", "p_m_method_5_2", " ", p_m_method_5_2, " ", "p_m_method_5_1", " ", p_m_method_5_1, "\n";
	return (if ((v_int_37 in v_map_2)) then (v_map_2[v_int_37]) else (-27.90));
}

method m_method_4(p_m_method_4_1: int, p_m_method_4_2: (real, real), p_m_method_4_3: int, p_m_method_4_4: int) returns (ret_1: char)
	requires ((23.17 < (p_m_method_4_2).0 < 23.37) && (15.01 < (p_m_method_4_2).1 < 15.21) && (p_m_method_4_1 == 23) && (p_m_method_4_4 == 20) && (p_m_method_4_3 == 24)) || ((-17.91 < (p_m_method_4_2).0 < -17.71) && (-20.60 < (p_m_method_4_2).1 < -20.40) && (p_m_method_4_1 == 19) && (p_m_method_4_4 == 13) && (p_m_method_4_3 == 6));
	ensures (((23.17 < (p_m_method_4_2).0 < 23.37) && (15.01 < (p_m_method_4_2).1 < 15.21) && (p_m_method_4_1 == 23) && (p_m_method_4_4 == 20) && (p_m_method_4_3 == 24)) ==> ((ret_1 == 'U'))) && (((-17.91 < (p_m_method_4_2).0 < -17.71) && (-20.60 < (p_m_method_4_2).1 < -20.40) && (p_m_method_4_1 == 19) && (p_m_method_4_4 == 13) && (p_m_method_4_3 == 6)) ==> ((ret_1 == 'U')));
{
	var v_int_20: int, v_int_21: int, v_int_22: int, v_int_23: int := -26, 6, 8, 5;
	v_int_20 := 2;
	var v_real_real_9: (real, real) := (-17.81, -20.50);
	print "v_int_23", " ", v_int_23, " ", "v_int_22", " ", v_int_22, " ", "v_int_21", " ", v_int_21, " ", "p_m_method_4_2.0", " ", (p_m_method_4_2.0 == -17.81), " ", "p_m_method_4_2.1", " ", (p_m_method_4_2.1 == -20.50), " ", "p_m_method_4_4", " ", p_m_method_4_4, " ", "p_m_method_4_1", " ", p_m_method_4_1, " ", "v_int_20", " ", v_int_20, " ", "p_m_method_4_3", " ", p_m_method_4_3, " ", "p_m_method_4_2", " ", (p_m_method_4_2 == v_real_real_9), "\n";
	return 'U';
}

method m_method_3(p_m_method_3_1: bool, p_m_method_3_2: char, p_m_method_3_3: array<int>) returns (ret_1: char)
	requires ((p_m_method_3_1 == true) && p_m_method_3_3.Length == 4 && (p_m_method_3_3[0] == 21) && (p_m_method_3_3[1] == 10) && (p_m_method_3_3[2] == 22) && (p_m_method_3_3[3] == 27) && (p_m_method_3_2 == 'U'));
	ensures (((p_m_method_3_1 == true) && p_m_method_3_3.Length == 4 && (p_m_method_3_3[0] == 21) && (p_m_method_3_3[1] == 10) && (p_m_method_3_3[2] == 22) && (p_m_method_3_3[3] == 27) && (p_m_method_3_2 == 'U')) ==> ((ret_1 == 'U')));
{
	var v_int_24: int := 23;
	var v_real_real_1: (real, real) := (23.27, 15.11);
	var v_real_real_2: (real, real) := v_real_real_1;
	var v_int_25: int := 24;
	var v_int_26: int := 20;
	var v_char_2: char := m_method_4(v_int_24, v_real_real_2, v_int_25, v_int_26);
	var v_real_real_10: (real, real) := (23.27, 15.11);
	var v_real_real_11: (real, real) := (23.27, 15.11);
	print "v_char_2", " ", (v_char_2 == 'U'), " ", "v_real_real_1.1", " ", (v_real_real_1.1 == 15.11), " ", "v_real_real_2", " ", (v_real_real_2 == v_real_real_10), " ", "v_real_real_1", " ", (v_real_real_1 == v_real_real_11), " ", "v_real_real_1.0", " ", (v_real_real_1.0 == 23.27), " ", "v_int_24", " ", v_int_24, " ", "p_m_method_3_3[0]", " ", p_m_method_3_3[0], " ", "p_m_method_3_3[1]", " ", p_m_method_3_3[1], " ", "p_m_method_3_3[2]", " ", p_m_method_3_3[2], " ", "v_int_26", " ", v_int_26, " ", "v_int_25", " ", v_int_25, " ", "p_m_method_3_2", " ", (p_m_method_3_2 == 'U'), " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_3", "\n";
	return v_char_2;
}

method safe_division(p_safe_division_1: int, p_safe_division_2: int) returns (ret_1: int)
	ensures (p_safe_division_2 == 0 ==> ret_1 == p_safe_division_1) && (p_safe_division_2 != 0 ==> ret_1 == p_safe_division_1 / p_safe_division_2);
{
	return (if ((p_safe_division_2 != 0)) then ((p_safe_division_1 / p_safe_division_2)) else (p_safe_division_1));
}

method safe_subsequence(p_safe_subsequence_1: seq, p_safe_subsequence_2: int, p_safe_subsequence_3: int) returns (ret_1: int, ret_2: int)
	ensures ((|p_safe_subsequence_1| > 0) ==> ((0 <= ret_1 < |p_safe_subsequence_1|) && (0 <= ret_2 < |p_safe_subsequence_1|) && ret_1 <= ret_2)) && ((((0 <= p_safe_subsequence_2 < |p_safe_subsequence_1|) ==> (ret_1 == p_safe_subsequence_2)) && ((0 > p_safe_subsequence_2 || p_safe_subsequence_2 >= |p_safe_subsequence_1|) ==> (ret_1 == 0)) && ((0 <= p_safe_subsequence_3 < |p_safe_subsequence_1|) ==> (ret_2 == p_safe_subsequence_3)) && ((0 > p_safe_subsequence_3 || p_safe_subsequence_3 >= |p_safe_subsequence_1|) ==> (ret_2 == 0))) || ((((0 <= p_safe_subsequence_2 < |p_safe_subsequence_1|) ==> (ret_2 == p_safe_subsequence_2)) && ((0 > p_safe_subsequence_2 || p_safe_subsequence_2 >= |p_safe_subsequence_1|) ==> (ret_2 == 0)) && ((0 <= p_safe_subsequence_3 < |p_safe_subsequence_1|) ==> (ret_1 == p_safe_subsequence_3)) && ((0 > p_safe_subsequence_3 || p_safe_subsequence_3 >= |p_safe_subsequence_1|) ==> (ret_1 == 0)))));
{
	var v_seq_1: seq := p_safe_subsequence_1;
	var v_int_2: int := p_safe_subsequence_2;
	var v_int_3: int := safe_index_seq(v_seq_1, v_int_2);
	var v_int_1: int := v_int_3;
	var v_seq_2: seq := p_safe_subsequence_1;
	var v_int_5: int := p_safe_subsequence_3;
	var v_int_6: int := safe_index_seq(v_seq_2, v_int_5);
	var v_int_4: int := v_int_6;
	if (v_int_1 <= v_int_4) {
		return v_int_1, v_int_4;
	} else {
		return v_int_4, v_int_1;
	}
}

method m_method_2(p_m_method_2_1: char) returns (ret_1: bool)
	requires ((p_m_method_2_1 == 'g'));
	ensures (((p_m_method_2_1 == 'g')) ==> ((ret_1 == true)));
{
	print "p_m_method_2_1", " ", (p_m_method_2_1 == 'g'), "\n";
	return (false ==> false);
}

method m_method_1(p_m_method_1_1: real) returns (ret_1: char)
	requires ((-28.00 < p_m_method_1_1 < -27.80));
	ensures (((-28.00 < p_m_method_1_1 < -27.80)) ==> ((ret_1 == 'U')));
{
	var v_int_9: int := 2;
	var v_int_10: int := 25;
	var v_int_11: int := safe_division(v_int_9, v_int_10);
	var v_int_12: int := v_int_11;
	var v_int_13: int := v_int_10;
	var v_int_14: int := safe_modulus(v_int_12, v_int_13);
	var v_int_15: int := v_int_9;
	var v_int_16: int := v_int_12;
	var v_int_17: int := safe_division(v_int_15, v_int_16);
	var v_int_18: int, v_int_19: int := v_int_14, v_int_17;
	for v_int_8 := v_int_18 to v_int_19 
		invariant (v_int_19 - v_int_8 >= 0)
	{
		var v_char_1: char := (match true {
			case true => 'g'
			case _ => 'u'
		});
		var v_bool_2: bool := m_method_2(v_char_1);
		if v_bool_2 {
			print "v_char_1", " ", (v_char_1 == 'g'), " ", "v_bool_2", " ", v_bool_2, " ", "v_int_8", " ", v_int_8, " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_int_11", " ", v_int_11, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == -27.90), " ", "v_int_10", " ", v_int_10, " ", "v_int_17", " ", v_int_17, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_9", " ", v_int_9, " ", "v_int_14", " ", v_int_14, "\n";
			break;
		}
		assert true;
		expect true;
		continue;
	}
	assert ((v_int_12 == 0) && (v_int_10 == 25) && (v_int_9 == 2) && (v_int_11 == 0) && (v_int_15 == 2));
	expect ((v_int_12 == 0) && (v_int_10 == 25) && (v_int_9 == 2) && (v_int_11 == 0) && (v_int_15 == 2));
	var v_bool_3: bool := ({29, 12} !! {8});
	var v_int_27: int := 19;
	var v_real_real_3: (real, real) := (-17.81, -20.50);
	var v_real_real_4: (real, real) := v_real_real_3;
	var v_int_28: int := 6;
	var v_int_29: int := 13;
	var v_char_3: char := m_method_4(v_int_27, v_real_real_4, v_int_28, v_int_29);
	var v_char_4: char := v_char_3;
	var v_seq_4: seq<array<int>> := [];
	var v_int_30: int := 8;
	var v_array_1: array<int> := new int[4] [21, 10, 22, 27];
	var v_array_2: array<int> := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_30]) else (v_array_1));
	var v_char_5: char := m_method_3(v_bool_3, v_char_4, v_array_2);
	var v_real_real_12: (real, real) := (-17.81, -20.50);
	var v_real_real_13: (real, real) := (-17.81, -20.50);
	print "v_bool_3", " ", v_bool_3, " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_real_real_4", " ", (v_real_real_4 == v_real_real_12), " ", "v_real_real_3", " ", (v_real_real_3 == v_real_real_13), " ", "p_m_method_1_1", " ", (p_m_method_1_1 == -27.90), " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_int_9", " ", v_int_9, " ", "v_array_2", " ", (v_array_2 == v_array_1), " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_char_3", " ", (v_char_3 == 'U'), " ", "v_char_5", " ", (v_char_5 == 'U'), " ", "v_char_4", " ", (v_char_4 == 'U'), " ", "v_real_real_3.1", " ", (v_real_real_3.1 == -20.50), " ", "v_real_real_3.0", " ", (v_real_real_3.0 == -17.81), " ", "v_int_29", " ", v_int_29, " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_int_17", " ", v_int_17, " ", "v_seq_4", " ", (v_seq_4 == []), " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_int_30", " ", v_int_30, " ", "v_array_1[3]", " ", v_array_1[3], "\n";
	return v_char_5;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_map_1: map<bool, bool> := map[true := true, false := false];
	var v_bool_1: bool := false;
	var v_seq_3: seq<multiset<bool>> := [multiset{}, multiset({true})];
	var v_int_7: int := 28;
	var v_seq_217: seq<multiset<bool>> := v_seq_3;
	var v_int_337: int := v_int_7;
	var v_int_338: int := safe_index_seq(v_seq_217, v_int_337);
	v_int_7 := v_int_338;
	var v_int_38: int := (match 26 {
		case 2 => 11
		case 22 => -21
		case _ => 12
	});
	var v_int_39: int := (if (true) then (18) else (28));
	var v_int_40: int := v_int_7;
	var v_int_41: int := v_int_7;
	var v_real_1: real := m_method_5(v_int_38, v_int_39, v_int_40, v_int_41);
	var v_real_2: real := v_real_1;
	var v_char_6: char := m_method_1(v_real_2);
	var v_seq_6: seq<int> := [8];
	var v_seq_216: seq<int> := v_seq_6;
	var v_int_333: int := 27;
	var v_int_334: int := 26;
	var v_int_335: int, v_int_336: int := safe_subsequence(v_seq_216, v_int_333, v_int_334);
	var v_int_331: int, v_int_332: int := v_int_335, v_int_336;
	var v_seq_7: seq<int> := ((match 19.79 {
		case 26.11 => [28, 14, 6]
		case _ => [12]
	}) + (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_331..v_int_332]) else (v_seq_6)));
	var v_int_42: int := v_int_40;
	var v_int_43: int := safe_index_seq(v_seq_7, v_int_42);
	v_bool_1, v_char_6, v_int_40 := (false in (if ((if ((v_bool_1 in v_map_1)) then (v_map_1[v_bool_1]) else (true))) then ((multiset{true, true, false, false} + multiset{true, false})) else ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else (multiset({true, false, false})))))), v_char_6, v_int_43;
	var v_map_3: map<int, multiset<int>> := map[20 := multiset{29, 2, -3}, 10 := multiset{-10, 7, 19}, -14 := multiset({14, 13}), 19 := multiset{6, 24, 4, 0}];
	var v_int_44: int := -26;
	if ((match 18 {
		case 3 => (multiset{6, 29} - multiset{28, 12, 16, 9})
		case _ => (multiset({7, 19, 29}) * multiset({14}))
	}) != ((if ((v_int_44 in v_map_3)) then (v_map_3[v_int_44]) else (multiset{})) - (multiset{} + multiset{11, 0, 5, 20}))) {
		var v_map_4: map<int, seq<int>> := map[0 := [29], 26 := [4], 15 := [13, 28], 12 := []][9 := [16, 8]];
		var v_int_48: int := v_int_40;
		var v_seq_8: seq<int> := [];
		var v_seq_9: seq<int> := v_seq_8;
		var v_int_45: int := 7;
		var v_int_46: int := safe_index_seq(v_seq_9, v_int_45);
		var v_int_47: int := v_int_46;
		var v_seq_10: seq<int> := (if ((v_int_48 in v_map_4)) then (v_map_4[v_int_48]) else ((if ((|v_seq_8| > 0)) then (v_seq_8[v_int_47 := 7]) else (v_seq_8))));
		var v_int_49: int := v_int_46;
		var v_int_50: int := safe_index_seq(v_seq_10, v_int_49);
		var v_seq_11: seq<int> := [13, 15, 1];
		var v_int_51: int := 19;
		var v_map_5: map<int, int> := map[10 := 18][25 := 29][(19 - 4) := (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_51]) else (29))];
		var v_int_53: int := v_int_38;
		var v_seq_12: seq<int> := v_seq_10;
		var v_int_52: int := v_int_51;
		v_int_53, v_int_7 := v_int_50, (if ((v_int_53 in v_map_5)) then (v_map_5[v_int_53]) else ((if ((|v_seq_12| > 0)) then (v_seq_12[v_int_52]) else ((if (false) then (24) else (-26))))));
		var v_DT_1_3_1: DT_1<bool, set<real>> := DT_1_3(false, {29.79, -19.95, 5.78}, {-26.53, -2.15, 26.94}, {-11.26, -5.25});
		var v_DT_1_3_2: DT_1<bool, set<real>> := DT_1_3(true, {14.80, 6.98}, {}, {28.95, 12.23, 13.61});
		var v_DT_1_3_3: DT_1<bool, set<real>> := DT_1_3(false, {}, {}, {});
		var v_DT_1_3_4: DT_1<bool, set<real>> := DT_1_3(false, {}, {18.44, 1.36, 17.22, 25.71}, {-20.59});
		var v_DT_1_3_5: DT_1<bool, set<real>> := DT_1_3(false, {}, {1.27}, {-27.96, 4.98, -0.15});
		var v_DT_1_3_6: DT_1<bool, set<real>> := DT_1_3(true, {9.86, 0.76, 11.90, -22.37}, {}, {-3.37, -6.51});
		var v_map_6: map<int, map<DT_1<bool, set<real>>, set<bool>>> := map[12 := map[v_DT_1_3_1 := {}], 5 := map[v_DT_1_3_2 := {true, false, false, true}, v_DT_1_3_3 := {false, true, true}, v_DT_1_3_4 := {true, true}, v_DT_1_3_5 := {false}, v_DT_1_3_6 := {}]];
		var v_int_54: int := 28;
		var v_DT_1_3_7: DT_1<bool, set<real>> := DT_1_3(true, {12.18, -7.66, -21.64, -28.37}, {-26.05}, {-21.14, 26.34, -20.63});
		var v_DT_1_3_8: DT_1<bool, set<real>> := DT_1_3(false, {5.81, -23.51, 20.56, 8.46}, {7.47}, {});
		var v_DT_1_3_9: DT_1<bool, set<real>> := DT_1_3(true, {19.31, 9.07, -3.02, 0.60}, {-18.88, -1.14, -12.12}, {-26.82, -20.53, -26.30, 21.09});
		var v_DT_1_3_10: DT_1<bool, set<real>> := DT_1_3(false, {-5.89, 1.75, -26.53, 6.24}, {11.60, -29.58, 20.58, 8.43}, {10.17});
		var v_map_9: map<set<bool>, set<bool>> := (map[{false} := {true, true}, {} := {true, false}, {true, false, true, false} := {}, {true, false, true} := {false}, {false, false, true, false} := {true, false, true}][{true, false} := {true}] - ({} - {}));
		var v_seq_13: seq<map<set<bool>, set<bool>>> := [map[{false, false, true} := {true}, {true, true} := {false, false}, {false, false} := {}, {} := {false}], map[{} := {false, false, false}, {false, false} := {false, false}, {true, false} := {true}, {true, true, true, true} := {true, true, true, true}, {true, false, false} := {true, true, false}]];
		var v_int_55: int := 12;
		var v_map_8: map<set<bool>, set<bool>> := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_55]) else (map[{false, false, true, true} := {false, false, true, false}, {false, true} := {}]));
		var v_array_3: array<char> := new char[3] ['f', 'b', 'q'];
		var v_array_4: array<char> := new char[4] ['Y', 'y', 'C', 't'];
		var v_set_1: set<bool> := (map[true := v_array_3, false := v_array_4]).Keys;
		var v_map_7: map<int, set<bool>> := map[19 := {false, false, true, false}, 13 := {false, true, true}, 7 := {false, true, true}, 7 := {}, -18 := {}];
		var v_int_56: int := 12;
		var v_set_2: set<bool> := (if ((v_set_1 in v_map_8)) then (v_map_8[v_set_1]) else ((if ((v_int_56 in v_map_7)) then (v_map_7[v_int_56]) else ({}))));
		var v_set_3: set<set<bool>>, v_set_4: set<bool> := (if ((v_bool_1 && (if (true) then (true) else (false)))) then ((match false {
			case _ => (match 20 {
				case _ => {{}, {}}
			})
		})) else (((if ((v_int_54 in v_map_6)) then (v_map_6[v_int_54]) else (map[v_DT_1_3_7 := {false}, v_DT_1_3_8 := {false}, v_DT_1_3_9 := {false, false, true, true}, v_DT_1_3_10 := {true}]))).Values)), (if ((v_set_2 in v_map_9)) then (v_map_9[v_set_2]) else (((if (false) then ({true, true, true}) else ({})) * v_set_1)));
		var v_map_10: map<int, int> := map[18 := 19, -17 := -12, 18 := 16, 25 := 10];
		var v_int_57: int := 0;
		var v_map_11: map<int, int> := map[10 := 21, 4 := 24, 7 := 4];
		var v_int_58: int := 11;
		if ((match 2 {
			case _ => (match 29 {
				case _ => 26
			})
		}) in (v_map_5 - (match 28 {
			case _ => {3, -17, 1, 19}
		}))) {
			var v_seq_14: seq<int> := [16];
			var v_seq_16: seq<int> := (if ((|v_seq_14| > 0)) then (v_seq_14[11..26]) else (v_seq_14));
			var v_seq_15: seq<int> := [2, 3, 23, 14];
			var v_int_59: int := 6;
			var v_int_60: int := (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_59]) else (11));
			var v_seq_17: seq<bool> := [false];
			var v_int_61: int := 2;
			var v_int_real_real_1: (int, real, real) := (18, 20.41, 11.73);
			var v_set_int_real_real_1: (set<bool>, (int, real, real)) := ({true, true, true}, v_int_real_real_1);
			var v_int_real_real_2: (int, real, real) := (29, -7.07, 29.95);
			var v_set_int_real_real_2: (set<bool>, (int, real, real)) := ({true}, v_int_real_real_2);
			var v_int_real_real_3: (int, real, real) := (7, 17.83, -11.20);
			var v_set_int_real_real_3: (set<bool>, (int, real, real)) := ({false, true, true, true}, v_int_real_real_3);
			var v_int_real_real_4: (int, real, real) := (12, -22.76, 29.50);
			var v_set_int_real_real_4: (set<bool>, (int, real, real)) := ({true, true}, v_int_real_real_4);
			var v_int_real_real_5: (int, real, real) := (9, 28.30, 12.08);
			var v_set_int_real_real_5: (set<bool>, (int, real, real)) := ({true, true}, v_int_real_real_5);
			var v_map_13: map<(set<bool>, (int, real, real)), int> := map[v_set_int_real_real_1 := 28, v_set_int_real_real_2 := 21, v_set_int_real_real_3 := 8, v_set_int_real_real_4 := 26][v_set_int_real_real_5 := 17];
			var v_int_real_1: (int, real) := (6, -14.79);
			var v_int_real_real_6: (int, real, real) := (14, 22.03, -18.52);
			var v_set_int_real_real_6: (set<bool>, (int, real, real)) := ({true, true}, v_int_real_real_6);
			var v_int_real_2: (int, real) := (1, -9.12);
			var v_int_real_3: (int, real) := (2, 23.28);
			var v_int_real_4: (int, real) := (-10, 0.20);
			var v_int_real_5: (int, real) := (23, 23.95);
			var v_int_real_real_7: (int, real, real) := (12, 6.26, 13.61);
			var v_set_int_real_real_7: (set<bool>, (int, real, real)) := ({true, true, false}, v_int_real_real_7);
			var v_int_real_6: (int, real) := (17, 8.58);
			var v_int_real_real_8: (int, real, real) := (20, 4.03, -26.48);
			var v_set_int_real_real_8: (set<bool>, (int, real, real)) := ({true, false}, v_int_real_real_8);
			var v_int_real_7: (int, real) := (7, -5.09);
			var v_int_real_8: (int, real) := (16, 12.76);
			var v_int_real_9: (int, real) := (17, -15.90);
			var v_int_real_10: (int, real) := (15, 29.37);
			var v_int_real_real_9: (int, real, real) := (3, -11.78, 1.24);
			var v_set_int_real_real_9: (set<bool>, (int, real, real)) := ({true, false, true, true}, v_int_real_real_9);
			var v_map_12: map<multiset<(int, real)>, (set<bool>, (int, real, real))> := map[multiset{v_int_real_1} := v_set_int_real_real_6, multiset({v_int_real_2, v_int_real_3, v_int_real_4, v_int_real_5}) := v_set_int_real_real_7, multiset{v_int_real_6} := v_set_int_real_real_8, multiset({v_int_real_7, v_int_real_8, v_int_real_9, v_int_real_10}) := v_set_int_real_real_9];
			var v_int_real_11: (int, real) := (-16, 14.68);
			var v_multiset_1: multiset<(int, real)> := multiset{v_int_real_11};
			var v_int_real_real_10: (int, real, real) := (20, -25.51, -21.39);
			var v_set_int_real_real_10: (set<bool>, (int, real, real)) := ({true, true}, v_int_real_real_10);
			var v_set_int_real_real_11: (set<bool>, (int, real, real)) := (if ((v_multiset_1 in v_map_12)) then (v_map_12[v_multiset_1]) else (v_set_int_real_real_10));
			var v_int_int_bool_1: (int, int, bool) := (24, 18, true);
			var v_char_int_int_bool_1: (char, (int, int, bool)) := ('h', v_int_int_bool_1);
			var v_int_int_bool_2: (int, int, bool) := (4, 10, true);
			var v_char_int_int_bool_2: (char, (int, int, bool)) := ('g', v_int_int_bool_2);
			var v_map_14: map<(char, (int, int, bool)), char> := map[v_char_int_int_bool_1 := 'Z', v_char_int_int_bool_2 := 'a'];
			var v_int_int_bool_3: (int, int, bool) := (11, 6, false);
			var v_char_int_int_bool_3: (char, (int, int, bool)) := ('Z', v_int_int_bool_3);
			var v_char_int_int_bool_4: (char, (int, int, bool)) := v_char_int_int_bool_3;
			var v_seq_18: seq<int> := [28, 23];
			var v_int_62: int := 4;
			var v_map_15: map<char, int> := (map['o' := 4] - {'Y'})[(if ((v_char_int_int_bool_4 in v_map_14)) then (v_map_14[v_char_int_int_bool_4]) else ('G')) := (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_62]) else (7))];
			var v_seq_19: seq<char> := [];
			var v_int_63: int := 24;
			var v_char_7: char := (if ((match 12 {
				case _ => false
			})) then (v_array_3[2]) else ((if ((|v_seq_19| > 0)) then (v_seq_19[v_int_63]) else ('H'))));
			var v_array_5: array<((real, bool), real)> := new ((real, bool), real)[4];
			var v_real_bool_1: (real, bool) := (-1.44, true);
			var v_real_bool_real_1: ((real, bool), real) := (v_real_bool_1, -28.78);
			v_array_5[0] := v_real_bool_real_1;
			var v_real_bool_2: (real, bool) := (6.33, false);
			var v_real_bool_real_2: ((real, bool), real) := (v_real_bool_2, 17.11);
			v_array_5[1] := v_real_bool_real_2;
			var v_real_bool_3: (real, bool) := (0.99, false);
			var v_real_bool_real_3: ((real, bool), real) := (v_real_bool_3, -8.75);
			v_array_5[2] := v_real_bool_real_3;
			var v_real_bool_4: (real, bool) := (20.74, true);
			var v_real_bool_real_4: ((real, bool), real) := (v_real_bool_4, -10.79);
			v_array_5[3] := v_real_bool_real_4;
			v_int_60, v_int_41, v_int_47 := ((if ((|v_seq_16| > 0)) then (v_seq_16[v_int_60]) else ((16 * 26))) / (if ((if ((|v_seq_17| > 0)) then (v_seq_17[v_int_61]) else (true))) then ((16 % 25)) else ((if (true) then (19) else (27))))), (if (v_DT_1_3_4.DT_1_3_1) then ((v_int_48 / (match -19 {
				case _ => 24
			}))) else ((if ((v_set_int_real_real_11 in v_map_13)) then (v_map_13[v_set_int_real_real_11]) else ((if (true) then (27) else (11)))))), (if ((v_char_7 in v_map_15)) then (v_map_15[v_char_7]) else ((v_int_int_bool_1.1 / v_array_5.Length)));
			var v_int_64: int := v_int_real_11.0;
			var v_seq_20: seq<int> := [];
			var v_int_66: int := 3;
			var v_real_real_5: (real, real) := (-8.76, -17.84);
			var v_seq_real_real_bool_1: (seq<int>, (real, real), bool) := ([18, 5], v_real_real_5, true);
			var v_real_real_6: (real, real) := (5.46, -28.59);
			var v_seq_real_real_bool_2: (seq<int>, (real, real), bool) := ([27, 0, 12], v_real_real_6, true);
			var v_real_real_7: (real, real) := (13.72, -6.34);
			var v_seq_real_real_bool_3: (seq<int>, (real, real), bool) := ([], v_real_real_7, true);
			var v_map_16: map<(seq<int>, (real, real), bool), int> := map[v_seq_real_real_bool_1 := 15, v_seq_real_real_bool_2 := 1, v_seq_real_real_bool_3 := -1];
			var v_real_real_8: (real, real) := (23.54, 9.63);
			var v_seq_real_real_bool_4: (seq<int>, (real, real), bool) := ([7], v_real_real_8, true);
			var v_seq_real_real_bool_5: (seq<int>, (real, real), bool) := v_seq_real_real_bool_4;
			var v_map_17: map<bool, seq<int>> := map[false := [16, 29, 17, -24], false := [18, 11, 16, 8], false := [24, 7, 5], false := [22, 20, 5]];
			var v_bool_4: bool := true;
			var v_seq_22: seq<int> := (if ((v_bool_4 in v_map_17)) then (v_map_17[v_bool_4]) else ([]));
			var v_seq_21: seq<int> := [9];
			var v_int_67: int := 20;
			var v_int_68: int := (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_67]) else (-27));
			var v_int_65: int := (if (((if ((|v_seq_20| > 0)) then (v_seq_20[v_int_66]) else (7)) > (if ((v_seq_real_real_bool_5 in v_map_16)) then (v_map_16[v_seq_real_real_bool_5]) else (-25)))) then ((if ((|v_seq_22| > 0)) then (v_seq_22[v_int_68]) else ((8.43).Floor))) else ((if (v_seq_real_real_bool_2.2) then ((if (false) then (4) else (0))) else (v_int_real_real_5.0))));
			while (v_int_64 < v_int_65) 
				decreases v_int_65 - v_int_64;
				invariant (v_int_64 <= v_int_65);
			{
				v_int_64 := (v_int_64 + 1);
				break;
			}
		}
		var v_seq_23: seq<char> := ['x'];
		var v_seq_24: seq<char> := v_seq_23;
		var v_int_69: int := 9;
		var v_int_70: int := safe_index_seq(v_seq_24, v_int_69);
		var v_int_71: int := v_int_70;
		var v_seq_25: seq<char> := (if ((|v_seq_23| > 0)) then (v_seq_23[v_int_71 := 'T']) else (v_seq_23));
		var v_int_72: int := v_int_7;
		var v_map_18: map<int, char> := map[18 := 'V', 26 := 'W', 25 := 'v', 9 := 'r', 5 := 'N'];
		var v_int_73: int := 16;
		var v_map_19: map<bool, char> := map[false := 'Q', false := 'J', true := 'V', true := 'k'];
		var v_bool_5: bool := false;
		var v_int_bool_1: (int, bool) := (6, false);
		var v_int_bool_2: (int, bool) := (8, false);
		var v_int_bool_3: (int, bool) := (-10, false);
		var v_int_bool_4: (int, bool) := (17, false);
		var v_int_bool_5: (int, bool) := (27, true);
		var v_int_bool_6: (int, bool) := (1, true);
		var v_seq_27: seq<(int, bool)> := ([v_int_bool_1, v_int_bool_2] + [v_int_bool_3, v_int_bool_4, v_int_bool_5, v_int_bool_6]);
		var v_seq_28: seq<(int, bool)> := v_seq_27;
		var v_int_75: int := (14 / 22);
		var v_int_76: int := safe_index_seq(v_seq_28, v_int_75);
		var v_int_77: int := v_int_76;
		var v_seq_26: seq<(int, bool)> := [];
		var v_int_74: int := 15;
		var v_int_bool_7: (int, bool) := (9, false);
		var v_seq_30: seq<(int, bool)> := (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_77 := (if ((|v_seq_26| > 0)) then (v_seq_26[v_int_74]) else (v_int_bool_7))]) else (v_seq_27));
		var v_DT_3_1_1: DT_3<array<real>> := DT_3_1;
		var v_DT_3_1_2: DT_3<array<real>> := DT_3_1;
		var v_DT_3_1_3: DT_3<array<real>> := DT_3_1;
		var v_map_20: map<DT_3<array<real>>, int> := map[v_DT_3_1_1 := 4, v_DT_3_1_2 := 11][v_DT_3_1_3 := -18];
		var v_DT_3_1_4: DT_3<array<real>> := v_DT_3_1_2;
		var v_seq_29: seq<int> := [18, 11, 23, 6];
		var v_int_78: int := 13;
		var v_int_79: int := (if ((v_DT_3_1_4 in v_map_20)) then (v_map_20[v_DT_3_1_4]) else ((if ((|v_seq_29| > 0)) then (v_seq_29[v_int_78]) else (5))));
		var v_DT_1_4_1: DT_1<int, char> := DT_1_4('k', 26, 'q', 'o');
		var v_DT_1_4_2: DT_1<int, char> := DT_1_4('c', 13, 'x', 'E');
		var v_DT_1_4_3: DT_1<int, char> := DT_1_4('a', 21, 'R', 'V');
		var v_DT_1_4_4: DT_1<int, char> := DT_1_4('k', 7, 'V', 'p');
		var v_DT_1_4_5: DT_1<int, char> := DT_1_4('P', 18, 'v', 'P');
		var v_DT_1_4_6: DT_1<int, char> := DT_1_4('Z', 21, 'o', 'N');
		var v_DT_1_4_7: DT_1<int, char> := DT_1_4('D', 6, 'o', 'X');
		var v_DT_1_4_8: DT_1<int, char> := DT_1_4('r', -27, 'Z', 'p');
		var v_DT_1_4_9: DT_1<int, char> := DT_1_4('x', 14, 'T', 'W');
		var v_DT_1_4_10: DT_1<int, char> := DT_1_4('g', 18, 't', 'H');
		var v_DT_1_4_11: DT_1<int, char> := DT_1_4('g', 6, 'r', 'g');
		var v_DT_1_4_12: DT_1<int, char> := DT_1_4('R', 6, 'v', 'A');
		var v_seq_31: seq<map<char, DT_1<int, char>>> := [map['Q' := v_DT_1_4_1, 'z' := v_DT_1_4_2, 'T' := v_DT_1_4_3], map['G' := v_DT_1_4_4, 'X' := v_DT_1_4_5, 'D' := v_DT_1_4_6], map['x' := v_DT_1_4_7, 'M' := v_DT_1_4_8, 'k' := v_DT_1_4_9, 'F' := v_DT_1_4_10], map['W' := v_DT_1_4_11, 't' := v_DT_1_4_12]];
		var v_int_80: int := 27;
		var v_DT_1_4_13: DT_1<int, char> := DT_1_4('O', 13, 'w', 'T');
		var v_DT_1_4_14: DT_1<int, char> := DT_1_4('k', 6, 'o', 'O');
		var v_DT_1_4_15: DT_1<int, char> := DT_1_4('d', 20, 'y', 'X');
		var v_DT_1_4_16: DT_1<int, char> := DT_1_4('W', 6, 'Z', 'S');
		var v_map_23: map<char, DT_1<int, char>> := (match true {
			case _ => map['V' := v_DT_1_4_14, 'H' := v_DT_1_4_15]['b' := v_DT_1_4_16]
		});
		var v_map_21: map<bool, char> := (map[false := 'z', false := 'R', true := 'P', false := 'L', true := 'p'] - {false, false, true});
		var v_bool_6: bool := (if (false) then (false) else (false));
		var v_char_9: char := (if ((v_bool_6 in v_map_21)) then (v_map_21[v_bool_6]) else ((if (false) then ('i') else ('s'))));
		var v_DT_1_4_17: DT_1<int, char> := DT_1_4('f', 16, 'p', 'k');
		var v_DT_1_4_18: DT_1<int, char> := DT_1_4('o', 1, 'e', 'L');
		var v_DT_1_4_19: DT_1<int, char> := DT_1_4('L', 8, 'j', 'I');
		var v_map_22: map<char, DT_1<int, char>> := map['L' := v_DT_1_4_17, 'J' := v_DT_1_4_18, 'H' := v_DT_1_4_19];
		var v_char_8: char := 'b';
		var v_DT_1_4_20: DT_1<int, char> := DT_1_4('e', 27, 'y', 'L');
		var v_DT_1_4_21: DT_1<int, char> := DT_1_4('o', 16, 'd', 'E');
		var v_DT_1_4_22: DT_1<int, char> := DT_1_4('X', 19, 'g', 'q');
		var v_array_6: array<int> := new int[4] [11, 18, 12, 12];
		var v_array_7: array<int> := new int[5] [4, 28, 26, 1, 23];
		var v_array_8: array<int> := new int[3] [8, -21, 23];
		var v_array_9: array<int> := new int[4] [24, 11, 22, 1];
		var v_array_10: array<int> := new int[4];
		v_array_10[0] := 29;
		v_array_10[1] := 19;
		v_array_10[2] := 5;
		v_array_10[3] := 11;
		var v_array_11: array<int> := new int[5] [-24, -14, 13, 4, 24];
		var v_array_12: array<int> := new int[3];
		v_array_12[0] := 26;
		v_array_12[1] := 9;
		v_array_12[2] := 20;
		var v_array_13: array<int> := new int[4] [1, 23, 27, 24];
		var v_array_14: array<int> := new int[5] [23, -17, 28, 25, 3];
		var v_array_15: array<int> := new int[4] [29, -19, 3, 27];
		var v_array_16: array<int> := new int[4] [29, 14, 17, 16];
		var v_array_17: array<int> := new int[3];
		v_array_17[0] := 22;
		v_array_17[1] := 15;
		v_array_17[2] := -17;
		var v_array_18: array<int> := new int[4] [2, 11, 29, 12];
		var v_seq_32: seq<map<bool, array<int>>> := [map[false := v_array_6, false := v_array_7], map[true := v_array_8, false := v_array_9, false := v_array_10, false := v_array_11, false := v_array_12], map[true := v_array_13, false := v_array_14, true := v_array_15], map[false := v_array_16, true := v_array_17, true := v_array_18]];
		var v_seq_33: seq<map<bool, array<int>>> := (if ((|v_seq_32| > 0)) then (v_seq_32[17..15]) else (v_seq_32));
		var v_seq_34: seq<map<bool, array<int>>> := (if ((|v_seq_33| > 0)) then (v_seq_33[(if (true) then (27) else (18))..0]) else (v_seq_33));
		var v_int_81: int := (match 14 {
			case _ => v_int_39
		});
		var v_array_19: array<int> := new int[5] [3, 27, 22, 13, 24];
		var v_array_20: array<int> := new int[4] [21, -21, 5, 4];
		var v_array_21: array<int> := new int[4] [3, 15, 25, 19];
		var v_array_22: array<int> := new int[5] [21, 15, 23, 20, 24];
		var v_array_23: array<int> := new int[4] [-28, 10, 12, 20];
		var v_array_24: array<int> := new int[3] [10, 23, 29];
		var v_array_25: array<int> := new int[4] [2, 14, 3, 0];
		var v_array_26: array<int> := new int[3] [24, 22, 27];
		var v_array_27: array<int> := new int[4] [8, 20, 19, 27];
		var v_array_28: array<int> := new int[4] [6, 0, 0, 2];
		var v_array_29: array<int> := new int[5] [-18, 24, 9, 18, 4];
		var v_map_24: map<bool, bool> := v_map_1;
		var v_bool_7: bool := v_bool_1;
		var v_seq_35: seq<bool> := [false, false, true];
		var v_seq_36: seq<bool> := v_seq_35;
		var v_int_82: int := 17;
		var v_int_83: int := safe_index_seq(v_seq_36, v_int_82);
		var v_int_84: int := v_int_83;
		var v_seq_37: seq<bool> := (if ((|v_seq_35| > 0)) then (v_seq_35[v_int_84 := true]) else (v_seq_35));
		var v_int_85: int := (if (false) then (0) else (17));
		var v_DT_3_2_1: DT_3<map<real, real>> := DT_3_2;
		var v_DT_3_2_2: DT_3<map<real, real>> := DT_3_2;
		var v_DT_3_2_3: DT_3<map<real, real>> := DT_3_2;
		var v_char_10: char, v_int_bool_8: (int, bool), v_DT_1_4_23: DT_1<int, char>, v_map_25: map<bool, array<int>>, v_bool_8: bool := (match 'c' {
			case _ => (match -14.47 {
				case _ => (if ((v_bool_5 in v_map_19)) then (v_map_19[v_bool_5]) else ('m'))
			})
		}), (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_79]) else (v_int_bool_1)), (if ((v_char_9 in v_map_23)) then (v_map_23[v_char_9]) else ((if ((if (false) then (false) else (false))) then ((if ((v_char_8 in v_map_22)) then (v_map_22[v_char_8]) else (v_DT_1_4_20))) else ((if (false) then (v_DT_1_4_21) else (v_DT_1_4_22)))))), (if ((|v_seq_34| > 0)) then (v_seq_34[v_int_81]) else ((if (true) then (map[true := v_array_19, true := v_array_20, true := v_array_21, false := v_array_22, false := v_array_23]) else (map[true := v_array_24, true := v_array_25, true := v_array_26, true := v_array_27]))[(if (false) then (false) else (true)) := (match 1 {
			case _ => v_array_29
		})])), (if ((v_bool_7 in v_map_24)) then (v_map_24[v_bool_7]) else ((if ((|v_seq_37| > 0)) then (v_seq_37[v_int_85]) else (({v_DT_3_2_1, v_DT_3_2_2} < {v_DT_3_2_3})))));
		return ;
	}
	var v_int_86: int := v_int_39;
	var v_bool_int_1: (bool, int) := (false, 19);
	var v_int_real_bool_int_1: (int, real, (bool, int)) := (6, -24.08, v_bool_int_1);
	var v_bool_int_2: (bool, int) := (true, 21);
	var v_int_real_bool_int_2: (int, real, (bool, int)) := (29, -19.73, v_bool_int_2);
	var v_bool_int_3: (bool, int) := (true, 20);
	var v_int_real_bool_int_3: (int, real, (bool, int)) := (19, -15.06, v_bool_int_3);
	var v_bool_int_4: (bool, int) := (true, 3);
	var v_int_real_bool_int_4: (int, real, (bool, int)) := (4, 19.19, v_bool_int_4);
	var v_bool_int_5: (bool, int) := (true, 3);
	var v_int_real_bool_int_5: (int, real, (bool, int)) := (27, 11.06, v_bool_int_5);
	var v_map_27: map<(int, real, (bool, int)), int> := (match 25 {
		case -9 => map[v_int_real_bool_int_1 := 5]
		case _ => map[v_int_real_bool_int_2 := 0, v_int_real_bool_int_3 := 26, v_int_real_bool_int_4 := 9, v_int_real_bool_int_5 := 7]
	});
	var v_bool_int_6: (bool, int) := (false, -3);
	var v_int_real_bool_int_6: (int, real, (bool, int)) := (5, 15.86, v_bool_int_6);
	var v_bool_int_7: (bool, int) := (true, 24);
	var v_int_real_bool_int_7: (int, real, (bool, int)) := (14, -4.00, v_bool_int_7);
	var v_bool_int_8: (bool, int) := (true, 5);
	var v_int_real_bool_int_8: (int, real, (bool, int)) := (0, 4.83, v_bool_int_8);
	var v_int_real_bool_int_9: (int, real, (bool, int)) := (match 27 {
		case 8 => v_int_real_bool_int_6
		case -3 => v_int_real_bool_int_7
		case _ => v_int_real_bool_int_8
	});
	var v_map_26: map<int, int> := map[-11 := 27, 11 := 12, -27 := -28];
	var v_int_88: int := 20;
	var v_int_87: int := (match 'x' {
		case 'e' => v_int_42
		case _ => (if ((v_int_real_bool_int_9 in v_map_27)) then (v_map_27[v_int_real_bool_int_9]) else ((if ((v_int_88 in v_map_26)) then (v_map_26[v_int_88]) else (10))))
	});
	while (v_int_86 < v_int_87) 
		decreases v_int_87 - v_int_86;
		invariant (v_int_86 <= v_int_87) && ((((v_int_86 == 18)) ==> ((((v_bool_1 == false))))));
	{
		v_int_86 := (v_int_86 + 1);
		match v_char_6 {
			case _ => {
				var v_seq_38: seq<seq<int>> := [[2, 28], [9, 26, 27, 17], [29, 3, 20, 29]];
				var v_int_91: int := 0;
				var v_seq_39: seq<int> := (if ((|v_seq_38| > 0)) then (v_seq_38[v_int_91]) else ([]));
				var v_seq_40: seq<int> := (if ((|v_seq_39| > 0)) then (v_seq_39[(if (true) then (29) else (10))..(5 * 24)]) else (v_seq_39));
				var v_int_92: int := (match 12 {
					case _ => (if (false) then (29) else (21))
				});
				var v_int_89: int := (if ((|v_seq_40| > 0)) then (v_seq_40[v_int_92]) else (v_int_43));
				var v_int_90: int := v_int_38;
				while (v_int_89 < v_int_90) 
					decreases v_int_90 - v_int_89;
					invariant (v_int_89 <= v_int_90);
				{
					v_int_89 := (v_int_89 + 1);
					var v_seq_41: seq<seq<set<bool>>> := [[{}, {true, true, false}, {false}, {true}], [{false, false, true, false}, {}, {}, {true, false, false, false}], [{false}], [{false, false}, {true}]];
					var v_int_93: int := 6;
					var v_seq_42: seq<set<bool>> := (if ((|v_seq_41| > 0)) then (v_seq_41[v_int_93]) else ([{false, false, false}]));
					var v_int_94: int := (if (false) then (20) else (28));
					var v_map_28: map<bool, set<bool>> := map[true := {true}, false := {true, false}, false := {true, true, true}, true := {true, true, false, true}, true := {false}];
					var v_bool_9: bool := true;
					match ((match false {
						case _ => ({true, false, false, true} - {})
					}) !! (if ((|v_seq_42| > 0)) then (v_seq_42[v_int_94]) else ((if ((v_bool_9 in v_map_28)) then (v_map_28[v_bool_9]) else ({}))))) {
						case _ => {
							return ;
						}
						
					}
					
					var v_seq_43: seq<map<bool, bool>> := [map[false := false, false := false], map[false := false, true := true, false := true, true := false, false := false], map[true := false, false := false], map[false := false, true := true, false := true, false := true]];
					var v_int_95: int := 27;
					var v_map_29: map<bool, bool> := (if ((|v_seq_43| > 0)) then (v_seq_43[v_int_95]) else (map[true := false, false := true, false := false, true := true, false := true]));
					var v_bool_10: bool := v_bool_9;
					var v_seq_44: seq<bool> := [true];
					var v_int_96: int := 19;
					var v_seq_45: seq<bool> := [true, false];
					var v_int_97: int := 0;
					var v_map_30: map<bool, bool> := map[true := true];
					var v_bool_11: bool := false;
					var v_seq_46: seq<bool> := [false, true];
					var v_int_98: int := 24;
					var v_map_31: map<bool, map<bool, bool>> := map[false := map[false := false], false := map[false := true, true := false, false := true], false := map[false := true, true := true, false := false, true := false, true := false]][true := map[true := true, true := true, false := true, false := true, false := true]];
					var v_bool_12: bool := (if (true) then (false) else (true));
					var v_map_33: map<bool, bool> := (if ((v_bool_12 in v_map_31)) then (v_map_31[v_bool_12]) else (map[false := false, false := false, true := true][true := false]));
					var v_map_32: map<bool, bool> := map[true := false, false := true, true := true, false := false, false := true];
					var v_bool_13: bool := true;
					var v_bool_14: bool := (v_bool_11 <==> (if ((v_bool_13 in v_map_32)) then (v_map_32[v_bool_13]) else (false)));
					var v_seq_47: seq<bool> := [];
					var v_int_99: int := 8;
					var v_seq_48: seq<bool> := [false];
					var v_int_100: int := 8;
					v_bool_1, v_bool_11, v_bool_10, v_bool_14 := (if (v_bool_1) then ((if ((v_bool_10 in v_map_29)) then (v_map_29[v_bool_10]) else ((if ((|v_seq_44| > 0)) then (v_seq_44[v_int_96]) else (false))))) else ((match false {
						case _ => (false && true)
					}))), (if (v_bool_10) then ((if ((multiset({false, false, true, true}) == multiset{})) then (v_bool_9) else ((if ((v_bool_11 in v_map_30)) then (v_map_30[v_bool_11]) else (false))))) else (((if ((|v_seq_46| > 0)) then (v_seq_46[v_int_98]) else (false)) !in ({false} * {true})))), (if ((v_bool_14 in v_map_33)) then (v_map_33[v_bool_14]) else (((if ((|v_seq_47| > 0)) then (v_seq_47[v_int_99]) else (false)) <== v_bool_13))), (match false {
						case _ => (match false {
							case _ => (false !in map[false := false, true := false, false := false, false := true])
						})
					});
					break;
				}
				assert true;
				expect true;
			}
			
		}
		
		assert true;
		expect true;
		var v_seq_49: seq<map<bool, bool>> := [map[false := false, true := true, true := false, true := false]];
		var v_int_101: int := 5;
		var v_map_34: map<bool, bool> := (if ((|v_seq_49| > 0)) then (v_seq_49[v_int_101]) else (map[true := false, true := true, false := true, true := true, true := true]));
		var v_seq_50: seq<bool> := [false, true, true];
		var v_int_102: int := 20;
		var v_bool_15: bool := (if ((|v_seq_50| > 0)) then (v_seq_50[v_int_102]) else (false));
		var v_seq_51: seq<bool> := [];
		var v_int_103: int := 21;
		var v_map_35: map<bool, bool> := map[true := false, true := true, false := true, false := false, false := false][true := false];
		var v_bool_16: bool := (match false {
			case _ => false
		});
		var v_map_36: map<int, bool> := (map[5 := true, 14 := true] - {28, 28});
		var v_int_105: int := (match 23 {
			case _ => 2
		});
		var v_seq_52: seq<bool> := [];
		var v_int_104: int := 6;
		if (if ((if ((v_bool_15 in v_map_34)) then (v_map_34[v_bool_15]) else ((if ((|v_seq_51| > 0)) then (v_seq_51[v_int_103]) else (true))))) then ((if ((v_bool_16 in v_map_35)) then (v_map_35[v_bool_16]) else (v_bool_15))) else ((if ((v_int_105 in v_map_36)) then (v_map_36[v_int_105]) else ((if ((|v_seq_52| > 0)) then (v_seq_52[v_int_104]) else (true)))))) {
			return ;
		} else {
			
		}
		var v_map_38: map<int, int> := map[28 := 8, -26 := 25, 8 := 12][24 := 26];
		var v_map_37: map<int, int> := map[8 := 17, 13 := 19, 22 := 1];
		var v_int_107: int := 21;
		var v_int_108: int := (if ((v_int_107 in v_map_37)) then (v_map_37[v_int_107]) else (0));
		var v_seq_53: seq<int> := [19, 28, 14, 9];
		var v_seq_55: seq<int> := (if ((|v_seq_53| > 0)) then (v_seq_53[25..-11]) else (v_seq_53));
		var v_seq_54: seq<int> := [25];
		var v_int_109: int := 14;
		var v_int_110: int := (if ((|v_seq_54| > 0)) then (v_seq_54[v_int_109]) else (27));
		var v_seq_56: seq<map<int, int>> := [];
		var v_seq_57: seq<map<int, int>> := (if ((|v_seq_56| > 0)) then (v_seq_56[8..6]) else (v_seq_56));
		var v_int_111: int := (5 * 17);
		var v_map_40: map<int, int> := (if ((|v_seq_57| > 0)) then (v_seq_57[v_int_111]) else ((map[-23 := 16, 7 := 16, 2 := 9] + map[27 := 18])));
		var v_seq_58: seq<int> := [4];
		var v_int_112: int := 26;
		var v_int_118: int := ((if ((|v_seq_58| > 0)) then (v_seq_58[v_int_112]) else (22)) % (match 28 {
			case _ => 28
		}));
		var v_seq_59: seq<int> := [20, 7, 20];
		var v_seq_60: seq<int> := v_seq_59;
		var v_int_113: int := 22;
		var v_int_114: int := safe_index_seq(v_seq_60, v_int_113);
		var v_int_115: int := v_int_114;
		var v_seq_61: seq<int> := (if ((|v_seq_59| > 0)) then (v_seq_59[v_int_115 := 17]) else (v_seq_59));
		var v_map_39: map<int, int> := map[-27 := 3, 21 := 22, 11 := 0, 10 := 3, 0 := 23];
		var v_int_116: int := 16;
		var v_int_117: int := (if ((v_int_116 in v_map_39)) then (v_map_39[v_int_116]) else (23));
		var v_int_154: int, v_int_155: int := ((if ((v_int_108 in v_map_38)) then (v_map_38[v_int_108]) else (v_int_107)) + (if ((|v_seq_55| > 0)) then (v_seq_55[v_int_110]) else (v_int_101))), (if ((v_int_118 in v_map_40)) then (v_map_40[v_int_118]) else ((if ((|v_seq_61| > 0)) then (v_seq_61[v_int_117]) else ((16 - 18)))));
		for v_int_106 := v_int_154 to v_int_155 
			invariant (v_int_155 - v_int_106 >= 0)
		{
			assert true;
			expect true;
			var v_seq_62: seq<int> := [8, 18, 7];
			var v_seq_63: seq<int> := (match 14 {
				case _ => ([16, 17, 20, 7] + [4, 13])
			});
			var v_int_119: int := (match 14 {
				case _ => (if (false) then (6) else (20))
			});
			var v_seq_64: seq<int> := ([9, -1] + [28, 20, 23, 16]);
			var v_int_120: int := (if (true) then (25) else (12));
			var v_map_41: map<int, int> := map[28 := 8, 14 := 17, 22 := 7];
			var v_int_121: int := 8;
			var v_seq_65: seq<int> := [];
			var v_int_122: int := 13;
			var v_int_bool_int_1: (int, bool, int) := (12, false, 13);
			var v_int_int_bool_int_1: (int, (int, bool, int)) := (18, v_int_bool_int_1);
			var v_int_bool_int_2: (int, bool, int) := (15, false, 3);
			var v_int_int_bool_int_2: (int, (int, bool, int)) := (17, v_int_bool_int_2);
			var v_int_bool_int_3: (int, bool, int) := (21, false, 3);
			var v_int_int_bool_int_3: (int, (int, bool, int)) := (14, v_int_bool_int_3);
			var v_int_bool_int_4: (int, bool, int) := (12, false, 24);
			var v_int_int_bool_int_4: (int, (int, bool, int)) := (27, v_int_bool_int_4);
			var v_map_42: map<(int, (int, bool, int)), int> := map[v_int_int_bool_int_1 := 7, v_int_int_bool_int_2 := 18, v_int_int_bool_int_3 := -22, v_int_int_bool_int_4 := 15];
			var v_int_bool_int_5: (int, bool, int) := (23, true, 8);
			var v_int_int_bool_int_5: (int, (int, bool, int)) := (15, v_int_bool_int_5);
			var v_int_int_bool_int_6: (int, (int, bool, int)) := v_int_int_bool_int_5;
			var v_seq_66: seq<int> := ([3, 2, 10] + [15, 27, 23, 15]);
			var v_int_bool_real_1: (int, bool, real) := (26, false, 13.30);
			var v_bool_real_bool_1: (bool, real, bool) := (false, 14.32, true);
			var v_int_int_bool_real_bool_real_bool_1: (int, (int, bool, real), (bool, real, bool)) := (0, v_int_bool_real_1, v_bool_real_bool_1);
			var v_map_43: map<(int, (int, bool, real), (bool, real, bool)), int> := map[v_int_int_bool_real_bool_real_bool_1 := 8];
			var v_int_bool_real_2: (int, bool, real) := (10, false, -22.15);
			var v_bool_real_bool_2: (bool, real, bool) := (false, -6.65, false);
			var v_int_int_bool_real_bool_real_bool_2: (int, (int, bool, real), (bool, real, bool)) := (9, v_int_bool_real_2, v_bool_real_bool_2);
			var v_int_int_bool_real_bool_real_bool_3: (int, (int, bool, real), (bool, real, bool)) := v_int_int_bool_real_bool_real_bool_2;
			var v_int_123: int := (if ((v_int_int_bool_real_bool_real_bool_3 in v_map_43)) then (v_map_43[v_int_int_bool_real_bool_real_bool_3]) else (12));
			var v_int_int_1: (int, int) := (11, 17);
			var v_DT_4_3_1: DT_4 := DT_4_3(29, 7.27, 5, false);
			var v_int_int_DT_4_3_set_1: ((int, int), DT_4, set<real>) := (v_int_int_1, v_DT_4_3_1, {-2.01});
			var v_int_int_2: (int, int) := (14, 21);
			var v_DT_4_3_2: DT_4 := DT_4_3(3, 10.18, 3, true);
			var v_int_int_DT_4_3_set_2: ((int, int), DT_4, set<real>) := (v_int_int_2, v_DT_4_3_2, {0.60});
			var v_int_int_3: (int, int) := (17, -29);
			var v_DT_4_3_3: DT_4 := DT_4_3(2, -19.12, 9, true);
			var v_int_int_DT_4_3_set_3: ((int, int), DT_4, set<real>) := (v_int_int_3, v_DT_4_3_3, {-9.59, 13.20});
			var v_map_44: map<((int, int), DT_4, set<real>), int> := map[v_int_int_DT_4_3_set_1 := 20, v_int_int_DT_4_3_set_2 := 28, v_int_int_DT_4_3_set_3 := 9];
			var v_int_int_4: (int, int) := (24, 9);
			var v_DT_4_3_4: DT_4 := DT_4_3(-23, 23.76, 8, false);
			var v_int_int_DT_4_3_set_4: ((int, int), DT_4, set<real>) := (v_int_int_4, v_DT_4_3_4, {});
			var v_int_int_DT_4_3_set_5: ((int, int), DT_4, set<real>) := v_int_int_DT_4_3_set_4;
			var v_real_bool_bool_1: (real, bool, bool) := (26.02, false, false);
			var v_real_bool_bool_2: (real, bool, bool) := (-22.12, false, true);
			var v_real_bool_bool_3: (real, bool, bool) := (28.10, true, true);
			v_int_101, v_int_104 := (if ((|v_seq_63| > 0)) then (v_seq_63[v_int_119]) else ((if ((|v_seq_64| > 0)) then (v_seq_64[v_int_120]) else ((if ((v_int_121 in v_map_41)) then (v_map_41[v_int_121]) else (15)))))), (match 25 {
				case _ => (if ((false == true)) then (|{[v_real_bool_bool_1, v_real_bool_bool_2], [v_real_bool_bool_3]}|) else ((match false {
					case _ => 22
				})))
			});
			match v_bool_1 {
				case _ => {
					var v_seq_71: seq<int> := [23, 15];
					var v_seq_72: seq<int> := v_seq_71;
					var v_int_131: int := 2;
					var v_int_132: int := safe_index_seq(v_seq_72, v_int_131);
					var v_int_133: int := v_int_132;
					var v_seq_73: seq<int> := (if ((|v_seq_71| > 0)) then (v_seq_71[v_int_133 := 10]) else (v_seq_71));
					var v_seq_75: seq<int> := (if ((|v_seq_73| > 0)) then (v_seq_73[(if (true) then (6) else (16))..0]) else (v_seq_73));
					var v_map_52: map<bool, int> := map[false := 12, true := 16][false := 4];
					var v_seq_74: seq<bool> := [true, true, false];
					var v_int_134: int := 20;
					var v_bool_24: bool := (if ((|v_seq_74| > 0)) then (v_seq_74[v_int_134]) else (false));
					var v_map_51: map<bool, int> := map[true := 21];
					var v_bool_23: bool := true;
					var v_int_135: int := (if ((v_bool_24 in v_map_52)) then (v_map_52[v_bool_24]) else ((if ((v_bool_23 in v_map_51)) then (v_map_51[v_bool_23]) else (24))));
					var v_seq_76: seq<int> := [10];
					var v_seq_77: seq<int> := (if ((|v_seq_76| > 0)) then (v_seq_76[-3..-18]) else (v_seq_76));
					var v_int_136: int := (match false {
						case _ => 16
					});
					var v_seq_78: seq<int> := [];
					var v_int_137: int := 21;
					var v_seq_79: seq<bool> := [];
					var v_seq_80: seq<bool> := v_seq_79;
					var v_int_138: int := 11;
					var v_int_139: int := safe_index_seq(v_seq_80, v_int_138);
					var v_int_140: int := v_int_139;
					var v_seq_81: seq<bool> := (if ((|v_seq_79| > 0)) then (v_seq_79[v_int_140 := false]) else (v_seq_79));
					var v_int_141: int := v_int_41;
					var v_seq_82: seq<int> := [12];
					var v_int_142: int := 26;
					var v_seq_83: seq<int> := [9, 22, 11, -17];
					var v_int_143: int := 10;
					var v_seq_84: seq<int> := [2, -28, -28, 14];
					var v_seq_85: seq<int> := (if ((|v_seq_84| > 0)) then (v_seq_84[9..18]) else (v_seq_84));
					var v_int_144: int := (match 'b' {
						case _ => 2
					});
					var v_map_53: map<set<int>, int> := map[{20} := 18, {2, 4} := -11, {8} := 10];
					var v_set_5: set<int> := {29, 21, 12};
					var v_int_145: int, v_int_146: int := (if ((|v_seq_75| > 0)) then (v_seq_75[v_int_135]) else ((if ((|v_seq_77| > 0)) then (v_seq_77[v_int_136]) else ((if ((|v_seq_78| > 0)) then (v_seq_78[v_int_137]) else (19)))))), (if ((if ((|v_seq_81| > 0)) then (v_seq_81[v_int_141]) else ((false || false)))) then ((if ((multiset({map[true := 9, false := 22, false := 26, true := 23, false := 6], map[false := 16], map[false := 6, false := -9, false := 17, false := 27]}) == multiset{map[true := 21, true := 26]})) then ((if ((|v_seq_82| > 0)) then (v_seq_82[v_int_142]) else (15))) else ((if ((|v_seq_83| > 0)) then (v_seq_83[v_int_143]) else (0))))) else ((if ((|v_seq_85| > 0)) then (v_seq_85[v_int_144]) else ((if ((v_set_5 in v_map_53)) then (v_map_53[v_set_5]) else (22))))));
					for v_int_130 := v_int_145 to v_int_146 
						invariant (v_int_146 - v_int_130 >= 0)
					{
						
					}
					var v_seq_86: seq<bool> := [true, true];
					var v_seq_87: seq<bool> := v_seq_86;
					var v_int_147: int := -10;
					var v_int_148: int := safe_index_seq(v_seq_87, v_int_147);
					var v_int_149: int := v_int_148;
					var v_seq_88: seq<bool> := (if ((|v_seq_86| > 0)) then (v_seq_86[v_int_149 := false]) else (v_seq_86));
					var v_seq_89: seq<bool> := v_seq_88;
					var v_int_150: int := (match false {
						case _ => 8
					});
					var v_int_151: int := safe_index_seq(v_seq_89, v_int_150);
					var v_int_152: int := v_int_151;
					var v_DT_3_1_5: DT_3<array<real>> := DT_3_1;
					var v_DT_3_1_6: DT_3<array<real>> := DT_3_1;
					var v_DT_3_1_7: DT_3<array<real>> := DT_3_1;
					var v_map_54: map<DT_3<array<real>>, bool> := map[v_DT_3_1_5 := false, v_DT_3_1_6 := false, v_DT_3_1_7 := true];
					var v_DT_3_1_8: DT_3<array<real>> := DT_3_1;
					var v_DT_3_1_9: DT_3<array<real>> := v_DT_3_1_8;
					var v_seq_90: seq<bool> := (if ((|v_seq_88| > 0)) then (v_seq_88[v_int_152 := (if ((v_DT_3_1_9 in v_map_54)) then (v_map_54[v_DT_3_1_9]) else (false))]) else (v_seq_88));
					var v_int_real_12: (int, real) := (3, 6.08);
					var v_map_55: map<(int, real), int> := map[v_int_real_12 := 28];
					var v_int_real_13: (int, real) := (25, 9.56);
					var v_int_real_14: (int, real) := v_int_real_13;
					var v_int_153: int := (match 'I' {
						case _ => v_int_138
					});
					if (if ((|v_seq_90| > 0)) then (v_seq_90[v_int_153]) else (v_bool_16)) {
						return ;
					}
					continue;
				}
				
			}
			
		}
	}
	assert ((v_char_6 == 'U'));
	expect ((v_char_6 == 'U'));
	var v_int_156: int := v_int_7;
	var v_map_56: map<int, int> := map[19 := 0, 26 := 8, 13 := 0, 17 := 2, 9 := 14][19 := 15];
	var v_int_158: int := (1 * 21);
	var v_array_35: array<int> := new int[4] [22, 17, 2, 20];
	var v_int_157: int := (match 4 {
		case 14 => v_int_41
		case _ => (if ((v_int_158 in v_map_56)) then (v_map_56[v_int_158]) else (v_array_35.Length))
	});
	while (v_int_156 < v_int_157) 
		decreases v_int_157 - v_int_156;
		invariant (v_int_156 <= v_int_157) && ((((v_int_156 == 0)) ==> ((((v_char_6 == 'U'))))));
	{
		v_int_156 := (v_int_156 + 1);
		var v_seq_91: seq<real> := [-29.92, 1.99, 1.03];
		var v_int_160: int := -27;
		var v_seq_219: seq<real> := v_seq_91;
		var v_int_341: int := v_int_160;
		var v_int_342: int := safe_index_seq(v_seq_219, v_int_341);
		v_int_160 := v_int_342;
		var v_seq_93: seq<int> := v_seq_7;
		var v_seq_92: seq<int> := [12];
		var v_int_161: int := 3;
		var v_seq_218: seq<int> := v_seq_92;
		var v_int_339: int := v_int_161;
		var v_int_340: int := safe_index_seq(v_seq_218, v_int_339);
		v_int_161 := v_int_340;
		var v_int_162: int := (if ((|v_seq_92| > 0)) then (v_seq_92[v_int_161]) else (11));
		var v_seq_220: seq<int> := v_seq_93;
		var v_int_343: int := v_int_162;
		var v_int_344: int := safe_index_seq(v_seq_220, v_int_343);
		v_int_162 := v_int_344;
		var v_seq_94: seq<real> := [];
		var v_seq_95: seq<real> := v_seq_94;
		var v_int_163: int := 21;
		var v_int_164: int := safe_index_seq(v_seq_95, v_int_163);
		var v_int_165: int := v_int_164;
		var v_seq_97: seq<real> := (if ((|v_seq_94| > 0)) then (v_seq_94[v_int_165 := 15.92]) else (v_seq_94));
		var v_seq_96: seq<int> := [];
		var v_int_166: int := 5;
		var v_int_167: int := (if ((|v_seq_96| > 0)) then (v_seq_96[v_int_166]) else (17));
		var v_int_256: int, v_int_257: int := (((if ((|v_seq_91| > 0)) then (v_seq_91[v_int_160]) else (11.98))).Floor / (if ((|v_seq_93| > 0)) then (v_seq_93[v_int_162]) else (v_int_162))), ((if ((|v_seq_97| > 0)) then (v_seq_97[v_int_167]) else ((match -7 {
			case 16 => 0.05
			case -5 => -2.22
			case _ => 21.82
		})))).Floor;
		for v_int_159 := v_int_256 to v_int_257 
			invariant (v_int_257 - v_int_159 >= 0) && ((((v_int_159 == -3)) ==> ((((v_char_6 == 'U'))))))
		{
			var v_seq_98: seq<array<int>> := [];
			var v_seq_99: seq<array<int>> := v_seq_98;
			var v_int_169: int := 0;
			var v_int_170: int := safe_index_seq(v_seq_99, v_int_169);
			var v_int_171: int := v_int_170;
			var v_array_36: array<int> := new int[5] [8, 14, 21, 0, 10];
			var v_seq_100: seq<array<int>> := (if ((|v_seq_98| > 0)) then (v_seq_98[v_int_171 := v_array_36]) else (v_seq_98));
			var v_int_172: int := v_array_36[2];
			var v_array_37: array<int> := new int[4] [10, 23, 2, 23];
			var v_array_38: array<int> := new int[3] [26, 3, 20];
			var v_seq_101: seq<int> := [-6, 17, -26];
			var v_int_173: int := 11;
			var v_map_58: map<int, int> := map[7 := 26, 10 := 23, 28 := 2, 15 := 1][4 := 27];
			var v_map_57: map<int, int> := map[5 := 12];
			var v_int_174: int := 6;
			var v_int_175: int := (if ((v_int_174 in v_map_57)) then (v_map_57[v_int_174]) else (-23));
			var v_int_212: int, v_int_213: int := (if ((|v_seq_100| > 0)) then (v_seq_100[v_int_172]) else ((match 3 {
				case 25 => v_array_37
				case _ => v_array_38
			}))).Length, (if ((match 7 {
				case 17 => (19 >= 10)
				case _ => (match 27 {
					case 29 => true
					case _ => false
				})
			})) then ((match 6 {
				case _ => (if (false) then (11) else (20))
			})) else ((if ((v_int_175 in v_map_58)) then (v_map_58[v_int_175]) else (v_int_44))));
			for v_int_168 := v_int_212 downto v_int_213 
				invariant (v_int_168 - v_int_213 >= 0) && ((((v_int_168 == 2)) ==> ((((v_int_174 == 6)) && ((v_int_172 == 21))))))
			{
				var v_map_59: map<int, int> := map[13 := 6, 14 := 25, 21 := 25, 15 := 25];
				var v_int_176: int := 16;
				var v_map_60: map<int, int> := map[27 := 25];
				var v_int_177: int := 13;
				var v_map_61: map<seq<int>, bool> := map[[17, 26] := false, [16] := false, [20, 28] := false];
				var v_seq_102: seq<int> := [9, 1];
				var v_map_62: map<int, int> := map[2 := 6, -11 := 2, 0 := 25];
				var v_int_178: int := 7;
				var v_array_39: array<int> := new int[3] [3, 19, 29];
				var v_array_40: array<int> := new int[5];
				v_array_40[0] := 2;
				v_array_40[1] := 29;
				v_array_40[2] := 0;
				v_array_40[3] := 7;
				v_array_40[4] := 22;
				var v_seq_103: seq<int> := [];
				var v_seq_104: seq<int> := [];
				var v_seq_105: seq<int> := v_seq_104;
				var v_int_179: int := 7;
				var v_int_180: int := safe_index_seq(v_seq_105, v_int_179);
				var v_int_181: int := v_int_180;
				var v_seq_106: seq<int> := ((if ((|v_seq_103| > 0)) then (v_seq_103[19..6]) else (v_seq_103)) + (if ((|v_seq_104| > 0)) then (v_seq_104[v_int_181 := 11]) else (v_seq_104)));
				var v_int_182: int := ((match 25 {
					case 10 => 13
					case _ => 23
				}) * (20.95).Floor);
				var v_seq_107: seq<int> := [0, 18, 0, 17];
				var v_int_183: int := 8;
				var v_seq_221: seq<int> := v_seq_107;
				var v_int_345: int := v_int_183;
				var v_int_346: int := safe_index_seq(v_seq_221, v_int_345);
				v_int_183 := v_int_346;
				var v_map_63: map<int, map<int, bool>> := map[8 := map[4 := false, 28 := true, 0 := false], 18 := map[3 := true, 5 := false, 6 := true], 15 := map[29 := false, -1 := false, 10 := true, 6 := true], -20 := map[10 := false, 24 := false]];
				var v_int_184: int := 24;
				var v_map_65: map<int, bool> := (if ((v_int_184 in v_map_63)) then (v_map_63[v_int_184]) else (map[10 := false, 14 := false, 20 := true, 28 := false, 9 := false]));
				var v_map_64: map<int, int> := map[9 := 14, 28 := 14, 25 := 4];
				var v_int_185: int := 16;
				var v_int_186: int := (if ((v_int_185 in v_map_64)) then (v_map_64[v_int_185]) else (22));
				var v_seq_108: seq<int> := [];
				var v_seq_109: seq<int> := v_seq_108;
				var v_int_187: int := 7;
				var v_int_188: int := safe_index_seq(v_seq_109, v_int_187);
				var v_int_189: int := v_int_188;
				var v_seq_110: seq<int> := (if ((|v_seq_108| > 0)) then (v_seq_108[v_int_189 := 18]) else (v_seq_108));
				var v_int_190: int := (if (true) then (-22) else (11));
				var v_array_41: array<int> := new int[3] [16, 16, 24];
				var v_array_42: array<int> := new int[4] [-12, -14, 9, 11];
				var v_array_43: array<int> := new int[3] [9, 27, 24];
				var v_array_44: array<int> := new int[4] [-19, 21, 18, 2];
				var v_array_45: array<int> := new int[3] [22, 11, 0];
				var v_array_46: array<int> := new int[4] [16, 19, 22, 13];
				var v_map_66: map<int, array<int>> := map[27 := v_array_42, 17 := v_array_43, 14 := v_array_44, 29 := v_array_45];
				var v_int_191: int := 8;
				var v_array_47: array<int> := new int[4];
				v_array_47[0] := 24;
				v_array_47[1] := 24;
				v_array_47[2] := 17;
				v_array_47[3] := -4;
				var v_array_48: array<map<bool, seq<bool>>> := new map<bool, seq<bool>>[3] [map[true := [false, false, true]], map[true := [false, true], false := [false]], map[false := [false]]];
				var v_array_49: array<map<bool, seq<bool>>> := new map<bool, seq<bool>>[4];
				v_array_49[0] := map[true := [false, true, true, true]];
				v_array_49[1] := map[false := [false], true := []];
				v_array_49[2] := map[false := [], true := [false]];
				v_array_49[3] := map[false := [true, true], true := [true]];
				v_int_174, v_int_172, v_int_188, v_array_45[2], v_array_41[2] := (match 4 {
					case 0 => ((if ((v_int_176 in v_map_59)) then (v_map_59[v_int_176]) else (5)) + (if ((v_int_177 in v_map_60)) then (v_map_60[v_int_177]) else (6)))
					case 26 => (if ((if ((v_seq_102 in v_map_61)) then (v_map_61[v_seq_102]) else (true))) then ((if ((v_int_178 in v_map_62)) then (v_map_62[v_int_178]) else (17))) else ((7 / 4)))
					case _ => (match 1 {
						case 23 => v_array_39
						case _ => v_array_40
					}).Length
				}), (v_real_2).Floor, (if ((|v_seq_106| > 0)) then (v_seq_106[v_int_182]) else ((match -25 {
					case 8 => (match 14 {
						case _ => 14
					})
					case 13 => (if (true) then (16) else (22))
					case _ => (if ((|v_seq_107| > 0)) then (v_seq_107[v_int_183]) else (16))
				}))), (if ((if ((v_int_186 in v_map_65)) then (v_map_65[v_int_186]) else ((match 1 {
					case 29 => true
					case 3 => false
					case _ => false
				})))) then ((if ((|v_seq_110| > 0)) then (v_seq_110[v_int_190]) else (v_array_41.Length))) else ((if ((v_int_191 in v_map_66)) then (v_map_66[v_int_191]) else (v_array_47)).Length)), (if (v_bool_1) then ((if (false) then (v_array_48) else (v_array_49)).Length) else ((match true {
					case false => v_array_46[3]
					case _ => (23 - 17)
				})));
				var v_seq_111: seq<bool> := [true, false, true, false];
				var v_int_192: int := 5;
				var v_seq_222: seq<bool> := v_seq_111;
				var v_int_347: int := v_int_192;
				var v_int_348: int := safe_index_seq(v_seq_222, v_int_347);
				v_int_192 := v_int_348;
				var v_map_69: map<char, bool> := map['L' := true, 'B' := true]['u' := false][(if (true) then ('Q') else ('b')) := (if ((|v_seq_111| > 0)) then (v_seq_111[v_int_192]) else (false))];
				var v_char_11: char := (match 'a' {
					case 'Q' => v_char_6
					case 'n' => (if (false) then ('X') else ('M'))
					case _ => (match 'y' {
						case 'z' => 'u'
						case _ => 'V'
					})
				});
				var v_seq_112: seq<map<bool, bool>> := [map[false := false, true := false], map[false := false, true := false], map[false := false, true := true]];
				var v_int_193: int := 19;
				var v_seq_223: seq<map<bool, bool>> := v_seq_112;
				var v_int_349: int := v_int_193;
				var v_int_350: int := safe_index_seq(v_seq_223, v_int_349);
				v_int_193 := v_int_350;
				var v_map_68: map<bool, bool> := (if ((|v_seq_112| > 0)) then (v_seq_112[v_int_193]) else (map[false := true]));
				var v_bool_25: bool := (8.32 < -29.87);
				var v_map_67: map<int, bool> := map[28 := true, 20 := true, -19 := false, 16 := true];
				var v_int_194: int := 12;
				if (if ((v_char_11 in v_map_69)) then (v_map_69[v_char_11]) else ((if ((v_bool_25 in v_map_68)) then (v_map_68[v_bool_25]) else ((if ((v_int_194 in v_map_67)) then (v_map_67[v_int_194]) else (true)))))) {
					return ;
				}
				var v_seq_113: seq<int> := [];
				var v_int_196: int := 5;
				var v_map_73: map<int, int> := v_map_64[(if ((|v_seq_113| > 0)) then (v_seq_113[v_int_196]) else (12)) := v_int_156];
				var v_map_71: map<int, int> := map[20 := 0, 8 := 29, 19 := 11][16 := 9];
				var v_int_198: int := (match 29 {
					case 28 => -2
					case 14 => 1
					case _ => 13
				});
				var v_map_70: map<int, int> := map[20 := 19, 6 := 16, 9 := 4];
				var v_int_197: int := 20;
				var v_int_202: int := (if ((v_int_198 in v_map_71)) then (v_map_71[v_int_198]) else ((if ((v_int_197 in v_map_70)) then (v_map_70[v_int_197]) else (5))));
				var v_map_72: map<int, int> := map[7 := 24, 6 := 2, 9 := 14, 10 := 24, 11 := 12][7 := 13];
				var v_seq_114: seq<int> := [9, 19];
				var v_int_199: int := 18;
				var v_seq_224: seq<int> := v_seq_114;
				var v_int_351: int := v_int_199;
				var v_int_352: int := safe_index_seq(v_seq_224, v_int_351);
				v_int_199 := v_int_352;
				var v_int_201: int := (if ((|v_seq_114| > 0)) then (v_seq_114[v_int_199]) else (26));
				var v_seq_115: seq<int> := [14, 21, 22];
				var v_int_200: int := 15;
				var v_map_74: map<int, map<int, int>> := map[12 := map[14 := 8, 27 := 19, 26 := 4], 24 := map[11 := 3, 4 := 24, 0 := -11, 28 := 18], 3 := map[24 := 29]][23 := map[22 := 19, 11 := 13, 13 := 12, 18 := 24]];
				var v_seq_116: seq<int> := [];
				var v_int_203: int := 13;
				var v_int_204: int := (if ((|v_seq_116| > 0)) then (v_seq_116[v_int_203]) else (19));
				var v_map_75: map<int, int> := (if ((v_int_204 in v_map_74)) then (v_map_74[v_int_204]) else (map[18 := 22, 10 := 20, 14 := 2, 12 := 26, 6 := 13][20 := 17]));
				var v_seq_117: seq<int> := [27, 16, 27, 24];
				var v_seq_118: seq<int> := v_seq_117;
				var v_int_205: int := 17;
				var v_int_206: int := safe_index_seq(v_seq_118, v_int_205);
				var v_int_207: int := v_int_206;
				var v_seq_119: seq<int> := (if ((|v_seq_117| > 0)) then (v_seq_117[v_int_207 := -29]) else (v_seq_117));
				var v_int_208: int := (if (false) then (29) else (29));
				var v_seq_225: seq<int> := v_seq_119;
				var v_int_353: int := v_int_208;
				var v_int_354: int := safe_index_seq(v_seq_225, v_int_353);
				v_int_208 := v_int_354;
				var v_int_209: int := (if ((|v_seq_119| > 0)) then (v_seq_119[v_int_208]) else ((if (true) then (5) else (24))));
				var v_int_210: int, v_int_211: int := (if ((v_int_202 in v_map_73)) then (v_map_73[v_int_202]) else ((if ((v_int_201 in v_map_72)) then (v_map_72[v_int_201]) else ((if ((|v_seq_115| > 0)) then (v_seq_115[v_int_200]) else (29)))))), (if ((v_int_209 in v_map_75)) then (v_map_75[v_int_209]) else (v_int_171));
				for v_int_195 := v_int_210 downto v_int_211 
					invariant (v_int_195 - v_int_211 >= 0)
				{
					print "v_int_195", " ", v_int_195, " ", "v_array_43[1]", " ", v_array_43[1], " ", "v_seq_105", " ", v_seq_105, " ", "v_seq_104", " ", v_seq_104, " ", "v_array_46[0]", " ", v_array_46[0], " ", "v_seq_106", " ", v_seq_106, " ", "v_array_48[2]", " ", (v_array_48[2] == map[false := [false]]), " ", "v_seq_103", " ", v_seq_103, " ", "v_seq_109", " ", v_seq_109, " ", "v_int_188", " ", v_int_188, " ", "v_seq_108", " ", v_seq_108, " ", "v_int_189", " ", v_int_189, " ", "v_int_184", " ", v_int_184, " ", "v_int_185", " ", v_int_185, " ", "v_bool_25", " ", v_bool_25, " ", "v_int_186", " ", v_int_186, " ", "v_int_187", " ", v_int_187, " ", "v_int_180", " ", v_int_180, " ", "v_int_181", " ", v_int_181, " ", "v_int_182", " ", v_int_182, " ", "v_seq_110", " ", v_seq_110, " ", "v_int_190", " ", v_int_190, " ", "v_array_43[2]", " ", v_array_43[2], " ", "v_array_41[0]", " ", v_array_41[0], " ", "v_seq_116", " ", v_seq_116, " ", "v_seq_115", " ", v_seq_115, " ", "v_seq_118", " ", v_seq_118, " ", "v_array_46[1]", " ", v_array_46[1], " ", "v_array_49[0]", " ", (v_array_49[0] == map[true := [false, true, true, true]]), " ", "v_seq_117", " ", v_seq_117, " ", "v_seq_112", " ", (v_seq_112 == [map[false := false, true := false], map[false := false, true := false], map[false := false, true := true]]), " ", "v_seq_111", " ", v_seq_111, " ", "v_seq_114", " ", v_seq_114, " ", "v_seq_113", " ", v_seq_113, " ", "v_int_199", " ", v_int_199, " ", "v_seq_119", " ", v_seq_119, " ", "v_int_196", " ", v_int_196, " ", "v_int_197", " ", v_int_197, " ", "v_int_198", " ", v_int_198, " ", "v_int_191", " ", v_int_191, " ", "v_int_192", " ", v_int_192, " ", "v_int_193", " ", v_int_193, " ", "v_int_194", " ", v_int_194, " ", "v_map_71", " ", (v_map_71 == map[16 := 9, 19 := 11, 20 := 0, 8 := 29]), " ", "v_map_72", " ", (v_map_72 == map[6 := 2, 7 := 13, 9 := 14, 10 := 24, 11 := 12]), " ", "v_map_70", " ", (v_map_70 == map[20 := 19, 6 := 16, 9 := 4]), " ", "v_array_42[2]", " ", v_array_42[2], " ", "v_array_45[1]", " ", v_array_45[1], " ", "v_array_48[0]", " ", (v_array_48[0] == map[true := [false, false, true]]), " ", "v_map_75", " ", (v_map_75 == map[18 := 22, 20 := 17, 6 := 13, 10 := 20, 12 := 26, 14 := 2]), " ", "v_array_47[3]", " ", v_array_47[3], " ", "v_map_73", " ", (v_map_73 == map[9 := 14, 25 := 4, 28 := 14, 12 := 1]), " ", "v_map_74", " ", (v_map_74 == map[3 := map[24 := 29], 23 := map[18 := 24, 22 := 19, 11 := 13, 13 := 12], 24 := map[0 := -11, 4 := 24, 11 := 3, 28 := 18], 12 := map[26 := 4, 27 := 19, 14 := 8]]), " ", "v_int_203", " ", v_int_203, " ", "v_int_204", " ", v_int_204, " ", "v_int_205", " ", v_int_205, " ", "v_int_206", " ", v_int_206, " ", "v_int_200", " ", v_int_200, " ", "v_int_168", " ", v_int_168, " ", "v_int_201", " ", v_int_201, " ", "v_int_202", " ", v_int_202, " ", "v_array_42[3]", " ", v_array_42[3], " ", "v_array_43[0]", " ", v_array_43[0], " ", "v_array_48[1]", " ", (v_array_48[1] == map[false := [false], true := [false, true]]), " ", "v_array_45[2]", " ", v_array_45[2], " ", "v_int_207", " ", v_int_207, " ", "v_int_208", " ", v_int_208, " ", "v_int_209", " ", v_int_209, " ", "v_int_179", " ", v_int_179, " ", "v_int_174", " ", v_int_174, " ", "v_int_172", " ", v_int_172, " ", "v_array_42[0]", " ", v_array_42[0], " ", "v_array_44[2]", " ", v_array_44[2], " ", "v_array_47[1]", " ", v_array_47[1], " ", "v_array_49[3]", " ", (v_array_49[3] == map[false := [true, true], true := [true]]), " ", "v_array_45[0]", " ", v_array_45[0], " ", "v_array_42[1]", " ", v_array_42[1], " ", "v_map_68", " ", (v_map_68 == map[false := false, true := false]), " ", "v_map_69", " ", (v_map_69 == map['Q' := true, 'B' := true, 'u' := false, 'L' := true]), " ", "v_array_47[2]", " ", v_array_47[2], " ", "v_map_66", " ", (v_map_66 == map[17 := v_array_43, 27 := v_array_42, 29 := v_array_45, 14 := v_array_44]), " ", "v_array_44[3]", " ", v_array_44[3], " ", "v_map_67", " ", (v_map_67 == map[16 := true, -19 := false, 20 := true, 28 := true]), " ", "v_map_64", " ", (v_map_64 == map[9 := 14, 25 := 4, 28 := 14]), " ", "v_map_65", " ", (v_map_65 == map[20 := true, 9 := false, 10 := false, 28 := false, 14 := false]), " ", "v_map_63", " ", (v_map_63 == map[18 := map[3 := true, 5 := false, 6 := true], -20 := map[24 := false, 10 := false], 8 := map[0 := false, 4 := false, 28 := true], 15 := map[-1 := false, 6 := true, 10 := true, 29 := false]]), " ", "v_array_41[1]", " ", v_array_41[1], " ", "v_array_44[0]", " ", v_array_44[0], " ", "v_char_11", " ", (v_char_11 == 'V'), " ", "v_array_46[2]", " ", v_array_46[2], " ", "v_array_49[1]", " ", (v_array_49[1] == map[false := [false], true := []]), " ", "v_array_44", " ", (v_array_44 == v_array_44), " ", "v_array_41[2]", " ", v_array_41[2], " ", "v_array_43", " ", (v_array_43 == v_array_43), " ", "v_array_42", " ", (v_array_42 == v_array_42), " ", "v_array_41", " ", (v_array_41 == v_array_41), " ", "v_array_44[1]", " ", v_array_44[1], " ", "v_array_47[0]", " ", v_array_47[0], " ", "v_array_46[3]", " ", v_array_46[3], " ", "v_array_49[2]", " ", (v_array_49[2] == map[false := [], true := [false]]), " ", "v_array_49", " ", (v_array_49 == v_array_49), " ", "v_array_48", " ", (v_array_48 == v_array_48), " ", "v_array_47", " ", (v_array_47 == v_array_47), " ", "v_array_46", " ", (v_array_46 == v_array_46), " ", "v_array_45", " ", (v_array_45 == v_array_45), " ", "v_map_57", " ", (v_map_57 == map[5 := 12]), " ", "v_map_58", " ", (v_map_58 == map[4 := 27, 7 := 26, 10 := 23, 28 := 2, 15 := 1]), " ", "v_seq_100", " ", (v_seq_100 == []), " ", "v_int_159", " ", v_int_159, " ", "v_seq_98", " ", (v_seq_98 == []), " ", "v_seq_99", " ", (v_seq_99 == []), " ", "v_int_169", " ", v_int_169, " ", "v_array_36[0]", " ", v_array_36[0], " ", "v_int_174", " ", v_int_174, " ", "v_array_36[1]", " ", v_array_36[1], " ", "v_int_175", " ", v_int_175, " ", "v_array_36[2]", " ", v_array_36[2], " ", "v_array_36[3]", " ", v_array_36[3], " ", "v_array_36", " ", (v_array_36 == v_array_36), " ", "v_array_36[4]", " ", v_array_36[4], " ", "v_int_170", " ", v_int_170, " ", "v_int_171", " ", v_int_171, " ", "v_int_172", " ", v_int_172, " ", "v_int_166", " ", v_int_166, " ", "v_int_167", " ", v_int_167, " ", "v_int_162", " ", v_int_162, " ", "v_seq_94", " ", (v_seq_94 == []), " ", "v_seq_95", " ", (v_seq_95 == []), " ", "v_int_163", " ", v_int_163, " ", "v_int_164", " ", v_int_164, " ", "v_seq_96", " ", v_seq_96, " ", "v_int_165", " ", v_int_165, " ", "v_seq_97", " ", (v_seq_97 == []), " ", "v_seq_91", " ", (v_seq_91 == [-29.92, 1.99, 1.03]), " ", "v_int_160", " ", v_int_160, " ", "v_seq_92", " ", v_seq_92, " ", "v_int_161", " ", v_int_161, " ", "v_seq_93", " ", v_seq_93, " ", "v_bool_1", " ", v_bool_1, " ", "v_char_6", " ", (v_char_6 == 'U'), " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[false := false, true := true]), " ", "v_map_3", " ", (v_map_3 == map[19 := multiset{0, 4, 6, 24}, 20 := multiset{2, -3, 29}, 10 := multiset{19, 7, -10}, -14 := multiset{13, 14}]), " ", "v_seq_7", " ", v_seq_7, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_44", " ", v_int_44, " ", "v_int_43", " ", v_int_43, " ", "v_int_87", " ", v_int_87, " ", "v_int_39", " ", v_int_39, " ", "v_seq_3", " ", (v_seq_3 == [multiset{}, multiset{true}]), " ", "v_int_38", " ", v_int_38, " ", "v_int_156", " ", v_int_156, " ", "v_int_157", " ", v_int_157, " ", "v_real_1", " ", (v_real_1 == -27.90), " ", "v_real_2", " ", (v_real_2 == -27.90), " ", "v_int_42", " ", v_int_42, " ", "v_int_86", " ", v_int_86, " ", "v_int_41", " ", v_int_41, " ", "v_int_40", " ", v_int_40, "\n";
					return ;
				}
				return ;
			}
			assert true;
			expect true;
			var v_map_76: map<int, map<int, int>> := map[7 := map[10 := 6, 26 := 19, 6 := 3, 5 := 26, -9 := 7], 29 := map[-25 := 14, 6 := 2], 17 := map[18 := 8, 20 := 3, 18 := 9, 23 := 17]];
			var v_int_216: int := 16;
			var v_map_77: map<int, int> := (if ((v_int_216 in v_map_76)) then (v_map_76[v_int_216]) else (map[22 := 26, 26 := 8, 17 := 2]))[v_int_167 := (10.05).Floor];
			var v_int_217: int := v_int_44;
			var v_int_214: int := (if ((v_int_217 in v_map_77)) then (v_map_77[v_int_217]) else (((match 6 {
				case _ => 0
			}) + (match 5 {
				case _ => 24
			}))));
			var v_map_78: map<char, bool> := map['P' := true, 's' := false];
			var v_char_12: char := 'm';
			var v_map_81: map<int, int> := (if ((if ((v_char_12 in v_map_78)) then (v_map_78[v_char_12]) else (false))) then (map[0 := 14, 21 := 27, 22 := 3][22 := 2]) else (map[23 := 15, 7 := 5, -27 := 18][27 := 20]));
			var v_map_79: map<char, int> := map['l' := 23, 'o' := 26, 'e' := 29, 'X' := 9];
			var v_char_13: char := 'B';
			var v_int_219: int := (if (('F' in multiset{'b'})) then ((if ((v_char_13 in v_map_79)) then (v_map_79[v_char_13]) else (24))) else ((20 - 18)));
			var v_seq_120: seq<map<char, int>> := [map['a' := 0, 'y' := 18], map['A' := 29, 'N' := 7], map['M' := 12, 'f' := 22]];
			var v_int_218: int := 17;
			var v_map_80: map<char, int> := (if ((|v_seq_120| > 0)) then (v_seq_120[v_int_218]) else (map['b' := 13, 'q' := 9]));
			var v_char_14: char := (if (true) then ('f') else ('P'));
			var v_int_215: int := (if ((v_int_219 in v_map_81)) then (v_map_81[v_int_219]) else ((if ((v_char_14 in v_map_80)) then (v_map_80[v_char_14]) else ((if (false) then (12) else (2))))));
			while (v_int_214 < v_int_215) 
				decreases v_int_215 - v_int_214;
				invariant (v_int_214 <= v_int_215);
			{
				v_int_214 := (v_int_214 + 1);
				var v_map_82: map<char, char> := map['U' := 'J', 'w' := 'Q', 'Y' := 'Y', 'h' := 'U', 'g' := 'e']['L' := 'D'];
				var v_char_15: char := v_char_13;
				var v_seq_121: seq<char> := ['r', 'J'];
				var v_seq_122: seq<char> := v_seq_121;
				var v_int_220: int := 24;
				var v_int_221: int := safe_index_seq(v_seq_122, v_int_220);
				var v_int_222: int := v_int_221;
				var v_seq_123: seq<char> := (if ((|v_seq_121| > 0)) then (v_seq_121[v_int_222 := 'A']) else (v_seq_121));
				var v_map_83: map<char, int> := map['h' := 11, 'E' := -3];
				var v_char_16: char := 'Z';
				var v_int_223: int := (if ((v_char_16 in v_map_83)) then (v_map_83[v_char_16]) else (12));
				var v_seq_124: seq<char> := ['Z'];
				var v_int_224: int := 24;
				var v_seq_125: seq<bool> := [true, false];
				var v_int_225: int := 1;
				var v_seq_126: seq<char> := ['D', 'B', 'p'];
				var v_int_226: int := 7;
				var v_map_84: map<char, char> := map['p' := 'U', 'O' := 'd', 'S' := 'v', 'S' := 'A'];
				var v_char_17: char := 'j';
				var v_map_85: map<char, char> := map['K' := 'Y', 'x' := 'z', 'P' := 'f', 'K' := 'j']['q' := 'J'];
				var v_char_18: char := (match 's' {
					case _ => 'z'
				});
				var v_seq_127: seq<bool> := [false, true, false, false];
				var v_int_227: int := 29;
				var v_seq_128: seq<char> := ['G', 'a', 'O'];
				var v_int_228: int := -11;
				var v_seq_129: seq<char> := ['R'];
				var v_int_229: int := 4;
				var v_map_86: map<char, char> := map['b' := 'K', 'F' := 's', 'R' := 'v']['W' := 'J'];
				var v_seq_130: seq<char> := ['J', 'a', 'a', 'R'];
				var v_int_230: int := 22;
				var v_char_19: char := (if ((|v_seq_130| > 0)) then (v_seq_130[v_int_230]) else ('e'));
				var v_seq_131: seq<char> := ['D', 'P', 'D', 'E'];
				var v_int_231: int := -22;
				var v_map_87: map<char, char> := map['c' := 'd'];
				var v_char_20: char := 'N';
				v_char_13, v_char_12, v_char_14, v_char_6, v_char_16 := (if (((match 'N' {
					case _ => true
				}) || (if (true) then (true) else (true)))) then ((if ((v_char_15 in v_map_82)) then (v_map_82[v_char_15]) else ((match 'H' {
					case _ => 'T'
				})))) else ((if ((|v_seq_123| > 0)) then (v_seq_123[v_int_223]) else ((if ((|v_seq_124| > 0)) then (v_seq_124[v_int_224]) else ('x')))))), (match 'K' {
					case _ => v_char_13
				}), (match 'I' {
					case _ => (if ((v_char_18 in v_map_85)) then (v_map_85[v_char_18]) else ((match 'L' {
						case _ => 'A'
					})))
				}), (match 'B' {
					case _ => (match 'd' {
						case _ => (if (false) then ('s') else ('D'))
					})
				}), v_char_14;
				break;
			}
			assert true;
			expect true;
			var v_map_88: map<char, bool> := map['H' := false, 'X' := true];
			var v_char_21: char := 'h';
			var v_map_89: map<char, char> := map['O' := 'w', 'm' := 'U', 'y' := 'V', 'l' := 'h', 'q' := 'f'];
			var v_char_22: char := 'M';
			var v_seq_132: seq<char> := ['r'];
			var v_seq_134: seq<char> := (if ((|v_seq_132| > 0)) then (v_seq_132[17..0]) else (v_seq_132));
			var v_seq_133: seq<int> := [20];
			var v_int_232: int := -1;
			var v_int_233: int := (if ((|v_seq_133| > 0)) then (v_seq_133[v_int_232]) else (14));
			var v_seq_135: seq<char> := [];
			var v_int_234: int := 15;
			v_char_6 := (if ((match 'y' {
				case _ => v_bool_1
			})) then ((match 'i' {
				case _ => (if (false) then ('d') else ('V'))
			})) else ((if ((|v_seq_134| > 0)) then (v_seq_134[v_int_233]) else ((if ((|v_seq_135| > 0)) then (v_seq_135[v_int_234]) else ('W'))))));
			var v_seq_136: seq<bool> := [];
			var v_seq_137: seq<bool> := (if ((|v_seq_136| > 0)) then (v_seq_136[13..3]) else (v_seq_136));
			var v_map_90: map<char, int> := map['T' := 4, 'f' := 5];
			var v_char_23: char := 'U';
			var v_int_236: int := (if ((v_char_23 in v_map_90)) then (v_map_90[v_char_23]) else (3));
			var v_map_91: map<char, bool> := map['Z' := false];
			var v_char_24: char := 'l';
			var v_seq_138: seq<int> := [25];
			var v_int_237: int := 6;
			var v_int_238: int, v_int_239: int := (v_real_1).Floor, (if ((if ((|v_seq_137| > 0)) then (v_seq_137[v_int_236]) else ((if ((v_char_24 in v_map_91)) then (v_map_91[v_char_24]) else (true))))) then ((if ((if (false) then (true) else (true))) then ((match 'M' {
				case _ => 25
			})) else (v_int_164))) else ((if (!(false)) then ((if (true) then (11) else (7))) else ((if ((|v_seq_138| > 0)) then (v_seq_138[v_int_237]) else (20))))));
			for v_int_235 := v_int_238 to v_int_239 
				invariant (v_int_239 - v_int_235 >= 0)
			{
				if v_bool_1 {
					return ;
				} else {
					return ;
				}
			}
			var v_seq_139: seq<bool> := [true, true, false, false];
			var v_seq_141: seq<bool> := (if ((|v_seq_139| > 0)) then (v_seq_139[-14..1]) else (v_seq_139));
			var v_seq_140: seq<int> := [-20];
			var v_int_240: int := 23;
			var v_int_241: int := (if ((|v_seq_140| > 0)) then (v_seq_140[v_int_240]) else (23));
			var v_map_92: map<char, bool> := map['n' := true, 'A' := false, 'e' := true, 'A' := true, 'F' := false];
			var v_char_25: char := 'V';
			var v_seq_142: seq<char> := ['N'];
			var v_int_242: int := 11;
			var v_map_93: map<char, char> := map['K' := 'K', 'J' := 'r', 'E' := 's', 'v' := 'C', 'y' := 'E'];
			var v_char_26: char := 'b';
			var v_seq_143: seq<char> := [];
			var v_seq_144: seq<char> := v_seq_143;
			var v_int_243: int := 6;
			var v_int_244: int := safe_index_seq(v_seq_144, v_int_243);
			var v_int_245: int := v_int_244;
			var v_seq_146: seq<char> := (if ((|v_seq_143| > 0)) then (v_seq_143[v_int_245 := 'V']) else (v_seq_143));
			var v_seq_147: seq<char> := v_seq_146;
			var v_seq_145: seq<int> := [];
			var v_int_246: int := 9;
			var v_int_247: int := (if ((|v_seq_145| > 0)) then (v_seq_145[v_int_246]) else (-18));
			var v_int_248: int := safe_index_seq(v_seq_147, v_int_247);
			var v_int_249: int := v_int_248;
			var v_seq_148: seq<char> := (if ((|v_seq_146| > 0)) then (v_seq_146[v_int_249 := (match 'V' {
				case _ => 'X'
			})]) else (v_seq_146));
			var v_int_250: int := v_int_172;
			var v_seq_149: seq<char> := ['y', 'D', 'l'];
			var v_seq_150: seq<char> := v_seq_149;
			var v_int_251: int := 5;
			var v_int_252: int := safe_index_seq(v_seq_150, v_int_251);
			var v_int_253: int := v_int_252;
			var v_seq_151: seq<char> := (if ((|v_seq_149| > 0)) then (v_seq_149[v_int_253 := 's']) else (v_seq_149));
			var v_int_254: int := (if (false) then (7) else (26));
			var v_map_94: map<char, char> := map['t' := 'v'];
			var v_char_27: char := 'I';
			var v_map_95: map<char, char> := map['I' := 'f', 'b' := 'U', 'u' := 'x', 't' := 'z']['O' := 'y'];
			var v_char_28: char := v_char_25;
			var v_map_96: map<char, char> := map['v' := 'J', 'C' := 'M', 'k' := 'l', 'v' := 's', 'r' := 'h']['j' := 'U'];
			var v_char_29: char := (if (false) then ('L') else ('s'));
			var v_seq_152: seq<char> := ['Z', 'd'];
			var v_int_255: int := 6;
			v_char_6, v_char_14, v_char_24, v_char_13, v_char_25 := (if ((if ((|v_seq_141| > 0)) then (v_seq_141[v_int_241]) else ((if ((v_char_25 in v_map_92)) then (v_map_92[v_char_25]) else (false))))) then ((if (('j' in map['A' := 'n', 'T' := 'q', 'S' := 'q', 'c' := 'f'])) then ((if ((|v_seq_142| > 0)) then (v_seq_142[v_int_242]) else ('B'))) else ((if ((v_char_26 in v_map_93)) then (v_map_93[v_char_26]) else ('I'))))) else (v_char_14)), (if ((|v_seq_148| > 0)) then (v_seq_148[v_int_250]) else ((if ((|v_seq_151| > 0)) then (v_seq_151[v_int_254]) else ((if (true) then ('h') else ('D')))))), (match 'l' {
				case _ => (if ((v_char_29 in v_map_96)) then (v_map_96[v_char_29]) else (v_char_6))
			}), (match 'Q' {
				case _ => v_char_13
			}), v_char_24;
			var v_map_97: map<char, char> := map['s' := 'W', 'v' := 'y', 'o' := 'c'];
			var v_char_30: char := 'U';
			var v_map_99: map<char, char> := map['C' := 'Z', 'I' := 'C', 'C' := 'B', 'x' := 'Z']['w' := 'S'][v_char_25 := (if ((v_char_30 in v_map_97)) then (v_map_97[v_char_30]) else ('z'))];
			var v_char_32: char := v_char_6;
			var v_map_98: map<char, char> := map['l' := 'w', 'U' := 'n'];
			var v_char_31: char := 'i';
			var v_map_100: map<char, char> := map['c' := 'U', 'n' := 'o', 'R' := 'T', 'n' := 'x', 'V' := 'L']['D' := 'G'][(if (false) then ('R') else ('B')) := v_char_24];
			var v_char_33: char := (if ((match 'A' {
				case _ => true
			})) then (v_char_13) else ((match 'G' {
				case _ => 'O'
			})));
			v_char_24, v_char_14, v_char_23, v_char_25 := (match 'T' {
				case _ => (match 'v' {
					case _ => (match 'd' {
						case _ => 'e'
					})
				})
			}), (if ((v_char_32 in v_map_99)) then (v_map_99[v_char_32]) else ((match 'S' {
				case _ => v_char_13
			}))), (if ((v_char_33 in v_map_100)) then (v_map_100[v_char_33]) else ((if ((false <== false)) then (v_char_6) else ((match 'i' {
				case _ => 'B'
			}))))), v_char_12;
			continue;
		}
	}
	var v_seq_153: seq<bool> := [true];
	var v_int_258: int := 7;
	var v_map_101: map<char, char> := map['s' := 'P', 'b' := 'Q']['H' := 'i'];
	var v_char_34: char := (if (false) then ('z') else ('L'));
	v_char_6 := (if ((match 'k' {
		case _ => ('s' == 'C')
	})) then (v_char_6) else ((if ((v_char_34 in v_map_101)) then (v_map_101[v_char_34]) else (v_char_6))));
	var v_seq_154: seq<char> := ['I', 'H', 'b', 'p'];
	var v_seq_155: seq<char> := (if ((|v_seq_154| > 0)) then (v_seq_154[8..27]) else (v_seq_154));
	var v_seq_156: seq<char> := v_seq_155;
	var v_int_259: int := (if (false) then (22) else (9));
	var v_int_260: int := safe_index_seq(v_seq_156, v_int_259);
	var v_int_261: int := v_int_260;
	var v_seq_157: seq<char> := (if ((|v_seq_155| > 0)) then (v_seq_155[v_int_261 := (match 'I' {
		case _ => 'l'
	})]) else (v_seq_155));
	var v_int_262: int := v_int_38;
	var v_seq_158: seq<char> := ['i', 'i', 'p', 'f'];
	var v_seq_159: seq<char> := (if ((|v_seq_158| > 0)) then (v_seq_158[17..9]) else (v_seq_158));
	var v_int_263: int := v_int_40;
	var v_map_102: map<char, char> := map['f' := 'O'];
	var v_char_35: char := 'V';
	v_char_6 := (if ((|v_seq_157| > 0)) then (v_seq_157[v_int_262]) else ((if ((|v_seq_159| > 0)) then (v_seq_159[v_int_263]) else ((if ((v_char_35 in v_map_102)) then (v_map_102[v_char_35]) else ('U'))))));
	var v_seq_160: seq<char> := [];
	var v_seq_161: seq<char> := v_seq_160;
	var v_int_264: int := 2;
	var v_int_265: int := safe_index_seq(v_seq_161, v_int_264);
	var v_int_266: int := v_int_265;
	var v_seq_162: seq<char> := (if ((|v_seq_160| > 0)) then (v_seq_160[v_int_266 := 'Y']) else (v_seq_160));
	var v_map_103: map<char, int> := map['U' := -14, 'e' := 20, 'P' := 14];
	var v_char_36: char := 'E';
	var v_int_267: int := (if ((v_char_36 in v_map_103)) then (v_map_103[v_char_36]) else (19));
	var v_map_105: map<char, char> := map['I' := 'A', 'f' := 'r', 'E' := 'l', 'i' := 'S']['C' := 'L'];
	var v_char_38: char := (match 'y' {
		case _ => 'w'
	});
	var v_map_104: map<char, char> := map['N' := 'w'];
	var v_char_37: char := 'H';
	v_char_34, v_char_6 := (match 'N' {
		case _ => (if ((v_char_38 in v_map_105)) then (v_map_105[v_char_38]) else ((if ((v_char_37 in v_map_104)) then (v_map_104[v_char_37]) else ('G'))))
	}), v_char_6;
	match v_char_6 {
		case _ => {
			var v_seq_209: seq<char> := ['e', 'L'];
			var v_int_324: int := 8;
			var v_seq_210: seq<char> := ['O', 'b', 'Y'];
			var v_int_325: int := 20;
			var v_map_136: map<char, char> := map['q' := 'P', 'Z' := 'I']['b' := 'e'][(if ((|v_seq_209| > 0)) then (v_seq_209[v_int_324]) else ('I')) := (if ((|v_seq_210| > 0)) then (v_seq_210[v_int_325]) else ('r'))];
			var v_char_69: char := v_char_35;
			var v_map_135: map<char, char> := map['w' := 'E', 'I' := 'V', 'w' := 'Y', 'j' := 'M', 't' := 'M'];
			var v_char_68: char := 'L';
			var v_seq_211: seq<char> := [];
			var v_seq_212: seq<char> := (if ((|v_seq_211| > 0)) then (v_seq_211[29..26]) else (v_seq_211));
			var v_int_326: int := (match 'w' {
				case _ => 1
			});
			var v_seq_213: seq<char> := ['O', 'R', 'e', 'S'];
			var v_int_327: int := 21;
			var v_seq_214: seq<char> := ['H'];
			var v_int_328: int := 26;
			var v_map_137: map<char, char> := map['i' := 'Q', 'b' := 'J', 's' := 'I', 'c' := 'H'];
			var v_char_70: char := 'n';
			v_char_35, v_char_69, v_char_6 := (if ((v_char_69 in v_map_136)) then (v_map_136[v_char_69]) else ((if (('B' !in multiset{})) then ((if ((v_char_68 in v_map_135)) then (v_map_135[v_char_68]) else ('Y'))) else (v_char_68)))), (match 'F' {
				case _ => (if ((|v_seq_212| > 0)) then (v_seq_212[v_int_326]) else ((if ((|v_seq_213| > 0)) then (v_seq_213[v_int_327]) else ('j'))))
			}), (match 'd' {
				case _ => v_char_34
			});
		}
		
	}
	
	return ;
}
