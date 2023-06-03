// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1
datatype DT_2 = DT_2_1 | DT_2_4(DT_2_4_1: DT_3<bool>, DT_2_4_2: int, DT_2_4_3: bool)
datatype DT_3<T_3> = DT_3_1 | DT_3_2(DT_3_2_1: T_3, DT_3_2_2: T_3)
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

method m_method_6(p_m_method_6_1: int, p_m_method_6_2: map<bool, int>, p_m_method_6_3: real) returns (ret_1: (bool, real, bool), ret_2: bool, ret_3: DT_1<char, multiset<bool>>, ret_4: bool, ret_5: real)
	requires ((-16.84 < p_m_method_6_3 < -16.64) && (p_m_method_6_2 == map[false := 24]) && (p_m_method_6_1 == 4));
	ensures (((-16.84 < p_m_method_6_3 < -16.64) && (p_m_method_6_2 == map[false := 24]) && (p_m_method_6_1 == 4)) ==> (((ret_1).0 == true) && (-15.93 < (ret_1).1 < -15.73) && ((ret_1).2 == true) && (ret_2 == true) && (ret_3.DT_1_1? && ((ret_3 == DT_1_1))) && (ret_4 == false) && (4.62 < ret_5 < 4.82)));
{
	var v_bool_real_bool_1: (bool, real, bool) := (false, -17.70, false);
	var v_bool_real_bool_2: (bool, real, bool) := (true, -15.83, true);
	var v_DT_1_1_7: DT_1<char, multiset<bool>> := DT_1_1;
	var v_DT_1_1_8: DT_1<char, multiset<bool>> := DT_1_1;
	var v_DT_1_1_9: DT_1<char, multiset<bool>> := DT_1_1;
	var v_bool_real_19: (bool, real) := (true, -29.09);
	var v_bool_real_20: (bool, real) := v_bool_real_19;
	var v_bool_13: bool := m_method_2(v_bool_real_20);
	var v_seq_9: seq<real> := [4.72, -2.05, 1.83];
	var v_int_21: int := 19;
	var v_seq_124: seq<real> := v_seq_9;
	var v_int_185: int := v_int_21;
	var v_int_186: int := safe_index_seq(v_seq_124, v_int_185);
	v_int_21 := v_int_186;
	var v_bool_real_22: (bool, real) := (true, -29.09);
	var v_bool_real_bool_34: (bool, real, bool) := (false, -17.70, false);
	var v_bool_real_23: (bool, real) := (true, -29.09);
	var v_bool_real_bool_35: (bool, real, bool) := (true, -15.83, true);
	print "v_bool_real_bool_2.2", " ", v_bool_real_bool_2.2, " ", "v_bool_real_bool_1.2", " ", v_bool_real_bool_1.2, " ", "v_bool_real_bool_2.1", " ", (v_bool_real_bool_2.1 == -15.83), " ", "v_bool_real_bool_1.1", " ", (v_bool_real_bool_1.1 == -17.70), " ", "v_bool_real_bool_2.0", " ", v_bool_real_bool_2.0, " ", "v_bool_real_bool_1.0", " ", v_bool_real_bool_1.0, " ", "v_bool_real_20", " ", (v_bool_real_20 == v_bool_real_22), " ", "v_bool_real_bool_1", " ", (v_bool_real_bool_1 == v_bool_real_bool_34), " ", "v_bool_real_19", " ", (v_bool_real_19 == v_bool_real_23), " ", "v_bool_real_bool_2", " ", (v_bool_real_bool_2 == v_bool_real_bool_35), " ", "v_bool_real_19.1", " ", (v_bool_real_19.1 == -29.09), " ", "v_seq_9", " ", (v_seq_9 == [4.72, -2.05, 1.83]), " ", "v_bool_real_19.0", " ", v_bool_real_19.0, " ", "v_int_21", " ", v_int_21, " ", "p_m_method_6_3", " ", (p_m_method_6_3 == -16.74), " ", "v_bool_13", " ", v_bool_13, " ", "p_m_method_6_2", " ", (p_m_method_6_2 == map[false := 24]), " ", "p_m_method_6_1", " ", p_m_method_6_1, "\n";
	return (if (false) then (v_bool_real_bool_1) else (v_bool_real_bool_2)), v_bool_real_bool_2.2, (match 'J' {
		case 'g' => v_DT_1_1_7
		case 'q' => v_DT_1_1_8
		case _ => v_DT_1_1_9
	}), v_bool_13, (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_21]) else (-23.42));
}

method m_method_5(p_m_method_5_1: map<bool, bool>) returns (ret_1: char)
	requires ((p_m_method_5_1 == map[false := false, true := false]));
	ensures (((p_m_method_5_1 == map[false := false, true := false])) ==> ((ret_1 == 'T')));
{
	var v_int_22: int := (if (false) then (3) else (4));
	var v_map_10: map<char, map<bool, int>> := map['Z' := map[true := 7, false := 17], 'E' := map[true := 8], 'W' := map[true := 11, false := 12], 'R' := map[true := 10, false := 15]];
	var v_char_6: char := 'T';
	var v_map_11: map<bool, int> := (if ((v_char_6 in v_map_10)) then (v_map_10[v_char_6]) else (map[false := 24]));
	var v_bool_14: bool := false;
	var v_array_13: array<real> := new real[3] [12.93, 3.17, -17.81];
	var v_array_14: array<real> := v_array_13;
	var v_real_2: real := m_method_1(v_bool_14, v_array_14);
	var v_real_3: real := v_real_2;
	var v_bool_real_bool_3: (bool, real, bool), v_bool_15: bool, v_DT_1_1_10: DT_1<char, multiset<bool>>, v_bool_16: bool, v_real_4: real := m_method_6(v_int_22, v_map_11, v_real_3);
	v_bool_real_bool_3, v_bool_16, v_DT_1_1_10, v_bool_14, v_real_3 := v_bool_real_bool_3, v_bool_15, v_DT_1_1_10, v_bool_16, v_real_4;
	var v_seq_10: seq<int> := [1, 0];
	var v_int_24: int := 12;
	var v_seq_125: seq<int> := v_seq_10;
	var v_int_187: int := v_int_24;
	var v_int_188: int := safe_index_seq(v_seq_125, v_int_187);
	v_int_24 := v_int_188;
	var v_int_25: int, v_int_26: int := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_24]) else (8)), (14 / 20);
	for v_int_23 := v_int_25 downto v_int_26 
		invariant (v_int_23 - v_int_26 >= 0)
	{
		var v_bool_real_bool_36: (bool, real, bool) := (true, -15.83, true);
		print "v_int_23", " ", v_int_23, " ", "v_array_13[1]", " ", (v_array_13[1] == 3.17), " ", "v_array_13[0]", " ", (v_array_13[0] == 12.93), " ", "v_bool_15", " ", v_bool_15, " ", "v_char_6", " ", (v_char_6 == 'T'), " ", "v_array_13[2]", " ", (v_array_13[2] == -17.81), " ", "v_bool_16", " ", v_bool_16, " ", "v_map_11", " ", (v_map_11 == map[false := 24]), " ", "v_bool_real_bool_3", " ", (v_bool_real_bool_3 == v_bool_real_bool_36), " ", "v_map_10", " ", (v_map_10 == map['R' := map[false := 15, true := 10], 'E' := map[true := 8], 'W' := map[false := 12, true := 11], 'Z' := map[false := 17, true := 7]]), " ", "v_int_24", " ", v_int_24, " ", "v_int_22", " ", v_int_22, " ", "v_seq_10", " ", v_seq_10, " ", "v_bool_14", " ", v_bool_14, " ", "v_real_2", " ", (v_real_2 == -16.74), " ", "v_DT_1_1_10", " ", v_DT_1_1_10, " ", "v_real_3", " ", (v_real_3 == 4.72), " ", "v_real_4", " ", (v_real_4 == 4.72), " ", "v_array_14", " ", (v_array_14 == v_array_13), " ", "v_array_13", " ", (v_array_13 == v_array_13), " ", "p_m_method_5_1", " ", (p_m_method_5_1 == map[false := false, true := false]), "\n";
		return v_char_6;
	}
	v_char_6 := v_char_6;
	var v_map_12: map<int, bool> := map[27 := true, 22 := false, 8 := true, 12 := true, 20 := true];
	var v_int_27: int := 4;
	if (if ((v_int_27 in v_map_12)) then (v_map_12[v_int_27]) else (false)) {
		var v_seq_11: seq<char> := ['c', 'o', 'I'];
		var v_int_28: int := 29;
		return (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_28]) else ('i'));
	} else {
		return (if (false) then ('e') else ('x'));
	}
}

method m_method_4(p_m_method_4_1: char, p_m_method_4_2: bool, p_m_method_4_3: char) returns (ret_1: (bool, real))
{
	var v_bool_real_16: (bool, real) := (false, 12.04);
	return v_bool_real_16;
}

method m_method_3(p_m_method_3_1: char, p_m_method_3_2: bool, p_m_method_3_3: int) returns (ret_1: bool)
	requires ((p_m_method_3_1 == 'E') && (p_m_method_3_3 == -2) && (p_m_method_3_2 == false));
	ensures (((p_m_method_3_1 == 'E') && (p_m_method_3_3 == -2) && (p_m_method_3_2 == false)) ==> ((ret_1 == false)));
{
	print "p_m_method_3_2", " ", p_m_method_3_2, " ", "p_m_method_3_1", " ", (p_m_method_3_1 == 'E'), " ", "p_m_method_3_3", " ", p_m_method_3_3, "\n";
	return (if (true) then (false) else (false));
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

method m_method_2(p_m_method_2_1: (bool, real)) returns (ret_1: bool)
	requires (((p_m_method_2_1).0 == false) && (-27.43 < (p_m_method_2_1).1 < -27.23)) || (((p_m_method_2_1).0 == true) && (-29.19 < (p_m_method_2_1).1 < -28.99));
	ensures ((((p_m_method_2_1).0 == false) && (-27.43 < (p_m_method_2_1).1 < -27.23)) ==> ((ret_1 == false))) && ((((p_m_method_2_1).0 == true) && (-29.19 < (p_m_method_2_1).1 < -28.99)) ==> ((ret_1 == false)));
{
	var v_bool_real_21: (bool, real) := (false, -27.33);
	print "p_m_method_2_1.0", " ", p_m_method_2_1.0, " ", "p_m_method_2_1.1", " ", (p_m_method_2_1.1 == -27.33), " ", "p_m_method_2_1", " ", (p_m_method_2_1 == v_bool_real_21), "\n";
	return false;
}

method m_method_1(p_m_method_1_1: bool, p_m_method_1_2: array<real>) returns (ret_1: real)
	requires ((p_m_method_1_1 == false) && p_m_method_1_2.Length == 3 && (1.19 < p_m_method_1_2[0] < 1.39) && (13.81 < p_m_method_1_2[1] < 14.01) && (28.32 < p_m_method_1_2[2] < 28.52)) || ((p_m_method_1_1 == false) && p_m_method_1_2.Length == 3 && (12.83 < p_m_method_1_2[0] < 13.03) && (3.07 < p_m_method_1_2[1] < 3.27) && (-17.91 < p_m_method_1_2[2] < -17.71));
	ensures (((p_m_method_1_1 == false) && p_m_method_1_2.Length == 3 && (12.83 < p_m_method_1_2[0] < 13.03) && (3.07 < p_m_method_1_2[1] < 3.27) && (-17.91 < p_m_method_1_2[2] < -17.71)) ==> ((-16.84 < ret_1 < -16.64))) && (((p_m_method_1_1 == false) && p_m_method_1_2.Length == 3 && (1.19 < p_m_method_1_2[0] < 1.39) && (13.81 < p_m_method_1_2[1] < 14.01) && (28.32 < p_m_method_1_2[2] < 28.52)) ==> ((-16.84 < ret_1 < -16.64)));
{
	var v_int_7: int := 24;
	var v_int_8: int := 14;
	while (v_int_7 < v_int_8) 
		decreases v_int_8 - v_int_7;
		invariant (v_int_7 <= v_int_8);
	{
		v_int_7 := (v_int_7 + 1);
		continue;
	}
	print "p_m_method_1_2", " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "p_m_method_1_2[0]", " ", (p_m_method_1_2[0] == 1.29), " ", "p_m_method_1_2[1]", " ", (p_m_method_1_2[1] == 13.91), " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "p_m_method_1_2[2]", " ", (p_m_method_1_2[2] == 28.42), "\n";
	return -16.74;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_bool_1: bool := false;
	var v_array_1: array<real> := new real[3] [1.29, 13.91, 28.42];
	var v_array_2: array<real> := v_array_1;
	var v_real_1: real := m_method_1(v_bool_1, v_array_2);
	var v_seq_3: seq<set<bool>> := [{}, {true}, {false}, {false, true, true}];
	var v_int_9: int := 0;
	var v_map_1: map<int, map<bool, real>> := (map[22 := map[false := -5.00], 10 := map[false := 24.08], 13 := map[false := -23.57]] + map[20 := map[false := 27.73], 19 := map[true := 23.10, false := -4.48], 25 := map[true := 19.38], 9 := map[false := -7.96]]);
	var v_int_10: int := v_int_9;
	var v_seq_4: seq<map<bool, real>> := (if (false) then ([map[true := 18.66, false := 3.46], map[false := 26.40, false := -8.54, true := 20.78, true := 6.91], map[false := -2.66, false := -13.90]]) else ([]));
	var v_int_11: int := (match -0.07 {
		case 12.11 => 16
		case 4.54 => 5
		case _ => 26
	});
	var v_int_12: int, v_set_1: set<map<bool, real>> := ((match 'v' {
		case 'l' => (match true {
			case _ => 19.11
		})
		case 'k' => -24.90
		case _ => (match false {
			case false => 26.93
			case _ => -7.01
		})
	})).Floor, {map[(true && false) := v_real_1], (map[false := 3.46, true := -19.97] - (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_9]) else ({true, true, true}))), (if ((v_int_10 in v_map_1)) then (v_map_1[v_int_10]) else ((if (true) then (map[false := -11.95, true := -18.83]) else (map[false := -24.56, true := -28.67])))), (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_11]) else ((if (false) then (map[false := 18.52, true := -15.75]) else (map[true := -21.50, false := 25.89]))))};
	var v_int_13: int := v_int_9;
	var v_array_3: array<bool> := new bool[4] [false, true, true, true];
	var v_array_4: array<bool> := new bool[4];
	v_array_4[0] := false;
	v_array_4[1] := false;
	v_array_4[2] := false;
	v_array_4[3] := true;
	var v_array_5: array<bool> := new bool[3] [false, true, true];
	var v_array_6: array<bool> := new bool[5] [true, false, true, true, true];
	var v_array_7: array<bool> := new bool[4] [false, false, true, true];
	var v_array_8: array<array<bool>> := new array<bool>[5] [v_array_3, v_array_4, v_array_5, v_array_6, v_array_7];
	var v_array_9: array<bool> := new bool[5] [true, true, true, false, true];
	var v_array_10: array<bool> := new bool[3] [true, false, false];
	var v_array_11: array<bool> := new bool[3] [true, true, true];
	var v_array_12: array<array<bool>> := new array<bool>[3] [v_array_9, v_array_10, v_array_11];
	var v_seq_5: seq<array<array<bool>>> := [v_array_8, v_array_12];
	var v_seq_122: seq<array<array<bool>>> := v_seq_5;
	var v_int_179: int := 27;
	var v_int_180: int := 9;
	var v_int_181: int, v_int_182: int := safe_subsequence(v_seq_122, v_int_179, v_int_180);
	var v_int_177: int, v_int_178: int := v_int_181, v_int_182;
	var v_seq_7: seq<array<array<bool>>> := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_177..v_int_178]) else (v_seq_5));
	var v_seq_6: seq<int> := [19, 27];
	var v_int_15: int := -25;
	var v_seq_123: seq<int> := v_seq_6;
	var v_int_183: int := v_int_15;
	var v_int_184: int := safe_index_seq(v_seq_123, v_int_183);
	v_int_15 := v_int_184;
	var v_int_16: int := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_15]) else (10));
	var v_int_14: int := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_16]) else (v_array_12)).Length;
	while (v_int_13 < v_int_14) 
		decreases v_int_14 - v_int_13;
		invariant (v_int_13 <= v_int_14) && ((((v_int_13 == 0)) ==> ((((v_int_9 == 0))))));
	{
		v_int_13 := (v_int_13 + 1);
		var v_bool_real_1: (bool, real) := (false, -27.33);
		var v_bool_real_2: (bool, real) := v_bool_real_1;
		var v_bool_2: bool := m_method_2(v_bool_real_2);
		var v_map_2: map<int, bool> := map[29 := true, 23 := false];
		var v_int_17: int := -2;
		var v_char_1: char := (match 19.14 {
			case 29.74 => 'Y'
			case -8.10 => 't'
			case _ => 'E'
		});
		var v_bool_3: bool := ({} >= {'I', 'c'});
		var v_int_18: int := (-1.12).Floor;
		var v_bool_4: bool := m_method_3(v_char_1, v_bool_3, v_int_18);
		if (if ((match false {
			case true => v_bool_2
			case _ => (if ((v_int_17 in v_map_2)) then (v_map_2[v_int_17]) else (true))
		})) then (v_array_3[0]) else (v_bool_4)) {
			assert true;
			expect true;
			var v_bool_real_3: (bool, real) := (true, 15.46);
			var v_bool_real_4: (bool, real) := (true, 3.52);
			var v_bool_real_5: (bool, real) := (false, 16.68);
			var v_bool_real_6: (bool, real) := (true, 29.48);
			var v_bool_real_7: (bool, real) := (false, 20.87);
			var v_bool_real_8: (bool, real) := (false, -7.26);
			var v_bool_real_9: (bool, real) := (false, 13.57);
			var v_bool_real_10: (bool, real) := (true, 14.95);
			var v_bool_real_11: (bool, real) := (true, -9.63);
			var v_bool_real_12: (bool, real) := (false, 0.02);
			var v_map_4: map<char, (bool, real)> := (map['Z' := v_bool_real_3, 'Q' := v_bool_real_4, 'L' := v_bool_real_5, 'L' := v_bool_real_6, 's' := v_bool_real_7] + map['J' := v_bool_real_8, 'g' := v_bool_real_9, 'j' := v_bool_real_10, 'w' := v_bool_real_11, 'X' := v_bool_real_12]);
			var v_map_3: map<bool, char> := map[true := 'a', true := 'h', true := 's', true := 'h', true := 'B'];
			var v_bool_5: bool := true;
			var v_char_2: char := (if ((v_bool_5 in v_map_3)) then (v_map_3[v_bool_5]) else ('Y'));
			var v_bool_real_13: (bool, real) := (true, 29.07);
			var v_bool_real_14: (bool, real) := (true, 29.62);
			var v_bool_real_15: (bool, real) := (if ((v_char_2 in v_map_4)) then (v_map_4[v_char_2]) else ((if (true) then (v_bool_real_13) else (v_bool_real_14))));
			var v_bool_6: bool := m_method_2(v_bool_real_15);
			if v_bool_6 {
				var v_DT_1_1_1: DT_1<char, multiset<bool>> := DT_1_1;
				var v_DT_1_1_2: DT_1<char, multiset<bool>> := DT_1_1;
				var v_DT_1_1_3: DT_1<char, multiset<bool>> := DT_1_1;
				var v_DT_1_1_4: DT_1<char, multiset<bool>> := DT_1_1;
				var v_DT_1_1_5: DT_1<char, multiset<bool>> := DT_1_1;
				var v_map_5: map<DT_1<char, multiset<bool>>, bool> := ((map[v_DT_1_1_1 := true] - {v_DT_1_1_2}) - (if (true) then ({v_DT_1_1_3, v_DT_1_1_4}) else ({v_DT_1_1_5})));
				var v_DT_1_1_6: DT_1<char, multiset<bool>> := v_DT_1_1_3;
				var v_char_3: char := 'c';
				var v_bool_7: bool := false;
				var v_char_4: char := 't';
				var v_bool_real_17: (bool, real) := m_method_4(v_char_3, v_bool_7, v_char_4);
				var v_bool_real_18: (bool, real) := v_bool_real_17;
				var v_bool_8: bool := m_method_2(v_bool_real_18);
				if (if ((v_DT_1_1_6 in v_map_5)) then (v_map_5[v_DT_1_1_6]) else (v_bool_8)) {
					return ;
				}
				var v_map_7: map<bool, bool> := (map[false := false, false := true, true := true, true := true, false := false] + map[true := false, true := true, true := true])[v_bool_8 := (true <==> true)];
				var v_char_5: char := 'z';
				var v_bool_9: bool := false;
				var v_int_19: int := 7;
				var v_bool_10: bool := m_method_3(v_char_5, v_bool_9, v_int_19);
				var v_seq_8: seq<bool> := [false, true, false, true];
				var v_int_20: int := -25;
				var v_bool_11: bool := (if (v_bool_10) then ((if ((|v_seq_8| > 0)) then (v_seq_8[v_int_20]) else (false))) else ((-29.09 > 14.17)));
				var v_map_6: map<set<multiset<real>>, bool> := map[{multiset({10.54}), multiset{23.77, 27.79}, multiset{-21.60}} := true, {multiset{-4.21, -19.68, -2.05}, multiset{-5.22, -1.45, 19.69, -3.81}, multiset{-21.23, -5.08}} := false];
				var v_set_2: set<multiset<real>> := {multiset{19.45, -0.88}, multiset({-16.67, -2.27}), multiset{-23.60, -0.80, -11.31, -3.36}};
				if (if ((v_bool_11 in v_map_7)) then (v_map_7[v_bool_11]) else ((if ((multiset({-7}) != multiset{18, 19, 28, 2})) then ((9 !in map[11 := multiset{multiset{13.30, 18.54, 9.84}, multiset({22.53, -16.00, -7.54})}, 2 := multiset{multiset{-6.52, 18.14}, multiset{23.02, 4.77, 13.63, 18.58}}, 7 := multiset({multiset{}, multiset{6.85}, multiset{17.19}})])) else ((if ((v_set_2 in v_map_6)) then (v_map_6[v_set_2]) else (false)))))) {
					return ;
				} else {
					return ;
				}
			}
		} else {
			var v_map_8: map<multiset<multiset<real>>, map<bool, char>> := map[multiset{multiset{}, multiset({})} := map[true := 'g', false := 'w'], multiset{multiset{-14.17, -0.27, 11.22}, multiset{7.72, -6.09}} := map[true := 'x', false := 't'], multiset{} := map[false := 'L'], multiset{multiset{21.04, -16.19, -11.73}, multiset{-29.61, 4.03, -25.36}, multiset{-19.46, -3.07, -21.84}, multiset{}} := map[false := 'g', true := 'P']];
			var v_multiset_1: multiset<multiset<real>> := multiset{multiset({-21.26, 22.65}), multiset{}, multiset{5.94, -17.19}};
			var v_map_9: map<bool, char> := (if ((v_multiset_1 in v_map_8)) then (v_map_8[v_multiset_1]) else (map[false := 'C', true := 'E']));
			var v_bool_12: bool := (multiset({false, true, false}) == multiset({true}));
			var v_map_13: map<bool, bool> := map[false := false, true := false][false := false];
			var v_char_7: char := m_method_5(v_map_13);
			if ((if ((v_bool_12 in v_map_9)) then (v_map_9[v_bool_12]) else (v_char_1)) > v_char_7) {
				var v_char_8: char := 'o';
				var v_bool_17: bool := true;
				var v_int_29: int := 20;
				var v_bool_18: bool := m_method_3(v_char_8, v_bool_17, v_int_29);
				var v_bool_real_bool_4: (bool, real, bool) := (true, -2.08, false);
				var v_bool_real_bool_5: (bool, real, bool) := (true, 4.01, true);
				var v_bool_real_bool_6: (bool, real, bool) := (false, -3.77, false);
				var v_bool_real_bool_7: (bool, real, bool) := (true, -27.54, true);
				var v_bool_real_bool_8: (bool, real, bool) := (true, -28.89, false);
				var v_bool_real_bool_9: (bool, real, bool) := (true, 14.80, true);
				var v_seq_12: seq<seq<(bool, real, bool)>> := [];
				var v_int_30: int := 4;
				var v_bool_real_bool_10: (bool, real, bool) := (true, 3.55, false);
				var v_bool_real_bool_11: (bool, real, bool) := (true, 2.82, false);
				var v_bool_real_bool_12: (bool, real, bool) := (false, 24.03, true);
				var v_bool_real_bool_13: (bool, real, bool) := (false, 26.30, true);
				var v_bool_real_bool_14: (bool, real, bool) := (true, 3.13, false);
				var v_bool_real_bool_15: (bool, real, bool) := (false, -29.15, true);
				var v_bool_real_bool_16: (bool, real, bool) := (true, 16.11, true);
				var v_bool_real_bool_17: (bool, real, bool) := (true, -14.11, true);
				var v_bool_real_bool_18: (bool, real, bool) := (false, 29.46, true);
				var v_bool_real_bool_19: (bool, real, bool) := (true, -18.67, true);
				var v_bool_real_bool_20: (bool, real, bool) := (true, 5.30, false);
				var v_bool_real_bool_21: (bool, real, bool) := (true, 29.11, false);
				var v_bool_real_bool_22: (bool, real, bool) := (true, 19.32, true);
				var v_bool_real_bool_23: (bool, real, bool) := (false, 26.77, true);
				var v_bool_real_bool_24: (bool, real, bool) := (false, 13.14, true);
				var v_bool_real_bool_25: (bool, real, bool) := (false, 20.75, false);
				var v_bool_real_bool_26: (bool, real, bool) := (true, 21.88, false);
				var v_bool_real_bool_27: (bool, real, bool) := (false, -13.89, false);
				var v_bool_real_bool_28: (bool, real, bool) := (true, -23.97, false);
				var v_map_14: map<int, seq<(bool, real, bool)>> := (if (false) then (map[27 := [v_bool_real_bool_12, v_bool_real_bool_13, v_bool_real_bool_14], 26 := [v_bool_real_bool_15, v_bool_real_bool_16, v_bool_real_bool_17, v_bool_real_bool_18], 21 := [v_bool_real_bool_19, v_bool_real_bool_20, v_bool_real_bool_21]]) else (map[21 := [v_bool_real_bool_22, v_bool_real_bool_23, v_bool_real_bool_24, v_bool_real_bool_25], 28 := [v_bool_real_bool_26, v_bool_real_bool_27, v_bool_real_bool_28]]));
				var v_int_34: int := v_int_29;
				var v_bool_real_bool_29: (bool, real, bool) := (false, -1.12, false);
				var v_bool_real_bool_30: (bool, real, bool) := (false, 23.14, true);
				var v_bool_real_bool_31: (bool, real, bool) := (true, -2.19, true);
				var v_bool_real_bool_32: (bool, real, bool) := (true, 27.71, true);
				var v_seq_13: seq<(bool, real, bool)> := [v_bool_real_bool_29, v_bool_real_bool_30, v_bool_real_bool_31, v_bool_real_bool_32];
				var v_seq_14: seq<(bool, real, bool)> := v_seq_13;
				var v_int_31: int := -21;
				var v_int_32: int := safe_index_seq(v_seq_14, v_int_31);
				var v_int_33: int := v_int_32;
				var v_bool_real_bool_33: (bool, real, bool) := (true, -1.40, false);
				var v_seq_bool_1: (seq<bool>, bool) := ([], true);
				var v_seq_bool_2: (seq<bool>, bool) := ([true, true, true, false], true);
				var v_seq_bool_3: (seq<bool>, bool) := ([false], false);
				var v_seq_bool_4: (seq<bool>, bool) := ([false], false);
				var v_seq_bool_5: (seq<bool>, bool) := ([false, false, false], true);
				var v_seq_bool_6: (seq<bool>, bool) := ([false, false, true], true);
				var v_seq_bool_7: (seq<bool>, bool) := ([true, false], true);
				var v_seq_bool_8: (seq<bool>, bool) := ([false, false, false], false);
				var v_seq_bool_9: (seq<bool>, bool) := ([false, true], false);
				var v_seq_bool_10: (seq<bool>, bool) := ([true, false], false);
				var v_seq_bool_11: (seq<bool>, bool) := ([], true);
				var v_seq_bool_12: (seq<bool>, bool) := ([], true);
				var v_seq_bool_13: (seq<bool>, bool) := ([], true);
				var v_seq_bool_14: (seq<bool>, bool) := ([true, false], false);
				var v_seq_bool_15: (seq<bool>, bool) := ([true], true);
				var v_map_16: map<int, map<bool, (seq<bool>, bool)>> := (if (false) then (map[18 := map[false := v_seq_bool_1, false := v_seq_bool_2], 10 := map[false := v_seq_bool_3, false := v_seq_bool_4, true := v_seq_bool_5], 4 := map[false := v_seq_bool_6, true := v_seq_bool_7], 6 := map[true := v_seq_bool_8, true := v_seq_bool_9], 12 := map[false := v_seq_bool_10, true := v_seq_bool_11]]) else (map[27 := map[true := v_seq_bool_12, false := v_seq_bool_13, false := v_seq_bool_14, true := v_seq_bool_15]]));
				var v_int_35: int := (match 27 {
					case _ => 2
				});
				var v_seq_bool_16: (seq<bool>, bool) := ([false, true, false, true], true);
				var v_seq_bool_17: (seq<bool>, bool) := ([true, false, false], false);
				var v_seq_bool_18: (seq<bool>, bool) := ([], false);
				var v_seq_bool_19: (seq<bool>, bool) := ([false, false, true, false], false);
				var v_seq_bool_20: (seq<bool>, bool) := ([], false);
				var v_seq_bool_21: (seq<bool>, bool) := ([false, true, true], false);
				var v_map_15: map<multiset<real>, map<bool, (seq<bool>, bool)>> := map[multiset{-0.50} := map[true := v_seq_bool_16], multiset{14.88, 19.56, 6.18} := map[false := v_seq_bool_17, false := v_seq_bool_18], multiset{} := map[true := v_seq_bool_19], multiset({14.75, -17.59}) := map[false := v_seq_bool_20, false := v_seq_bool_21]];
				var v_multiset_2: multiset<real> := multiset{};
				var v_seq_bool_22: (seq<bool>, bool) := ([true, false, false, false], true);
				var v_seq_bool_23: (seq<bool>, bool) := ([true], true);
				var v_seq_bool_24: (seq<bool>, bool) := ([true, true, false, false], false);
				var v_seq_bool_25: (seq<bool>, bool) := ([false, true], false);
				var v_seq_bool_26: (seq<bool>, bool) := ([false], true);
				var v_map_18: map<bool, (seq<bool>, bool)> := (if ((v_int_35 in v_map_16)) then (v_map_16[v_int_35]) else ((if ((v_multiset_2 in v_map_15)) then (v_map_15[v_multiset_2]) else (map[false := v_seq_bool_22, false := v_seq_bool_23, false := v_seq_bool_24, true := v_seq_bool_25, true := v_seq_bool_26]))));
				var v_bool_19: bool := v_bool_real_bool_16.2;
				var v_seq_bool_27: (seq<bool>, bool) := ([false, false, false, true], true);
				var v_seq_bool_28: (seq<bool>, bool) := ([], true);
				var v_seq_bool_29: (seq<bool>, bool) := ([true, true], false);
				var v_seq_bool_30: (seq<bool>, bool) := ([], false);
				var v_map_17: map<char, seq<(seq<bool>, bool)>> := map['z' := [v_seq_bool_27, v_seq_bool_28, v_seq_bool_29, v_seq_bool_30]];
				var v_char_9: char := 'l';
				var v_seq_15: seq<(seq<bool>, bool)> := (if ((v_char_9 in v_map_17)) then (v_map_17[v_char_9]) else ([]));
				var v_int_36: int := |[-6, 25, 21, 9]|;
				var v_seq_bool_31: (seq<bool>, bool) := ([true, false], false);
				var v_seq_bool_32: (seq<bool>, bool) := ([], true);
				var v_seq_bool_33: (seq<bool>, bool) := ([false, true], true);
				v_seq_14, v_seq_bool_28 := (if ((if ((true ==> false)) then (v_array_3[0]) else (v_bool_18))) then ((match 22 {
					case _ => (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_30]) else ([v_bool_real_bool_10, v_bool_real_bool_11]))
				})) else ((if ((v_int_34 in v_map_14)) then (v_map_14[v_int_34]) else ((if ((|v_seq_13| > 0)) then (v_seq_13[v_int_33 := v_bool_real_bool_33]) else (v_seq_13)))))), (if ((v_bool_19 in v_map_18)) then (v_map_18[v_bool_19]) else ((if ((|v_seq_15| > 0)) then (v_seq_15[v_int_36]) else ((match 16 {
					case _ => v_seq_bool_33
				})))));
			}
			print "v_map_9", " ", (v_map_9 == map[false := 'C', true := 'E']), " ", "v_map_8", " ", (v_map_8 == map[multiset{} := map[false := 'L'], multiset{multiset{}, multiset{}} := map[false := 'w', true := 'g'], multiset{multiset{}, multiset{-29.61, -25.36, 4.03}, multiset{-16.19, 21.04, -11.73}, multiset{-19.46, -3.07, -21.84}} := map[false := 'g', true := 'P'], multiset{multiset{-14.17, -0.27, 11.22}, multiset{7.72, -6.09}} := map[false := 't', true := 'x']]), " ", "v_char_7", " ", (v_char_7 == 'T'), " ", "v_map_13", " ", (v_map_13 == map[false := false, true := false]), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{multiset{}, multiset{-17.19, 5.94}, multiset{22.65, -21.26}}), " ", "v_bool_12", " ", v_bool_12, " ", "v_char_1", " ", (v_char_1 == 'E'), " ", "v_bool_3", " ", v_bool_3, " ", "v_int_18", " ", v_int_18, " ", "v_bool_4", " ", v_bool_4, " ", "v_array_7[1]", " ", v_array_7[1], " ", "v_array_6[4]", " ", v_array_6[4], " ", "v_array_11[2]", " ", v_array_11[2], " ", "v_array_10[1]", " ", v_array_10[1], " ", "v_array_1[2]", " ", (v_array_1[2] == 28.42), " ", "v_array_3[0]", " ", v_array_3[0], " ", "v_array_9[4]", " ", v_array_9[4], " ", "v_array_4[1]", " ", v_array_4[1], " ", "v_array_8[3]", " ", (v_array_8[3] == v_array_6), " ", "v_array_5[2]", " ", v_array_5[2], " ", "v_array_9[0]", " ", v_array_9[0], " ", "v_array_7[0]", " ", v_array_7[0], " ", "v_array_7[2]", " ", v_array_7[2], " ", "v_array_12[2]", " ", (v_array_12[2] == v_array_11), " ", "v_array_11[1]", " ", v_array_11[1], " ", "v_array_10[0]", " ", v_array_10[0], " ", "v_set_1", " ", (v_set_1 == {map[false := 25.89, true := -21.50], map[false := -11.95, true := -18.83], map[false := -16.74], map[false := 3.46, true := -19.97]}), " ", "v_real_1", " ", (v_real_1 == -16.74), " ", "v_array_9[3]", " ", v_array_9[3], " ", "v_array_8[2]", " ", (v_array_8[2] == v_array_5), " ", "v_array_3[1]", " ", v_array_3[1], " ", "v_array_6[0]", " ", v_array_6[0], " ", "v_array_4[2]", " ", v_array_4[2], " ", "v_bool_1", " ", v_bool_1, " ", "v_array_6[2]", " ", v_array_6[2], " ", "v_array_11", " ", (v_array_11 == v_array_11), " ", "v_array_10", " ", (v_array_10 == v_array_10), " ", "v_array_7[3]", " ", v_array_7[3], " ", "v_array_12[1]", " ", (v_array_12[1] == v_array_10), " ", "v_array_11[0]", " ", v_array_11[0], " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "v_array_5", " ", (v_array_5 == v_array_5), " ", "v_array_6", " ", (v_array_6 == v_array_6), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_1), " ", "v_int_9", " ", v_int_9, " ", "v_array_1[0]", " ", (v_array_1[0] == 1.29), " ", "v_array_5[0]", " ", v_array_5[0], " ", "v_array_7", " ", (v_array_7 == v_array_7), " ", "v_array_9[2]", " ", v_array_9[2], " ", "v_array_8", " ", (v_array_8 == v_array_8), " ", "v_array_4[3]", " ", v_array_4[3], " ", "v_array_8[1]", " ", (v_array_8[1] == v_array_4), " ", "v_array_9", " ", (v_array_9 == v_array_9), " ", "v_array_3[2]", " ", v_array_3[2], " ", "v_array_6[1]", " ", v_array_6[1], " ", "v_array_12", " ", (v_array_12 == v_array_12), " ", "v_array_6[3]", " ", v_array_6[3], " ", "v_array_10[2]", " ", v_array_10[2], " ", "v_array_12[0]", " ", (v_array_12[0] == v_array_9), " ", "v_map_1", " ", (v_map_1 == map[19 := map[false := -4.48, true := 23.10], 20 := map[false := 27.73], 22 := map[false := -5.00], 25 := map[true := 19.38], 9 := map[false := -7.96], 10 := map[false := 24.08], 13 := map[false := -23.57]]), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_seq_7", " ", (v_seq_7 == []), " ", "v_int_11", " ", v_int_11, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_10", " ", v_int_10, " ", "v_seq_5", " ", (v_seq_5 == [v_array_8, v_array_12]), " ", "v_seq_4", " ", (v_seq_4 == []), " ", "v_seq_3", " ", (v_seq_3 == [{}, {true}, {false}, {false, true}]), " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_array_1[1]", " ", (v_array_1[1] == 13.91), " ", "v_array_8[4]", " ", (v_array_8[4] == v_array_7), " ", "v_array_3[3]", " ", v_array_3[3], " ", "v_array_4[0]", " ", v_array_4[0], " ", "v_array_9[1]", " ", v_array_9[1], " ", "v_array_5[1]", " ", v_array_5[1], " ", "v_array_8[0]", " ", (v_array_8[0] == v_array_3), "\n";
			return ;
		}
		var v_seq_16: seq<seq<int>> := [[], [6, 21, 23, 26]];
		var v_seq_17: seq<seq<int>> := v_seq_16;
		var v_int_39: int := 11;
		var v_int_40: int := safe_index_seq(v_seq_17, v_int_39);
		var v_int_41: int := v_int_40;
		var v_seq_18: seq<seq<int>> := (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_41 := [17, 2]]) else (v_seq_16));
		var v_int_42: int := v_int_13;
		var v_seq_19: seq<int> := (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_42]) else (v_seq_6));
		var v_int_43: int := v_int_39;
		var v_DT_1_1_11: DT_1<char, multiset<bool>> := DT_1_1;
		var v_DT_1_1_12: DT_1<char, multiset<bool>> := DT_1_1;
		var v_DT_1_1_13: DT_1<char, multiset<bool>> := DT_1_1;
		var v_DT_1_1_14: DT_1<char, multiset<bool>> := DT_1_1;
		var v_DT_1_1_15: DT_1<char, multiset<bool>> := DT_1_1;
		var v_array_15: array<DT_1<char, multiset<bool>>> := new DT_1<char, multiset<bool>>[5] [v_DT_1_1_11, v_DT_1_1_12, v_DT_1_1_13, v_DT_1_1_14, v_DT_1_1_15];
		var v_DT_1_1_16: DT_1<char, multiset<bool>> := DT_1_1;
		var v_DT_1_1_17: DT_1<char, multiset<bool>> := DT_1_1;
		var v_DT_1_1_18: DT_1<char, multiset<bool>> := DT_1_1;
		var v_DT_1_1_19: DT_1<char, multiset<bool>> := DT_1_1;
		var v_DT_1_1_20: DT_1<char, multiset<bool>> := DT_1_1;
		var v_array_16: array<DT_1<char, multiset<bool>>> := new DT_1<char, multiset<bool>>[5] [v_DT_1_1_16, v_DT_1_1_17, v_DT_1_1_18, v_DT_1_1_19, v_DT_1_1_20];
		var v_int_37: int := (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_43]) else ((if (false) then (v_array_15) else (v_array_16)).Length));
		var v_int_38: int := v_int_39;
		while (v_int_37 < v_int_38) 
			decreases v_int_38 - v_int_37;
			invariant (v_int_37 <= v_int_38);
		{
			v_int_37 := (v_int_37 + 1);
			var v_seq_20: seq<set<int>> := [{17, 23, 24}, {1, 7, 14}, {6}, {0}];
			var v_int_44: int := 23;
			var v_map_19: map<set<multiset<real>>, set<int>> := map[{} := {-6, 3}, {multiset{-29.48, 18.93, 3.31}, multiset{26.15, 0.73}, multiset{-17.99, 4.67, -4.92}, multiset({-18.31, 29.23, -2.09})} := {2, 22, 29, 0}, {multiset({}), multiset{22.45, 3.45}, multiset({-13.57, 12.37, 16.10})} := {}, {} := {2, 14}];
			var v_set_3: set<multiset<real>> := {multiset({-6.82, -4.19, -0.49, 29.05})};
			var v_seq_21: seq<set<set<int>>> := [{{5, 18, 29}, {1, 23, 0, 19}, {7, 27}}];
			var v_seq_23: seq<set<set<int>>> := (match 22 {
				case _ => ([{}] + [])
			});
			var v_array_17: array<int> := new int[3] [10, 26, 12];
			var v_array_18: array<int> := new int[3] [23, 12, 29];
			var v_array_19: array<int> := new int[5] [7, 25, 24, 24, 2];
			var v_seq_22: seq<array<int>> := [v_array_17, v_array_18, v_array_19];
			var v_int_45: int := -27;
			var v_array_20: array<int> := new int[5] [0, 12, 9, -27, 0];
			var v_int_46: int := (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_45]) else (v_array_20)).Length;
			var v_seq_24: seq<set<set<int>>> := ([{{2, 21, 29, 6}, {16, 27}, {10, 6, -8, 12}}] + [{{-24, 3, 9}, {}}, {}, {{25}, {-13, 10, 0}}, {{}}]);
			var v_int_47: int := (if (false) then (4) else (0));
			var v_map_20: map<int, seq<set<set<bool>>>> := map[9 := [{{true, true}, {true, true, false}, {}, {false, true, false}}, {{false, true}, {true, false, true, false}, {false}}, {{false, true}, {true}, {true, true, false, true}, {}}, {{false}, {true}, {false, false, false}, {true, true}}], 22 := [{{true}, {true, true, false}, {}, {}}, {{false, false}}, {{false}, {false, false}, {false}}], 11 := [{{false, true, true}, {true, false}, {true, false, true, true}}], -4 := [{{}, {false, true}, {}, {true}}, {{}, {true, false, true}, {false, true, false}}, {{}, {}, {true, false}, {true, true}}, {{true, true, false}, {true}}]];
			var v_int_48: int := 9;
			var v_seq_25: seq<set<set<bool>>> := (if ((v_int_48 in v_map_20)) then (v_map_20[v_int_48]) else ([{{false, false}, {true, true, true, true}, {false, true, true}, {}}, {{true}, {true, true, false}, {true, false, true, true}, {true, true, true}}, {{true, true, true, true}}, {{false}, {true, false, false}}]));
			var v_int_49: int := v_int_11;
			var v_seq_26: seq<set<set<bool>>> := [{{false, false, false}, {false, true}, {true, true, true, true}}, {{}, {true}, {}, {false, false, true, false}}, {{true}, {false, true}}, {{false}, {true, true, true}, {false, false, false, true}}];
			var v_int_50: int := 11;
			var v_seq_27: seq<map<int, set<set<bool>>>> := [map[24 := {{}, {true}, {}, {true, false, false, false}}, -6 := {{true}, {false, true}, {}, {}}, 7 := {{false, false, false, false}, {true, false, true}, {false, true, false, false}}, 13 := {{false, true}, {}, {false, false, false, false}}, 22 := {{}, {false, true}, {false, false, false, true}}], map[26 := {{true, true, true, false}, {}, {false, true, false}, {false, true, false, false}}], map[8 := {}, 25 := {{true}, {}, {true, false}, {true, false, false}}, 17 := {{true, false}, {true, true, true}, {false, false}}]];
			var v_int_51: int := 29;
			var v_map_21: map<int, set<set<bool>>> := (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_51]) else (map[20 := {}, 3 := {{true}, {}, {true}}]));
			var v_int_52: int := v_array_19[1];
			var v_int_53: int, v_set_4: set<int>, v_set_5: set<set<int>>, v_char_10: char, v_set_6: set<set<bool>> := v_int_40, ((({} * {13, 24, 5}) - (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_44]) else ({24, 12}))) + (if (v_array_6[4]) then ((if ((v_set_3 in v_map_19)) then (v_map_19[v_set_3]) else ({12, 10}))) else ((map[27 := 16.76, 4 := 23.83, 13 := -27.04]).Keys))), (if ((|v_seq_23| > 0)) then (v_seq_23[v_int_46]) else ((if ((|v_seq_24| > 0)) then (v_seq_24[v_int_47]) else ((if (false) then ({{}}) else ({})))))), v_char_1, (match 29 {
				case _ => (if ((v_int_52 in v_map_21)) then (v_map_21[v_int_52]) else ((if (true) then ({{false}, {false}, {true, false}, {true}}) else ({{}, {true, false}}))))
			});
			var v_seq_28: seq<int> := [9, 28];
			var v_seq_29: seq<int> := v_seq_28;
			var v_int_54: int := 3;
			var v_int_55: int := safe_index_seq(v_seq_29, v_int_54);
			var v_int_56: int := v_int_55;
			var v_seq_30: seq<int> := (if ((|v_seq_28| > 0)) then (v_seq_28[v_int_56 := 6]) else (v_seq_28));
			var v_seq_31: seq<int> := v_seq_30;
			var v_map_22: map<int, int> := map[22 := -22, 11 := -29, -22 := 28, 5 := 20];
			var v_int_57: int := 18;
			var v_int_58: int := (if ((v_int_57 in v_map_22)) then (v_map_22[v_int_57]) else (27));
			var v_int_59: int := safe_index_seq(v_seq_31, v_int_58);
			var v_int_60: int := v_int_59;
			var v_seq_34: seq<int> := (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_60 := |{23}|]) else (v_seq_30));
			var v_seq_32: seq<map<int, int>> := [];
			var v_int_61: int := 18;
			var v_map_24: map<int, int> := (if ((|v_seq_32| > 0)) then (v_seq_32[v_int_61]) else (map[19 := 5, 28 := 16, 6 := 4]));
			var v_map_23: map<int, int> := map[27 := 9, 29 := 8, 6 := 21, 16 := 21];
			var v_int_62: int := 10;
			var v_int_64: int := (if ((v_int_62 in v_map_23)) then (v_map_23[v_int_62]) else (26));
			var v_seq_33: seq<int> := [4];
			var v_int_63: int := 5;
			var v_int_65: int := (if ((v_int_64 in v_map_24)) then (v_map_24[v_int_64]) else ((if ((|v_seq_33| > 0)) then (v_seq_33[v_int_63]) else (29))));
			v_int_54, v_array_18[2] := (if ((|v_seq_34| > 0)) then (v_seq_34[v_int_65]) else ((v_real_1).Floor)), v_int_40;
			var v_int_int_int_1: (int, int, int) := (14, 23, 0);
			var v_int_int_int_2: (int, int, int) := (11, 5, 5);
			var v_int_int_int_3: (int, int, int) := (10, 26, 20);
			var v_int_int_int_4: (int, int, int) := (27, 17, -23);
			var v_int_int_int_5: (int, int, int) := (0, 21, 26);
			var v_int_int_int_6: (int, int, int) := (17, 5, 16);
			var v_int_int_int_7: (int, int, int) := (23, 3, 8);
			var v_map_26: map<(int, int, int), int> := (if ((match 26 {
				case _ => false
			})) then (map[v_int_int_int_1 := 24, v_int_int_int_2 := 9, v_int_int_int_3 := -28, v_int_int_int_4 := -6][v_int_int_int_5 := 19]) else (map[v_int_int_int_6 := 1][v_int_int_int_7 := 14]));
			var v_int_int_int_8: (int, int, int) := (10, 3, 3);
			var v_int_int_int_9: (int, int, int) := (-6, -27, 22);
			var v_int_int_int_10: (int, int, int) := (24, -23, 0);
			var v_int_int_int_11: (int, int, int) := (18, 4, 9);
			var v_int_int_int_12: (int, int, int) := (0, -1, 14);
			var v_int_int_int_13: (int, int, int) := (24, -5, -12);
			var v_int_int_int_14: (int, int, int) := (-25, 10, -5);
			var v_int_int_int_15: (int, int, int) := (21, 21, 5);
			var v_map_25: map<char, (int, int, int)> := (if (true) then (map['Y' := v_int_int_int_8, 'h' := v_int_int_int_9, 'y' := v_int_int_int_10]) else (map['B' := v_int_int_int_11, 'Y' := v_int_int_int_12, 'W' := v_int_int_int_13, 'N' := v_int_int_int_14, 'm' := v_int_int_int_15]));
			var v_char_11: char := v_char_1;
			var v_int_int_int_16: (int, int, int) := (11, 26, 8);
			var v_int_int_int_17: (int, int, int) := (24, 1, 14);
			var v_int_int_int_18: (int, int, int) := (if ((v_char_11 in v_map_25)) then (v_map_25[v_char_11]) else ((if (false) then (v_int_int_int_16) else (v_int_int_int_17))));
			var v_seq_35: seq<int> := (([18, 24, -26, 18] + [18]) + v_seq_31);
			var v_int_66: int := v_int_int_int_9.1;
			var v_map_27: map<int, int> := map[7 := 24, 6 := 21, 1 := 13, 27 := 14];
			var v_int_67: int := 23;
			var v_map_28: map<int, int> := (map[19 := 20, 6 := 8, -16 := 27, 5 := 2, 1 := 2] - {})[v_int_int_int_13.2 := (if ((v_int_67 in v_map_27)) then (v_map_27[v_int_67]) else (26))];
			var v_int_72: int := v_int_55;
			var v_seq_36: seq<int> := [23, 28, 23];
			var v_seq_37: seq<int> := v_seq_36;
			var v_int_68: int := -14;
			var v_int_69: int := safe_index_seq(v_seq_37, v_int_68);
			var v_int_70: int := v_int_69;
			var v_seq_38: seq<int> := (if ((|v_seq_36| > 0)) then (v_seq_36[v_int_70 := 12]) else (v_seq_36));
			var v_int_71: int := (match 'O' {
				case _ => 26
			});
			var v_map_29: map<char, map<char, int>> := map['D' := map['x' := 25], 'I' := map['S' := 24], 'y' := map['c' := 3, 'u' := 22], 'p' := map['s' := 4, 'M' := 29, 'h' := 25], 'f' := map['w' := 18, 'c' := 2, 'x' := 11, 'Y' := -23, 'D' := 2]];
			var v_char_12: char := 'w';
			var v_map_31: map<char, int> := (match 'm' {
				case _ => (if ((v_char_12 in v_map_29)) then (v_map_29[v_char_12]) else (map['w' := 25, 'K' := 3]))
			});
			var v_seq_39: seq<char> := ['j', 'N', 'b'];
			var v_seq_40: seq<char> := (if ((|v_seq_39| > 0)) then (v_seq_39[-6..24]) else (v_seq_39));
			var v_int_73: int := (if (false) then (14) else (2));
			var v_char_14: char := (if ((|v_seq_40| > 0)) then (v_seq_40[v_int_73]) else ((match 'Z' {
				case _ => 'L'
			})));
			var v_seq_41: seq<int> := v_seq_6;
			var v_int_74: int := (-29 / 28);
			var v_map_30: map<char, int> := map['c' := 2, 'e' := 12];
			var v_char_13: char := 'C';
			v_array_18[2], v_array_19[3], v_int_53, v_int_58, v_int_9 := (if ((v_int_int_int_18 in v_map_26)) then (v_map_26[v_int_int_int_18]) else (v_int_int_int_3.0)), (if ((|v_seq_35| > 0)) then (v_seq_35[v_int_66]) else (v_array_20[3])), (if ((v_int_72 in v_map_28)) then (v_map_28[v_int_72]) else ((if ((|v_seq_38| > 0)) then (v_seq_38[v_int_71]) else (v_int_39)))), v_array_18[1], (if ((v_char_14 in v_map_31)) then (v_map_31[v_char_14]) else ((if ((|v_seq_41| > 0)) then (v_seq_41[v_int_74]) else ((if ((v_char_13 in v_map_30)) then (v_map_30[v_char_13]) else (7))))));
			var v_map_34: map<char, bool> := (map['G' := false, 'j' := false, 'O' := true, 's' := false, 'B' := true] + map['z' := false, 'l' := true, 'S' := true, 'W' := false, 'F' := false])[(if (true) then ('m') else ('l')) := (false && true)];
			var v_char_17: char := (if ((['i', 'C'] < [])) then (v_char_1) else ((match 'W' {
				case _ => 'W'
			})));
			var v_map_32: map<char, int> := map['y' := 13, 'W' := 29, 'O' := 6];
			var v_char_15: char := 'K';
			var v_map_33: map<char, int> := map['z' := 12, 'g' := 18, 'v' := 26];
			var v_char_16: char := 'R';
			if (if ((v_char_17 in v_map_34)) then (v_map_34[v_char_17]) else (((if ((v_char_15 in v_map_32)) then (v_map_32[v_char_15]) else (2)) <= (if ((v_char_16 in v_map_33)) then (v_map_33[v_char_16]) else (21))))) {
				
			} else {
				var v_seq_42: seq<int> := v_seq_36;
				var v_map_35: map<char, int> := (map['E' := -3] - {'g', 'B', 'T', 'j'});
				var v_char_18: char := v_char_10;
				var v_array_21: array<char> := new char[5] ['i', 'O', 'B', 'x', 't'];
				var v_int_77: int := (if ((v_char_18 in v_map_35)) then (v_map_35[v_char_18]) else (v_array_21.Length));
				var v_map_36: map<char, seq<int>> := map['M' := [4, 29, 28]];
				var v_char_19: char := 'F';
				var v_seq_44: seq<int> := (if ((v_char_19 in v_map_36)) then (v_map_36[v_char_19]) else ([3, 10, 26]));
				var v_seq_43: seq<int> := [-26, 21, 19, 20];
				var v_int_78: int := 13;
				var v_int_79: int := (if ((|v_seq_43| > 0)) then (v_seq_43[v_int_78]) else (28));
				var v_map_37: map<char, int> := map['r' := 23, 'Z' := 15];
				var v_char_20: char := 'B';
				var v_int_75: int := (if ((|v_seq_42| > 0)) then (v_seq_42[v_int_77]) else ((if ((|v_seq_44| > 0)) then (v_seq_44[v_int_79]) else ((if ((v_char_20 in v_map_37)) then (v_map_37[v_char_20]) else (20))))));
				var v_map_38: map<char, map<char, int>> := map['z' := map['U' := 24, 'o' := 20], 'J' := map['K' := 2, 'e' := 22, 'Z' := 13, 'e' := 15], 'T' := map['Q' := 17], 'A' := map['F' := 16, 'K' := 3, 'z' := 25, 'e' := 2]];
				var v_char_21: char := 'R';
				var v_map_39: map<char, int> := (match 'P' {
					case _ => (if (false) then (map['t' := 6, 'c' := 27, 'D' := 24, 'd' := 12]) else (map['C' := 10, 'f' := 24]))
				});
				var v_seq_45: seq<char> := (['g'] + ['p', 'u', 'S']);
				var v_int_80: int := (if (false) then (14) else (14));
				var v_seq_46: seq<char> := ['u', 'R'];
				var v_int_81: int := 20;
				var v_char_22: char := (if ((|v_seq_45| > 0)) then (v_seq_45[v_int_80]) else ((if ((|v_seq_46| > 0)) then (v_seq_46[v_int_81]) else ('N'))));
				var v_seq_47: seq<int> := [23, 14];
				var v_int_82: int := 14;
				var v_seq_48: seq<int> := [-27];
				var v_int_83: int := 9;
				var v_int_76: int := (if ((v_char_22 in v_map_39)) then (v_map_39[v_char_22]) else ((if (('r' in {'r'})) then ((if ((|v_seq_47| > 0)) then (v_seq_47[v_int_82]) else (22))) else ((if ((|v_seq_48| > 0)) then (v_seq_48[v_int_83]) else (20))))));
				while (v_int_75 < v_int_76) 
					decreases v_int_76 - v_int_75;
					invariant (v_int_75 <= v_int_76);
				{
					v_int_75 := (v_int_75 + 1);
					return ;
				}
				if v_array_11[0] {
					
				} else {
					
				}
				var v_seq_50: seq<int> := (match 'G' {
					case _ => []
				});
				var v_seq_49: seq<int> := [15];
				var v_int_85: int := 7;
				var v_int_86: int := (if ((|v_seq_49| > 0)) then (v_seq_49[v_int_85]) else (16));
				var v_map_40: map<char, int> := map['l' := 22, 'j' := 7];
				var v_char_23: char := 'B';
				var v_map_41: map<char, int> := (match 'M' {
					case _ => map['O' := 25]
				});
				var v_char_24: char := v_char_19;
				var v_int_87: int, v_int_88: int := v_int_int_int_10.0, (match 'R' {
					case _ => (if ((v_char_24 in v_map_41)) then (v_map_41[v_char_24]) else ((if (false) then (26) else (23))))
				});
				for v_int_84 := v_int_87 to v_int_88 
					invariant (v_int_88 - v_int_84 >= 0)
				{
					return ;
				}
				assert true;
				expect true;
				return ;
			}
			var v_seq_51: seq<bool> := [false, false];
			var v_int_89: int := 17;
			var v_seq_52: seq<bool> := [false, true];
			var v_int_90: int := 28;
			var v_seq_53: seq<bool> := [];
			var v_int_91: int := 7;
			if (if ((match 'S' {
				case _ => v_array_4[1]
			})) then ((if ((if ((|v_seq_51| > 0)) then (v_seq_51[v_int_89]) else (true))) then (v_array_9[0]) else ((if ((|v_seq_52| > 0)) then (v_seq_52[v_int_90]) else (false))))) else ((if ((match 'w' {
				case _ => true
			})) then (({'S', 'x', 'D'} != {'x', 'a'})) else ((if ((|v_seq_53| > 0)) then (v_seq_53[v_int_91]) else (true)))))) {
				
			} else {
				var v_map_42: map<char, seq<seq<bool>>> := map['U' := [[true, false, true], []], 'd' := [[false, false, true, true], [], [false, true], [false]], 'K' := [[], [true, false]]];
				var v_char_25: char := 'A';
				var v_seq_54: seq<seq<bool>> := (if ((v_char_25 in v_map_42)) then (v_map_42[v_char_25]) else ([[true, true], [], [], []]));
				var v_int_92: int := (if (true) then (-20) else (23));
				var v_seq_55: seq<bool> := [false];
				var v_seq_56: seq<bool> := v_seq_55;
				var v_int_93: int := 3;
				var v_int_94: int := safe_index_seq(v_seq_56, v_int_93);
				var v_int_95: int := v_int_94;
				var v_seq_58: seq<bool> := (if ((|v_seq_54| > 0)) then (v_seq_54[v_int_92]) else ((if ((|v_seq_55| > 0)) then (v_seq_55[v_int_95 := false]) else (v_seq_55))));
				var v_seq_57: seq<int> := [5];
				var v_int_96: int := -14;
				var v_int_97: int := (if (v_array_9[0]) then ((match 'E' {
					case _ => 0
				})) else ((if ((|v_seq_57| > 0)) then (v_seq_57[v_int_96]) else (10))));
				var v_map_43: map<char, bool> := map['z' := false, 'z' := false];
				var v_char_26: char := 'T';
				var v_map_44: map<char, bool> := map['y' := true, 'E' := true, 'y' := false];
				var v_char_27: char := 'G';
				if (if ((|v_seq_58| > 0)) then (v_seq_58[v_int_97]) else ((if ((if ((v_char_26 in v_map_43)) then (v_map_43[v_char_26]) else (true))) then ((match 'S' {
					case _ => false
				})) else ((if ((v_char_27 in v_map_44)) then (v_map_44[v_char_27]) else (false)))))) {
					
				} else {
					return ;
				}
				return ;
			}
		}
	}
	var v_map_45: map<char, bool> := map['j' := false, 'x' := false, 'E' := true, 'O' := false, 'I' := true];
	var v_char_28: char := 'J';
	if (((match 'F' {
		case _ => multiset{'S', 'e', 'L'}
	}) != (multiset{'S'} - multiset({'s'}))) || (match 'B' {
		case _ => v_array_10[1]
	})) {
		var v_map_46: map<char, char> := map['f' := 'H', 'T' := 'v', 'q' := 't'];
		var v_char_29: char := 'd';
		var v_seq_59: seq<set<char>> := [{}, {'C', 'B'}];
		var v_int_98: int := 3;
		var v_seq_60: seq<bool> := [];
		var v_int_99: int := 1;
		if (if (((if ((v_char_29 in v_map_46)) then (v_map_46[v_char_29]) else ('M')) in (if ((|v_seq_59| > 0)) then (v_seq_59[v_int_98]) else ({'h'})))) then ((match 'g' {
			case _ => (if ((|v_seq_60| > 0)) then (v_seq_60[v_int_99]) else (false))
		})) else (((match 'L' {
			case _ => multiset{'E'}
		}) <= (multiset({'d', 'x', 'U'}) + multiset{'K', 'C'})))) {
			assert true;
			expect true;
			var v_map_47: map<char, bool> := map['h' := true, 'q' := true, 'M' := false]['p' := false];
			var v_char_30: char := v_char_29;
			var v_map_48: map<char, char> := map['K' := 'P', 'a' := 'X', 'M' := 't']['B' := 'A'];
			var v_char_31: char := (if (false) then ('Z') else ('K'));
			var v_map_49: map<char, bool> := map['G' := true];
			var v_char_32: char := 'u';
			var v_map_52: map<char, char> := (if ((if ((v_char_32 in v_map_49)) then (v_map_49[v_char_32]) else (true))) then ((match 'x' {
				case _ => map['c' := 'j', 'O' := 'p']
			})) else (map['q' := 'f', 'r' := 'f', 'h' := 'N']['u' := 'C']));
			var v_seq_61: seq<bool> := [true, false, false, true];
			var v_int_100: int := -16;
			var v_map_50: map<char, char> := map['G' := 'v', 'b' := 's'];
			var v_char_33: char := 'i';
			var v_map_51: map<char, char> := map['U' := 'u', 'M' := 'P', 'A' := 'J', 'i' := 'y', 't' := 'F'];
			var v_char_34: char := 'i';
			var v_char_35: char := (if ((if ((|v_seq_61| > 0)) then (v_seq_61[v_int_100]) else (false))) then ((if ((v_char_33 in v_map_50)) then (v_map_50[v_char_33]) else ('H'))) else ((if ((v_char_34 in v_map_51)) then (v_map_51[v_char_34]) else ('Q'))));
			var v_seq_62: seq<char> := ['f', 'g', 'X', 'o'];
			var v_seq_63: seq<char> := v_seq_62;
			var v_int_101: int := 27;
			var v_int_102: int := safe_index_seq(v_seq_63, v_int_101);
			var v_int_103: int := v_int_102;
			var v_seq_64: seq<char> := (if ((|v_seq_62| > 0)) then (v_seq_62[v_int_103 := 'Z']) else (v_seq_62));
			var v_int_104: int := |map['Z' := 'I', 'M' := 'q', 'E' := 'C']|;
			var v_seq_65: seq<char> := ['V', 'g', 'y', 'c'];
			var v_seq_66: seq<char> := (if ((|v_seq_65| > 0)) then (v_seq_65[4..21]) else (v_seq_65));
			var v_int_105: int := (4 - 17);
			v_char_33, v_char_35, v_char_29, v_char_30, v_char_31 := (if ((if ((v_char_30 in v_map_47)) then (v_map_47[v_char_30]) else (v_array_7[3]))) then (v_char_30) else ((if ((v_char_31 in v_map_48)) then (v_map_48[v_char_31]) else ((if (false) then ('i') else ('L')))))), (if ((v_char_35 in v_map_52)) then (v_map_52[v_char_35]) else ((if ((|v_seq_64| > 0)) then (v_seq_64[v_int_104]) else (v_char_33)))), v_char_32, v_char_32, (match 'Z' {
				case _ => (if ((|v_seq_66| > 0)) then (v_seq_66[v_int_105]) else ((if (false) then ('s') else ('z'))))
			});
			var v_seq_68: seq<bool> := v_seq_61;
			var v_seq_67: seq<int> := [26];
			var v_int_106: int := -15;
			var v_int_107: int := (if ((|v_seq_67| > 0)) then (v_seq_67[v_int_106]) else (26));
			var v_seq_69: seq<char> := ['l', 'Q'];
			var v_seq_71: seq<char> := (if ((|v_seq_69| > 0)) then (v_seq_69[5..0]) else (v_seq_69));
			var v_seq_70: seq<int> := [];
			var v_int_108: int := 5;
			var v_int_109: int := (if ((|v_seq_70| > 0)) then (v_seq_70[v_int_108]) else (19));
			var v_map_53: map<char, bool> := map['A' := false, 'r' := true, 'P' := true, 'I' := true];
			var v_char_36: char := 's';
			var v_map_54: map<char, map<char, char>> := map['h' := map['R' := 'h', 'D' := 'R', 'm' := 'o', 'i' := 'm'], 'k' := map['F' := 'T', 'l' := 'z', 'v' := 'G', 'R' := 'C', 'Q' := 'x'], 'o' := map['C' := 'q', 'f' := 'Z']];
			var v_char_37: char := 'B';
			var v_map_56: map<char, char> := (if ((v_char_37 in v_map_54)) then (v_map_54[v_char_37]) else (map['C' := 'l', 'Z' := 'u', 'P' := 'W', 'i' := 'G', 'M' := 'C']));
			var v_map_55: map<char, char> := map['z' := 'j', 'f' := 'z', 'e' := 't', 'b' := 'l', 'z' := 'a'];
			var v_char_38: char := 'B';
			var v_char_39: char := (if ((v_char_38 in v_map_55)) then (v_map_55[v_char_38]) else ('g'));
			var v_map_57: map<char, char> := map['V' := 's', 'Z' := 'I', 'i' := 'q', 'K' := 'c', 'l' := 'v'];
			var v_char_40: char := 'b';
			var v_map_58: map<char, char> := map['q' := 'X', 'J' := 'o', 'o' := 'p', 'T' := 'K', 'Q' := 'w'];
			var v_char_41: char := 'Y';
			v_char_33, v_char_30, v_char_34 := (if (!(v_array_7[0])) then ((if ((match 'Z' {
				case _ => true
			})) then ((if (false) then ('j') else ('S'))) else (v_char_30))) else (v_char_29)), (if ((if ((|v_seq_68| > 0)) then (v_seq_68[v_int_107]) else ((if (true) then (true) else (false))))) then ((if ((|v_seq_71| > 0)) then (v_seq_71[v_int_109]) else ((match 'k' {
				case _ => 'q'
			})))) else (v_char_32)), (match 'S' {
				case _ => (match 'y' {
					case _ => (if ((v_char_41 in v_map_58)) then (v_map_58[v_char_41]) else ('l'))
				})
			});
			var v_map_59: map<char, char> := map['c' := 'V', 'N' := 'F'];
			var v_char_42: char := 'C';
			var v_map_60: map<char, char> := map['s' := 'G'];
			var v_char_43: char := 'h';
			var v_seq_72: seq<char> := ['O', 'k', 'h'];
			var v_seq_73: seq<char> := v_seq_72;
			var v_int_110: int := 25;
			var v_int_111: int := safe_index_seq(v_seq_73, v_int_110);
			var v_int_112: int := v_int_111;
			var v_seq_75: seq<char> := (if ((|v_seq_72| > 0)) then (v_seq_72[v_int_112 := 'g']) else (v_seq_72));
			var v_seq_74: seq<int> := [15, 13, 0, 21];
			var v_int_113: int := 11;
			var v_int_114: int := (if ((|v_seq_74| > 0)) then (v_seq_74[v_int_113]) else (17));
			var v_seq_76: seq<char> := [];
			var v_int_115: int := 22;
			v_char_30, v_char_31 := (match 'S' {
				case _ => (if ((|v_seq_75| > 0)) then (v_seq_75[v_int_114]) else ((if ((|v_seq_76| > 0)) then (v_seq_76[v_int_115]) else ('b'))))
			}), v_char_33;
			var v_seq_77: seq<int> := [-5, 8, 27];
			var v_seq_78: seq<int> := (if ((|v_seq_77| > 0)) then (v_seq_77[28..-21]) else (v_seq_77));
			var v_int_118: int := (match 'm' {
				case _ => 12
			});
			var v_map_61: map<char, int> := map['X' := 29, 'T' := 7, 'T' := 24]['h' := 11];
			var v_char_44: char := (if (false) then ('h') else ('e'));
			var v_seq_79: seq<int> := [28];
			var v_int_119: int := 22;
			var v_int_116: int := (match 'U' {
				case _ => (match 'W' {
					case _ => v_int_98
				})
			});
			var v_seq_80: seq<bool> := [false, false, false];
			var v_seq_82: seq<bool> := (if ((|v_seq_80| > 0)) then (v_seq_80[26..24]) else (v_seq_80));
			var v_seq_81: seq<int> := [18];
			var v_int_120: int := 1;
			var v_int_121: int := (if ((|v_seq_81| > 0)) then (v_seq_81[v_int_120]) else (18));
			var v_map_62: map<char, int> := (if (true) then (map['u' := 22, 'M' := 8]) else (map['c' := 20, 'R' := 3]));
			var v_char_45: char := v_char_29;
			var v_seq_83: seq<int> := [20, 8, 25, 25];
			var v_int_122: int := 7;
			var v_int_117: int := (if ((if ((|v_seq_82| > 0)) then (v_seq_82[v_int_121]) else ((6 == 24)))) then (v_int_15) else ((if ((v_char_45 in v_map_62)) then (v_map_62[v_char_45]) else ((if ((|v_seq_83| > 0)) then (v_seq_83[v_int_122]) else (18))))));
			while (v_int_116 < v_int_117) 
				decreases v_int_117 - v_int_116;
				invariant (v_int_116 <= v_int_117);
			{
				v_int_116 := (v_int_116 + 1);
				var v_map_63: map<char, int> := map['x' := 9, 'k' := 4, 'u' := -17];
				var v_char_46: char := 'J';
				var v_seq_84: seq<multiset<char>> := [];
				var v_int_125: int := 7;
				var v_int_123: int := ((match 'G' {
					case _ => (if ((v_char_46 in v_map_63)) then (v_map_63[v_char_46]) else (-4))
				}) + |(if ((|v_seq_84| > 0)) then (v_seq_84[v_int_125]) else (multiset{'M', 'e', 'G'}))|);
				var v_int_124: int := v_int_12;
				while (v_int_123 < v_int_124) 
					decreases v_int_124 - v_int_123;
					invariant (v_int_123 <= v_int_124);
				{
					v_int_123 := (v_int_123 + 1);
					return ;
				}
				if v_array_6[0] {
					return ;
				}
				match v_char_33 {
					case _ => {
						return ;
					}
					
				}
				
			}
			assert true;
			expect true;
			return ;
		} else {
			return ;
		}
	}
	var v_seq_85: seq<int> := [28, 25, 27];
	var v_seq_86: seq<int> := (if ((|v_seq_85| > 0)) then (v_seq_85[11..0]) else (v_seq_85));
	var v_map_64: map<char, int> := map['L' := -4, 'b' := 0, 'T' := 18, 'b' := 20, 'X' := 21];
	var v_char_47: char := 'U';
	var v_int_127: int := (if ((v_char_47 in v_map_64)) then (v_map_64[v_char_47]) else (22));
	var v_seq_87: seq<int> := [13];
	var v_int_128: int := 26;
	var v_array_22: array<char> := new char[3] ['v', 'E', 'g'];
	var v_array_23: array<char> := new char[3] ['L', 'H', 'f'];
	var v_array_24: array<char> := new char[4] ['o', 'e', 'u', 'j'];
	var v_seq_88: seq<array<char>> := [v_array_22, v_array_23, v_array_24];
	var v_int_129: int := 8;
	var v_array_25: array<char> := new char[4] ['J', 'H', 'r', 'H'];
	var v_array_26: array<char> := new char[5] ['o', 'x', 'q', 's', 'p'];
	var v_array_27: array<char> := new char[4] ['q', 'V', 'W', 'S'];
	var v_seq_89: seq<array<char>> := [v_array_26, v_array_27];
	var v_int_130: int := 11;
	var v_array_28: array<char> := new char[4] ['M', 'c', 'A', 'T'];
	var v_int_175: int, v_int_176: int := (match 'x' {
		case _ => (match 'm' {
			case _ => v_int_10
		})
	}), (if ((if (true) then (true) else (true))) then ((if ((|v_seq_88| > 0)) then (v_seq_88[v_int_129]) else (v_array_25))) else ((if ((|v_seq_89| > 0)) then (v_seq_89[v_int_130]) else (v_array_28)))).Length;
	for v_int_126 := v_int_175 to v_int_176 
		invariant (v_int_176 - v_int_126 >= 0)
	{
		var v_map_65: map<char, int> := map['q' := 7, 'U' := 16];
		var v_char_48: char := 'Q';
		var v_map_66: map<char, int> := map['I' := 21, 'S' := 14, 'V' := 22];
		var v_char_49: char := 'o';
		var v_seq_90: seq<int> := [];
		var v_int_132: int := 6;
		var v_seq_91: seq<bool> := [false, false];
		var v_seq_92: seq<bool> := v_seq_91;
		var v_int_133: int := 19;
		var v_int_134: int := safe_index_seq(v_seq_92, v_int_133);
		var v_int_135: int := v_int_134;
		var v_seq_94: seq<bool> := (if ((|v_seq_91| > 0)) then (v_seq_91[v_int_135 := true]) else (v_seq_91));
		var v_seq_93: seq<int> := [6, 5, 2, 19];
		var v_int_136: int := 28;
		var v_int_137: int := (if ((|v_seq_93| > 0)) then (v_seq_93[v_int_136]) else (2));
		var v_map_68: map<char, int> := (match 'q' {
			case _ => map['K' := 14, 'y' := -17, 'C' := 19, 'l' := 12, 'm' := 7]
		});
		var v_char_51: char := (match 'a' {
			case _ => 'm'
		});
		var v_map_67: map<char, int> := map['l' := 22, 'a' := 23, 'v' := 5, 'I' := 0, 's' := -1];
		var v_char_50: char := 'x';
		var v_int_164: int, v_int_165: int := (if (v_array_3[0]) then ((match 't' {
			case _ => (if ((v_char_49 in v_map_66)) then (v_map_66[v_char_49]) else (4))
		})) else (((if ((|v_seq_90| > 0)) then (v_seq_90[v_int_132]) else (28)) / v_int_9))), (if ((if ((|v_seq_94| > 0)) then (v_seq_94[v_int_137]) else ((if (true) then (true) else (true))))) then ((if ((v_char_51 in v_map_68)) then (v_map_68[v_char_51]) else ((if ((v_char_50 in v_map_67)) then (v_map_67[v_char_50]) else (19))))) else ((match 'i' {
			case _ => v_int_136
		})));
		for v_int_131 := v_int_164 to v_int_165 
			invariant (v_int_165 - v_int_131 >= 0)
		{
			var v_int_138: int := v_int_12;
			var v_array_29: array<char> := new char[3] ['n', 'R', 'm'];
			var v_seq_95: seq<int> := [9, 7, -13, -29];
			var v_seq_96: seq<int> := v_seq_95;
			var v_int_140: int := 7;
			var v_int_141: int := safe_index_seq(v_seq_96, v_int_140);
			var v_int_142: int := v_int_141;
			var v_seq_97: seq<int> := (if ((|v_seq_95| > 0)) then (v_seq_95[v_int_142 := 18]) else (v_seq_95));
			var v_int_143: int := (if (false) then (-19) else (22));
			var v_array_30: array<char> := new char[5];
			v_array_30[0] := 'E';
			v_array_30[1] := 'v';
			v_array_30[2] := 'v';
			v_array_30[3] := 'N';
			v_array_30[4] := 'w';
			var v_seq_98: seq<bool> := [];
			var v_int_144: int := 6;
			var v_int_139: int := (match 'A' {
				case _ => (if ((if ((|v_seq_98| > 0)) then (v_seq_98[v_int_144]) else (true))) then ((match 'p' {
					case _ => 23
				})) else ((-7 * 1)))
			});
			while (v_int_138 < v_int_139) 
				decreases v_int_139 - v_int_138;
				invariant (v_int_138 <= v_int_139);
			{
				v_int_138 := (v_int_138 + 1);
				var v_seq_99: seq<int> := [17, 17, 16];
				var v_seq_100: seq<int> := v_seq_99;
				var v_int_147: int := 10;
				var v_int_148: int := safe_index_seq(v_seq_100, v_int_147);
				var v_int_149: int := v_int_148;
				var v_seq_101: seq<int> := ((if (false) then ([-18, 23, 22]) else ([9])) + (if ((|v_seq_99| > 0)) then (v_seq_99[v_int_149 := 27]) else (v_seq_99)));
				var v_int_150: int := (if ((match 'j' {
					case _ => false
				})) then (v_int_134) else ((match 'a' {
					case _ => 2
				})));
				var v_int_145: int := (if ((|v_seq_101| > 0)) then (v_seq_101[v_int_150]) else ((if (({'o', 'I', 'z', 'x'} <= {'K', 'J', 'Q'})) then (v_int_16) else ((match 'S' {
					case _ => 24
				})))));
				var v_int_146: int := v_int_13;
				while (v_int_145 < v_int_146) 
					decreases v_int_146 - v_int_145;
					invariant (v_int_145 <= v_int_146);
				{
					v_int_145 := (v_int_145 + 1);
				}
				continue;
			}
			var v_map_69: map<char, int> := map['c' := 28, 'v' := 12, 'E' := 16]['D' := -13];
			var v_seq_102: seq<char> := [];
			var v_int_152: int := 6;
			var v_char_52: char := (if ((|v_seq_102| > 0)) then (v_seq_102[v_int_152]) else ('g'));
			var v_array_31: array<char> := new char[4] ['h', 'F', 'q', 'w'];
			var v_seq_103: seq<int> := [20];
			var v_seq_104: seq<int> := v_seq_103;
			var v_int_153: int := 17;
			var v_int_154: int := safe_index_seq(v_seq_104, v_int_153);
			var v_int_155: int := v_int_154;
			var v_seq_106: seq<int> := (if ((|v_seq_103| > 0)) then (v_seq_103[v_int_155 := 15]) else (v_seq_103));
			var v_seq_105: seq<int> := [21, 20, 24, 21];
			var v_int_156: int := 20;
			var v_seq_110: seq<int> := (if ((|v_seq_106| > 0)) then (v_seq_106[(match 'u' {
				case _ => 17
			})..(if ((|v_seq_105| > 0)) then (v_seq_105[v_int_156]) else (0))]) else (v_seq_106));
			var v_seq_107: seq<int> := [26, 17, 22, 27];
			var v_seq_109: seq<int> := (if ((|v_seq_107| > 0)) then (v_seq_107[2..1]) else (v_seq_107));
			var v_seq_108: seq<int> := [11, 24];
			var v_int_157: int := 12;
			var v_int_158: int := (if ((|v_seq_108| > 0)) then (v_seq_108[v_int_157]) else (25));
			var v_int_159: int := (if ((|v_seq_109| > 0)) then (v_seq_109[v_int_158]) else ((17 * 15)));
			var v_int_162: int, v_int_163: int := (v_int_135 + (if ((v_char_52 in v_map_69)) then (v_map_69[v_char_52]) else (v_array_31.Length))), (if ((|v_seq_110| > 0)) then (v_seq_110[v_int_159]) else ((match 'b' {
				case _ => v_int_13
			})));
			for v_int_151 := v_int_162 to v_int_163 
				invariant (v_int_163 - v_int_151 >= 0)
			{
				var v_map_70: map<char, bool> := map['j' := false, 'v' := true, 'A' := true, 'g' := true, 'V' := false];
				var v_char_53: char := 'G';
				var v_map_71: map<char, bool> := map['S' := true, 'e' := false, 'a' := true]['L' := true];
				var v_seq_111: seq<char> := ['R'];
				var v_int_160: int := 16;
				var v_char_54: char := (if ((|v_seq_111| > 0)) then (v_seq_111[v_int_160]) else ('E'));
				var v_seq_112: seq<bool> := [true, false];
				var v_seq_113: seq<bool> := (if ((|v_seq_112| > 0)) then (v_seq_112[7..22]) else (v_seq_112));
				var v_int_161: int := (24 * 0);
				var v_map_72: map<char, bool> := map['C' := false];
				var v_char_55: char := 'v';
				if (if ((if ((if (true) then (false) else (false))) then ((if ((v_char_53 in v_map_70)) then (v_map_70[v_char_53]) else (true))) else (!(true)))) then ((if ((v_char_54 in v_map_71)) then (v_map_71[v_char_54]) else ((match 'I' {
					case _ => false
				})))) else ((if ((|v_seq_113| > 0)) then (v_seq_113[v_int_161]) else ((if ((v_char_55 in v_map_72)) then (v_map_72[v_char_55]) else (true)))))) {
					return ;
				} else {
					return ;
				}
			}
		}
		var v_seq_114: seq<char> := ['P', 'z', 'I', 'a'];
		var v_seq_115: seq<char> := v_seq_114;
		var v_int_166: int := 8;
		var v_int_167: int := safe_index_seq(v_seq_115, v_int_166);
		var v_int_168: int := v_int_167;
		var v_seq_116: seq<char> := ['h', 'z', 'P'];
		var v_seq_117: seq<char> := v_seq_116;
		var v_int_169: int := 18;
		var v_int_170: int := safe_index_seq(v_seq_117, v_int_169);
		var v_int_171: int := v_int_170;
		var v_seq_120: seq<char> := (match 'a' {
			case _ => (if ((|v_seq_116| > 0)) then (v_seq_116[v_int_171 := 'S']) else (v_seq_116))
		});
		var v_seq_118: seq<int> := [];
		var v_seq_119: seq<int> := (if ((|v_seq_118| > 0)) then (v_seq_118[14..1]) else (v_seq_118));
		var v_int_172: int := (26 % 14);
		var v_map_73: map<char, int> := map['n' := 13, 'g' := 9, 'R' := 26];
		var v_char_56: char := 'r';
		var v_int_173: int := (if ((|v_seq_119| > 0)) then (v_seq_119[v_int_172]) else ((if ((v_char_56 in v_map_73)) then (v_map_73[v_char_56]) else (27))));
		var v_map_74: map<char, char> := map['R' := 'c', 'V' := 'l'];
		var v_char_57: char := 'h';
		var v_map_75: map<char, char> := map['J' := 'V', 'L' := 'd'];
		var v_char_58: char := 'D';
		var v_map_76: map<char, char> := map['j' := 's', 'i' := 'Z', 'M' := 'K', 'g' := 'c']['f' := 'm'][(if ((v_char_57 in v_map_74)) then (v_map_74[v_char_57]) else ('p')) := (if ((v_char_58 in v_map_75)) then (v_map_75[v_char_58]) else ('P'))];
		var v_seq_121: seq<char> := ['J', 'f', 'u'];
		var v_int_174: int := -29;
		var v_char_59: char := (match 'R' {
			case _ => (if ((|v_seq_121| > 0)) then (v_seq_121[v_int_174]) else ('B'))
		});
		v_char_58, v_array_23[1], v_array_22[2], v_char_59 := (if ((|v_seq_120| > 0)) then (v_seq_120[v_int_173]) else (v_array_26[1])), (if ((v_char_59 in v_map_76)) then (v_map_76[v_char_59]) else ((if ((match 'N' {
			case _ => true
		})) then (v_array_26[1]) else ((if (true) then ('U') else ('u')))))), v_array_24[0], v_array_26[1];
		return ;
	}
}
