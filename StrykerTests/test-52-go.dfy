// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1> = DT_1_1
datatype DT_2 = DT_2_1 | DT_2_4(DT_2_4_1: char, DT_2_4_2: char, DT_2_4_3: char)
datatype DT_3<T_2, T_3> = DT_3_1
method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method m_method_9(p_m_method_9_1: char, p_m_method_9_2: char, p_m_method_9_3: char) returns (ret_1: (bool, (real, real)))
	requires ((p_m_method_9_1 == 'B') && (p_m_method_9_3 == 'A') && (p_m_method_9_2 == 'u'));
	ensures (((p_m_method_9_1 == 'B') && (p_m_method_9_3 == 'A') && (p_m_method_9_2 == 'u')) ==> (((ret_1).0 == false) && (-14.56 < ((ret_1).1).0 < -14.36) && (9.56 < ((ret_1).1).1 < 9.76)));
{
	if true {
		var v_real_real_6: (real, real) := (-14.46, 9.66);
		var v_bool_real_real_1: (bool, (real, real)) := (false, v_real_real_6);
		var v_real_real_8: (real, real) := (-14.46, 9.66);
		var v_bool_real_real_5: (bool, (real, real)) := (false, v_real_real_8);
		var v_real_real_9: (real, real) := (-14.46, 9.66);
		var v_real_real_10: (real, real) := (-14.46, 9.66);
		print "v_bool_real_real_1.0", " ", v_bool_real_real_1.0, " ", "v_real_real_6.1", " ", (v_real_real_6.1 == 9.66), " ", "v_bool_real_real_1", " ", (v_bool_real_real_1 == v_bool_real_real_5), " ", "v_real_real_6", " ", (v_real_real_6 == v_real_real_9), " ", "v_real_real_6.0", " ", (v_real_real_6.0 == -14.46), " ", "v_bool_real_real_1.1", " ", (v_bool_real_real_1.1 == v_real_real_10), " ", "p_m_method_9_3", " ", (p_m_method_9_3 == 'A'), " ", "p_m_method_9_2", " ", (p_m_method_9_2 == 'u'), " ", "p_m_method_9_1", " ", (p_m_method_9_1 == 'B'), "\n";
		return v_bool_real_real_1;
	} else {
		var v_real_real_7: (real, real) := (-15.27, -0.22);
		var v_bool_real_real_2: (bool, (real, real)) := (false, v_real_real_7);
		return v_bool_real_real_2;
	}
}

method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_8(p_m_method_8_1: int) returns (ret_1: seq<seq<bool>>)
	requires ((p_m_method_8_1 == 13));
	ensures (((p_m_method_8_1 == 13)) ==> (|ret_1| == 2 && |ret_1[0]| == 2 && (ret_1[0][0] == true) && (ret_1[0][1] == true) && |ret_1[1]| == 1 && (ret_1[1][0] == true)));
{
	var v_array_37: array<bool> := new bool[5] [false, false, false, true, true];
	var v_array_multiset_1: (array<bool>, multiset<real>) := (v_array_37, multiset({}));
	var v_array_38: array<bool> := new bool[3] [true, true, false];
	var v_array_multiset_2: (array<bool>, multiset<real>) := (v_array_38, multiset{6.07, -24.55, -21.77});
	var v_array_39: array<bool> := new bool[3] [false, false, false];
	var v_array_multiset_3: (array<bool>, multiset<real>) := (v_array_39, multiset{22.07, -1.83, 8.07, 1.64});
	var v_map_7: map<char, (array<bool>, multiset<real>)> := map['r' := v_array_multiset_1, 'G' := v_array_multiset_2, 'K' := v_array_multiset_3];
	var v_char_5: char := 'F';
	var v_array_40: array<bool> := new bool[4] [true, true, false, false];
	var v_array_multiset_4: (array<bool>, multiset<real>) := (v_array_40, multiset({-26.12, -16.76}));
	var v_char_6: char := 'B';
	var v_char_7: char := 'u';
	var v_char_8: char := 'A';
	var v_bool_real_real_3: (bool, (real, real)) := m_method_9(v_char_6, v_char_7, v_char_8);
	var v_char_9: char := 'm';
	var v_char_10: char := 'L';
	var v_char_11: char := 'A';
	var v_bool_real_real_int_3: (bool, (real, real, int)) := m_method_10(v_char_9, v_char_10, v_char_11);
	var v_real_bool_13: (real, bool) := (21.39, true);
	var v_real_bool_14: (real, bool) := (-8.25, false);
	var v_real_bool_15: (real, bool) := (10.14, true);
	var v_real_bool_16: (real, bool) := (13.68, true);
	var v_real_bool_17: (real, bool) := (19.79, true);
	var v_DT_2_4_1: DT_2 := DT_2_4('H', 'o', 'C');
	var v_DT_2_4_2: DT_2 := DT_2_4('S', 'M', 'K');
	var v_DT_2_4_3: DT_2 := DT_2_4('j', 'S', 'E');
	var v_DT_2_4_4: DT_2 := DT_2_4('Y', 'k', 'P');
	var v_seq_14: seq<DT_2> := [v_DT_2_4_1, v_DT_2_4_2, v_DT_2_4_3, v_DT_2_4_4];
	var v_int_35: int := 11;
	var v_seq_181: seq<DT_2> := v_seq_14;
	var v_int_223: int := v_int_35;
	var v_int_224: int := safe_index_seq(v_seq_181, v_int_223);
	v_int_35 := v_int_224;
	var v_DT_2_4_5: DT_2 := DT_2_4('O', 'C', 'k');
	var v_array_multiset_5: (array<bool>, multiset<real>), v_bool_real_real_4: (bool, (real, real)), v_bool_real_real_int_4: (bool, (real, real, int)), v_map_8: map<(real, bool), int>, v_DT_2_4_6: DT_2 := (if ((v_char_5 in v_map_7)) then (v_map_7[v_char_5]) else (v_array_multiset_4)), v_bool_real_real_3, v_bool_real_real_int_3, map[v_real_bool_13 := 6, v_real_bool_14 := 3, v_real_bool_15 := 25, v_real_bool_16 := 15][v_real_bool_17 := 20], (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_35]) else (v_DT_2_4_5));
	var v_int_bool_int_1: (int, bool, int) := (25, false, 18);
	var v_int_bool_int_2: (int, bool, int) := (28, true, 2);
	var v_int_bool_int_3: (int, bool, int) := (27, false, 1);
	var v_int_bool_int_4: (int, bool, int) := (29, false, -5);
	var v_seq_16: seq<(int, bool, int)> := [v_int_bool_int_1, v_int_bool_int_2, v_int_bool_int_3, v_int_bool_int_4];
	var v_int_37: int := 22;
	var v_seq_182: seq<(int, bool, int)> := v_seq_16;
	var v_int_225: int := v_int_37;
	var v_int_226: int := safe_index_seq(v_seq_182, v_int_225);
	v_int_37 := v_int_226;
	var v_int_bool_int_5: (int, bool, int) := (19, true, 3);
	var v_int_bool_int_6: (int, bool, int) := (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_37]) else (v_int_bool_int_5));
	var v_char_13: char := v_DT_2_4_2.DT_2_4_3;
	var v_char_14: char := v_DT_2_4_2.DT_2_4_3;
	var v_char_15: char := v_DT_2_4_2.DT_2_4_3;
	var v_char_16: char, v_char_17: char, v_char_18: char, v_char_19: char, v_char_20: char := m_method_11(v_int_bool_int_6, v_char_13, v_char_14, v_char_15);
	v_char_15, v_char_13, v_char_10, v_char_5, v_char_19 := v_char_16, v_char_17, v_char_18, v_char_19, v_char_20;
	var v_real_real_int_6: (real, real, int) := (21.52, -1.79, 13);
	var v_bool_real_real_int_6: (bool, (real, real, int)) := (false, v_real_real_int_6);
	var v_real_real_int_7: (real, real, int) := (21.52, -1.79, 13);
	var v_bool_real_real_int_7: (bool, (real, real, int)) := (false, v_real_real_int_7);
	var v_DT_2_4_7: DT_2 := DT_2_4('H', 'o', 'C');
	var v_DT_2_4_8: DT_2 := DT_2_4('O', 'C', 'k');
	var v_DT_2_4_9: DT_2 := DT_2_4('Y', 'k', 'P');
	var v_DT_2_4_10: DT_2 := DT_2_4('j', 'S', 'E');
	var v_DT_2_4_11: DT_2 := DT_2_4('S', 'M', 'K');
	var v_DT_2_4_12: DT_2 := DT_2_4('H', 'o', 'C');
	var v_array_multiset_6: (array<bool>, multiset<real>) := (v_array_40, multiset{-26.12, -16.76});
	var v_array_multiset_7: (array<bool>, multiset<real>) := (v_array_40, multiset{-26.12, -16.76});
	var v_array_multiset_8: (array<bool>, multiset<real>) := (v_array_39, multiset{-1.83, 8.07, 22.07, 1.64});
	var v_array_multiset_9: (array<bool>, multiset<real>) := (v_array_38, multiset{-21.77, 6.07, -24.55});
	var v_array_multiset_10: (array<bool>, multiset<real>) := (v_array_37, multiset{});
	var v_real_bool_23: (real, bool) := (21.39, true);
	var v_array_multiset_11: (array<bool>, multiset<real>) := (v_array_37, multiset{});
	var v_array_multiset_12: (array<bool>, multiset<real>) := (v_array_38, multiset{-21.77, 6.07, -24.55});
	var v_array_multiset_13: (array<bool>, multiset<real>) := (v_array_39, multiset{-1.83, 8.07, 22.07, 1.64});
	var v_real_bool_24: (real, bool) := (21.39, true);
	var v_real_bool_25: (real, bool) := (13.68, true);
	var v_real_bool_26: (real, bool) := (-8.25, false);
	var v_real_bool_27: (real, bool) := (10.14, true);
	var v_real_bool_28: (real, bool) := (19.79, true);
	var v_real_bool_29: (real, bool) := (13.68, true);
	var v_real_bool_30: (real, bool) := (19.79, true);
	var v_real_bool_31: (real, bool) := (-8.25, false);
	var v_real_bool_32: (real, bool) := (10.14, true);
	var v_real_real_11: (real, real) := (-14.46, 9.66);
	var v_bool_real_real_6: (bool, (real, real)) := (false, v_real_real_11);
	var v_real_real_12: (real, real) := (-14.46, 9.66);
	var v_bool_real_real_7: (bool, (real, real)) := (false, v_real_real_12);
	var v_DT_2_4_13: DT_2 := DT_2_4('H', 'o', 'C');
	var v_DT_2_4_14: DT_2 := DT_2_4('S', 'M', 'K');
	var v_DT_2_4_15: DT_2 := DT_2_4('j', 'S', 'E');
	var v_DT_2_4_16: DT_2 := DT_2_4('Y', 'k', 'P');
	print "v_array_40[2]", " ", v_array_40[2], " ", "v_array_37[1]", " ", v_array_37[1], " ", "v_DT_2_4_2.DT_2_4_2", " ", (v_DT_2_4_2.DT_2_4_2 == 'M'), " ", "v_DT_2_4_2.DT_2_4_1", " ", (v_DT_2_4_2.DT_2_4_1 == 'S'), " ", "v_DT_2_4_2.DT_2_4_3", " ", (v_DT_2_4_2.DT_2_4_3 == 'K'), " ", "v_real_bool_16.1", " ", v_real_bool_16.1, " ", "v_real_bool_16.0", " ", (v_real_bool_16.0 == 13.68), " ", "p_m_method_8_1", " ", p_m_method_8_1, " ", "v_array_40[3]", " ", v_array_40[3], " ", "v_array_37[2]", " ", v_array_37[2], " ", "v_bool_real_real_int_3", " ", (v_bool_real_real_int_3 == v_bool_real_real_int_6), " ", "v_bool_real_real_int_4", " ", (v_bool_real_real_int_4 == v_bool_real_real_int_7), " ", "v_int_bool_int_3.0", " ", v_int_bool_int_3.0, " ", "v_array_multiset_3.1", " ", (v_array_multiset_3.1 == multiset{-1.83, 8.07, 22.07, 1.64}), " ", "v_int_bool_int_3.2", " ", v_int_bool_int_3.2, " ", "v_array_multiset_3.0", " ", (v_array_multiset_3.0 == v_array_39), " ", "v_int_bool_int_3.1", " ", v_int_bool_int_3.1, " ", "v_DT_2_4_1", " ", (v_DT_2_4_1 == v_DT_2_4_7), " ", "v_int_35", " ", v_int_35, " ", "v_DT_2_4_5", " ", (v_DT_2_4_5 == v_DT_2_4_8), " ", "v_DT_2_4_4", " ", (v_DT_2_4_4 == v_DT_2_4_9), " ", "v_DT_2_4_3", " ", (v_DT_2_4_3 == v_DT_2_4_10), " ", "v_int_37", " ", v_int_37, " ", "v_DT_2_4_2", " ", (v_DT_2_4_2 == v_DT_2_4_11), " ", "v_DT_2_4_6", " ", (v_DT_2_4_6 == v_DT_2_4_12), " ", "v_array_multiset_5", " ", (v_array_multiset_5 == v_array_multiset_6), " ", "v_array_multiset_4", " ", (v_array_multiset_4 == v_array_multiset_7), " ", "v_array_39[1]", " ", v_array_39[1], " ", "v_array_multiset_3", " ", (v_array_multiset_3 == v_array_multiset_8), " ", "v_array_multiset_2", " ", (v_array_multiset_2 == v_array_multiset_9), " ", "v_array_multiset_1", " ", (v_array_multiset_1 == v_array_multiset_10), " ", "v_array_40[0]", " ", v_array_40[0], " ", "v_real_bool_17.1", " ", v_real_bool_17.1, " ", "v_real_bool_17.0", " ", (v_real_bool_17.0 == 19.79), " ", "v_real_bool_13.1", " ", v_real_bool_13.1, " ", "v_real_bool_13.0", " ", (v_real_bool_13.0 == 21.39), " ", "v_DT_2_4_1.DT_2_4_3", " ", (v_DT_2_4_1.DT_2_4_3 == 'C'), " ", "v_real_bool_13", " ", (v_real_bool_13 == v_real_bool_23), " ", "v_DT_2_4_1.DT_2_4_2", " ", (v_DT_2_4_1.DT_2_4_2 == 'o'), " ", "v_DT_2_4_1.DT_2_4_1", " ", (v_DT_2_4_1.DT_2_4_1 == 'H'), " ", "v_array_39[2]", " ", v_array_39[2], " ", "v_map_7", " ", (v_map_7 == map['r' := v_array_multiset_11, 'G' := v_array_multiset_12, 'K' := v_array_multiset_13]), " ", "v_char_5", " ", (v_char_5 == 'w'), " ", "v_array_37[0]", " ", v_array_37[0], " ", "v_map_8", " ", (v_map_8 == map[v_real_bool_24 := 6, v_real_bool_25 := 15, v_real_bool_26 := 3, v_real_bool_27 := 25, v_real_bool_28 := 20]), " ", "v_int_bool_int_6", " ", v_int_bool_int_6, " ", "v_char_7", " ", (v_char_7 == 'u'), " ", "v_int_bool_int_5", " ", v_int_bool_int_5, " ", "v_array_40[1]", " ", v_array_40[1], " ", "v_char_6", " ", (v_char_6 == 'B'), " ", "v_int_bool_int_4", " ", v_int_bool_int_4, " ", "v_char_9", " ", (v_char_9 == 'm'), " ", "v_int_bool_int_3", " ", v_int_bool_int_3, " ", "v_char_8", " ", (v_char_8 == 'A'), " ", "v_DT_2_4_3.DT_2_4_1", " ", (v_DT_2_4_3.DT_2_4_1 == 'j'), " ", "v_int_bool_int_2", " ", v_int_bool_int_2, " ", "v_int_bool_int_1", " ", v_int_bool_int_1, " ", "v_array_multiset_2.0", " ", (v_array_multiset_2.0 == v_array_38), " ", "v_real_bool_16", " ", (v_real_bool_16 == v_real_bool_29), " ", "v_int_bool_int_2.1", " ", v_int_bool_int_2.1, " ", "v_real_bool_17", " ", (v_real_bool_17 == v_real_bool_30), " ", "v_int_bool_int_2.0", " ", v_int_bool_int_2.0, " ", "v_real_bool_14", " ", (v_real_bool_14 == v_real_bool_31), " ", "v_DT_2_4_3.DT_2_4_2", " ", (v_DT_2_4_3.DT_2_4_2 == 'S'), " ", "v_array_multiset_2.1", " ", (v_array_multiset_2.1 == multiset{-21.77, 6.07, -24.55}), " ", "v_real_bool_15", " ", (v_real_bool_15 == v_real_bool_32), " ", "v_DT_2_4_3.DT_2_4_3", " ", (v_DT_2_4_3.DT_2_4_3 == 'E'), " ", "v_int_bool_int_2.2", " ", v_int_bool_int_2.2, " ", "v_bool_real_real_3", " ", (v_bool_real_real_3 == v_bool_real_real_6), " ", "v_bool_real_real_4", " ", (v_bool_real_real_4 == v_bool_real_real_7), " ", "v_array_38[2]", " ", v_array_38[2], " ", "v_real_bool_14.1", " ", v_real_bool_14.1, " ", "v_real_bool_14.0", " ", (v_real_bool_14.0 == -8.25), " ", "v_array_39", " ", (v_array_39 == v_array_39), " ", "v_array_38", " ", (v_array_38 == v_array_38), " ", "v_array_37", " ", (v_array_37 == v_array_37), " ", "v_array_39[0]", " ", v_array_39[0], " ", "v_int_bool_int_1.0", " ", v_int_bool_int_1.0, " ", "v_int_bool_int_5.2", " ", v_int_bool_int_5.2, " ", "v_int_bool_int_5.1", " ", v_int_bool_int_5.1, " ", "v_array_multiset_1.1", " ", (v_array_multiset_1.1 == multiset{}), " ", "v_int_bool_int_1.2", " ", v_int_bool_int_1.2, " ", "v_array_multiset_1.0", " ", (v_array_multiset_1.0 == v_array_37), " ", "v_int_bool_int_1.1", " ", v_int_bool_int_1.1, " ", "v_int_bool_int_5.0", " ", v_int_bool_int_5.0, " ", "v_DT_2_4_5.DT_2_4_1", " ", (v_DT_2_4_5.DT_2_4_1 == 'O'), " ", "v_DT_2_4_5.DT_2_4_3", " ", (v_DT_2_4_5.DT_2_4_3 == 'k'), " ", "v_DT_2_4_5.DT_2_4_2", " ", (v_DT_2_4_5.DT_2_4_2 == 'C'), " ", "v_char_18", " ", (v_char_18 == 'K'), " ", "v_char_17", " ", (v_char_17 == 'I'), " ", "v_array_37[3]", " ", v_array_37[3], " ", "v_char_16", " ", (v_char_16 == 'I'), " ", "v_char_15", " ", (v_char_15 == 'I'), " ", "v_array_38[0]", " ", v_array_38[0], " ", "v_char_14", " ", (v_char_14 == 'K'), " ", "v_char_13", " ", (v_char_13 == 'I'), " ", "v_char_11", " ", (v_char_11 == 'A'), " ", "v_real_bool_15.1", " ", v_real_bool_15.1, " ", "v_real_bool_15.0", " ", (v_real_bool_15.0 == 10.14), " ", "v_char_19", " ", (v_char_19 == 'O'), " ", "v_DT_2_4_4.DT_2_4_3", " ", (v_DT_2_4_4.DT_2_4_3 == 'P'), " ", "v_seq_14", " ", (v_seq_14 == [v_DT_2_4_13, v_DT_2_4_14, v_DT_2_4_15, v_DT_2_4_16]), " ", "v_seq_16", " ", v_seq_16, " ", "v_DT_2_4_4.DT_2_4_1", " ", (v_DT_2_4_4.DT_2_4_1 == 'Y'), " ", "v_DT_2_4_4.DT_2_4_2", " ", (v_DT_2_4_4.DT_2_4_2 == 'k'), " ", "v_char_20", " ", (v_char_20 == 'O'), " ", "v_array_37[4]", " ", v_array_37[4], " ", "v_array_38[1]", " ", v_array_38[1], " ", "v_array_40", " ", (v_array_40 == v_array_40), " ", "v_int_bool_int_4.2", " ", v_int_bool_int_4.2, " ", "v_array_multiset_4.0", " ", (v_array_multiset_4.0 == v_array_40), " ", "v_int_bool_int_4.1", " ", v_int_bool_int_4.1, " ", "v_int_bool_int_4.0", " ", v_int_bool_int_4.0, " ", "v_array_multiset_4.1", " ", (v_array_multiset_4.1 == multiset{-26.12, -16.76}), " ", "v_char_10", " ", (v_char_10 == 'K'), "\n";
	return (match 'o' {
		case 'K' => [[]]
		case _ => [[true, true], [true]]
	});
}

method m_method_7(p_m_method_7_1: bool, p_m_method_7_2: char) returns (ret_1: bool)
	requires ((p_m_method_7_2 == 'G') && (p_m_method_7_1 == true)) || ((p_m_method_7_2 == 'a') && (p_m_method_7_1 == true)) || ((p_m_method_7_2 == 'r') && (p_m_method_7_1 == true)) || ((p_m_method_7_2 == 'v') && (p_m_method_7_1 == false));
	ensures (((p_m_method_7_2 == 'G') && (p_m_method_7_1 == true)) ==> ((ret_1 == false))) && (((p_m_method_7_2 == 'v') && (p_m_method_7_1 == false)) ==> ((ret_1 == false))) && (((p_m_method_7_2 == 'r') && (p_m_method_7_1 == true)) ==> ((ret_1 == false))) && (((p_m_method_7_2 == 'a') && (p_m_method_7_1 == true)) ==> ((ret_1 == false)));
{
	print "p_m_method_7_2", " ", (p_m_method_7_2 == 'G'), " ", "p_m_method_7_1", " ", p_m_method_7_1, "\n";
	return false;
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: (bool, bool), p_m_method_6_2: array<int>) returns (ret_1: ((int, real), (real, bool), (bool, int, bool)))
	requires (p_m_method_6_2.Length == 5 && (p_m_method_6_2[0] == 1) && (p_m_method_6_2[1] == 4) && (p_m_method_6_2[2] == 9) && (p_m_method_6_2[3] == 9) && (p_m_method_6_2[4] == 20) && ((p_m_method_6_1).0 == false) && ((p_m_method_6_1).1 == false));
	ensures ((p_m_method_6_2.Length == 5 && (p_m_method_6_2[0] == 1) && (p_m_method_6_2[1] == 4) && (p_m_method_6_2[2] == 9) && (p_m_method_6_2[3] == 9) && (p_m_method_6_2[4] == 20) && ((p_m_method_6_1).0 == false) && ((p_m_method_6_1).1 == false)) ==> ((((ret_1).0).0 == 15) && (-3.47 < ((ret_1).0).1 < -3.27) && (24.34 < ((ret_1).1).0 < 24.54) && (((ret_1).1).1 == true) && (((ret_1).2).0 == true) && (((ret_1).2).1 == 11) && (((ret_1).2).2 == true)));
{
	if false {
		if false {
			var v_int_real_9: (int, real) := (13, -25.67);
			var v_real_bool_9: (real, bool) := (9.66, false);
			var v_bool_int_bool_9: (bool, int, bool) := (false, 8, true);
			var v_int_real_real_bool_bool_int_bool_9: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_9, v_real_bool_9, v_bool_int_bool_9);
			return v_int_real_real_bool_bool_int_bool_9;
		}
	} else {
		var v_int_27: int, v_int_28: int := 7, 13;
		for v_int_26 := v_int_27 to v_int_28 
			invariant (v_int_28 - v_int_26 >= 0)
		{
			var v_int_real_10: (int, real) := (15, -3.37);
			var v_real_bool_10: (real, bool) := (24.44, true);
			var v_bool_int_bool_10: (bool, int, bool) := (true, 11, true);
			var v_int_real_real_bool_bool_int_bool_10: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_10, v_real_bool_10, v_bool_int_bool_10);
			var v_int_real_13: (int, real) := (15, -3.37);
			var v_real_bool_20: (real, bool) := (24.44, true);
			var v_int_real_14: (int, real) := (15, -3.37);
			var v_real_bool_21: (real, bool) := (24.44, true);
			var v_bool_int_bool_13: (bool, int, bool) := (true, 11, true);
			var v_int_real_real_bool_bool_int_bool_15: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_14, v_real_bool_21, v_bool_int_bool_13);
			var v_int_real_15: (int, real) := (15, -3.37);
			var v_real_bool_22: (real, bool) := (24.44, true);
			print "v_int_real_real_bool_bool_int_bool_10.0", " ", (v_int_real_real_bool_bool_int_bool_10.0 == v_int_real_13), " ", "v_int_real_10.1", " ", (v_int_real_10.1 == -3.37), " ", "v_int_real_10.0", " ", v_int_real_10.0, " ", "v_int_real_real_bool_bool_int_bool_10.2", " ", v_int_real_real_bool_bool_int_bool_10.2, " ", "v_int_real_real_bool_bool_int_bool_10.1", " ", (v_int_real_real_bool_bool_int_bool_10.1 == v_real_bool_20), " ", "v_int_real_real_bool_bool_int_bool_10", " ", (v_int_real_real_bool_bool_int_bool_10 == v_int_real_real_bool_bool_int_bool_15), " ", "v_int_real_10", " ", (v_int_real_10 == v_int_real_15), " ", "v_real_bool_10.1", " ", v_real_bool_10.1, " ", "v_bool_int_bool_10", " ", v_bool_int_bool_10, " ", "v_bool_int_bool_10.1", " ", v_bool_int_bool_10.1, " ", "v_real_bool_10.0", " ", (v_real_bool_10.0 == 24.44), " ", "v_bool_int_bool_10.0", " ", v_bool_int_bool_10.0, " ", "v_real_bool_10", " ", (v_real_bool_10 == v_real_bool_22), " ", "v_int_26", " ", v_int_26, " ", "v_bool_int_bool_10.2", " ", v_bool_int_bool_10.2, " ", "p_m_method_6_2[0]", " ", p_m_method_6_2[0], " ", "p_m_method_6_2[1]", " ", p_m_method_6_2[1], " ", "p_m_method_6_2[2]", " ", p_m_method_6_2[2], " ", "p_m_method_6_2", " ", "p_m_method_6_1.0", " ", p_m_method_6_1.0, " ", "p_m_method_6_1.1", " ", p_m_method_6_1.1, " ", "p_m_method_6_1", " ", p_m_method_6_1, "\n";
			return v_int_real_real_bool_bool_int_bool_10;
		}
		var v_int_real_11: (int, real) := (18, 0.98);
		var v_real_bool_11: (real, bool) := (-7.70, true);
		var v_bool_int_bool_11: (bool, int, bool) := (true, 10, false);
		var v_int_real_real_bool_bool_int_bool_11: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_11, v_real_bool_11, v_bool_int_bool_11);
		return v_int_real_real_bool_bool_int_bool_11;
	}
	var v_int_30: int, v_int_31: int := 4, 8;
	for v_int_29 := v_int_30 to v_int_31 
		invariant (v_int_31 - v_int_29 >= 0)
	{
		assert true;
		expect true;
		break;
	}
	var v_int_real_12: (int, real) := (28, 16.73);
	var v_real_bool_12: (real, bool) := (-27.17, true);
	var v_bool_int_bool_12: (bool, int, bool) := (true, 0, false);
	var v_int_real_real_bool_bool_int_bool_12: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_12, v_real_bool_12, v_bool_int_bool_12);
	return v_int_real_real_bool_bool_int_bool_12;
}

method m_method_5(p_m_method_5_1: int, p_m_method_5_2: (bool, bool, real), p_m_method_5_3: array<bool>) returns (ret_1: seq<int>)
	requires ((p_m_method_5_1 == 15) && p_m_method_5_3.Length == 5 && (p_m_method_5_3[0] == false) && (p_m_method_5_3[1] == false) && (p_m_method_5_3[2] == true) && (p_m_method_5_3[3] == false) && (p_m_method_5_3[4] == true) && ((p_m_method_5_2).0 == true) && ((p_m_method_5_2).1 == false) && (5.34 < (p_m_method_5_2).2 < 5.54));
	ensures (((p_m_method_5_1 == 15) && p_m_method_5_3.Length == 5 && (p_m_method_5_3[0] == false) && (p_m_method_5_3[1] == false) && (p_m_method_5_3[2] == true) && (p_m_method_5_3[3] == false) && (p_m_method_5_3[4] == true) && ((p_m_method_5_2).0 == true) && ((p_m_method_5_2).1 == false) && (5.34 < (p_m_method_5_2).2 < 5.54)) ==> (|ret_1| == 4 && (ret_1[0] == 5) && (ret_1[1] == 0) && (ret_1[2] == 1) && (ret_1[3] == 14)));
{
	var v_bool_bool_real_3: (bool, bool, real) := (true, false, 5.44);
	print "p_m_method_5_3[1]", " ", p_m_method_5_3[1], " ", "p_m_method_5_3[2]", " ", p_m_method_5_3[2], " ", "p_m_method_5_3[0]", " ", p_m_method_5_3[0], " ", "p_m_method_5_3", " ", "p_m_method_5_2.1", " ", p_m_method_5_2.1, " ", "p_m_method_5_2.2", " ", (p_m_method_5_2.2 == 5.44), " ", "p_m_method_5_2", " ", (p_m_method_5_2 == v_bool_bool_real_3), " ", "p_m_method_5_1", " ", p_m_method_5_1, " ", "p_m_method_5_2.0", " ", p_m_method_5_2.0, "\n";
	return [5, 0, 1, 14];
}

method m_method_4(p_m_method_4_1: int) returns (ret_1: seq<int>)
	requires ((p_m_method_4_1 == 11));
	ensures (((p_m_method_4_1 == 11)) ==> (|ret_1| == 4 && (ret_1[0] == 5) && (ret_1[1] == 0) && (ret_1[2] == 1) && (ret_1[3] == 14)));
{
	var v_array_2: array<int> := new int[4] [8, 24, 18, -19];
	var v_int_17: int, v_int_18: int := v_array_2.Length, v_array_2[0];
	for v_int_11 := v_int_17 to v_int_18 
		invariant (v_int_18 - v_int_11 >= 0) && ((((v_int_11 == 4)) ==> ((((v_array_2[1] == 24))))) && (((v_int_11 == 6)) ==> ((((v_array_2[1] == 15))))) && (((v_int_11 == 5)) ==> ((((v_array_2[1] == 15))))) && (((v_int_11 == 7)) ==> ((((v_array_2[1] == 15))))))
	{
		var v_map_2: map<int, int> := map[27 := 3, 4 := 28];
		var v_int_12: int := 8;
		var v_int_13: int, v_int_14: int, v_int_15: int := (11 / -17), (4.01).Floor, (if ((v_int_12 in v_map_2)) then (v_map_2[v_int_12]) else (19));
		var v_map_3: map<int, int> := map[4 := -19, 0 := 29, 15 := 14];
		var v_int_16: int := 25;
		var v_array_3: array<int> := new int[3] [12, 7, 26];
		v_array_2[1], v_int_14, v_int_16, v_array_3[2], v_int_13 := (if ((v_int_16 in v_map_3)) then (v_map_3[v_int_16]) else (15)), (24 + 8), v_array_2[1], v_array_3.Length, (-18.67).Floor;
		print "v_map_3", " ", (v_map_3 == map[0 := 29, 4 := -19, 15 := 14]), " ", "v_map_2", " ", (v_map_2 == map[4 := 28, 27 := 3]), " ", "v_int_13", " ", v_int_13, " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_int_12", " ", v_int_12, " ", "v_int_11", " ", v_int_11, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_array_3[0]", " ", v_array_3[0], " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_array_3[1]", " ", v_array_3[1], " ", "v_array_3[2]", " ", v_array_3[2], " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_array_2[1]", " ", v_array_2[1], " ", "p_m_method_4_1", " ", p_m_method_4_1, " ", "v_array_2[2]", " ", v_array_2[2], " ", "v_array_2[3]", " ", v_array_2[3], "\n";
		continue;
	}
	var v_int_19: int := 21;
	var v_int_20: int := 21;
	var v_int_21: int := safe_division(v_int_19, v_int_20);
	v_array_2[2], v_int_19 := v_int_17, v_int_21;
	var v_int_22: int := 15;
	var v_bool_bool_real_1: (bool, bool, real) := (true, false, 5.44);
	var v_bool_bool_real_2: (bool, bool, real) := v_bool_bool_real_1;
	var v_array_4: array<bool> := new bool[5] [false, false, true, false, true];
	var v_array_5: array<bool> := v_array_4;
	var v_seq_8: seq<int> := m_method_5(v_int_22, v_bool_bool_real_2, v_array_5);
	var v_bool_bool_real_4: (bool, bool, real) := (true, false, 5.44);
	var v_bool_bool_real_5: (bool, bool, real) := (true, false, 5.44);
	print "v_array_4[4]", " ", v_array_4[4], " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "v_int_22", " ", v_int_22, " ", "v_array_5", " ", (v_array_5 == v_array_4), " ", "v_int_21", " ", v_int_21, " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_2[1]", " ", v_array_2[1], " ", "p_m_method_4_1", " ", p_m_method_4_1, " ", "v_int_20", " ", v_int_20, " ", "v_array_4[1]", " ", v_array_4[1], " ", "v_array_4[3]", " ", v_array_4[3], " ", "v_array_2[3]", " ", v_array_2[3], " ", "v_seq_8", " ", v_seq_8, " ", "v_bool_bool_real_1.0", " ", v_bool_bool_real_1.0, " ", "v_int_17", " ", v_int_17, " ", "v_bool_bool_real_1.2", " ", (v_bool_bool_real_1.2 == 5.44), " ", "v_bool_bool_real_1.1", " ", v_bool_bool_real_1.1, " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_bool_bool_real_1", " ", (v_bool_bool_real_1 == v_bool_bool_real_4), " ", "v_array_4[0]", " ", v_array_4[0], " ", "v_array_2[2]", " ", v_array_2[2], " ", "v_bool_bool_real_2", " ", (v_bool_bool_real_2 == v_bool_bool_real_5), " ", "v_array_4[2]", " ", v_array_4[2], "\n";
	return v_seq_8;
}

method m_method_3(p_m_method_3_1: (int, bool, real), p_m_method_3_2: (int, real, bool)) returns (ret_1: char)
	requires (((p_m_method_3_1).0 == 11) && ((p_m_method_3_1).1 == true) && (18.62 < (p_m_method_3_1).2 < 18.82) && ((p_m_method_3_2).0 == 1) && (-10.66 < (p_m_method_3_2).1 < -10.46) && ((p_m_method_3_2).2 == false)) || (((p_m_method_3_1).0 == 5) && ((p_m_method_3_1).1 == false) && (4.30 < (p_m_method_3_1).2 < 4.50) && ((p_m_method_3_2).0 == 15) && (3.02 < (p_m_method_3_2).1 < 3.22) && ((p_m_method_3_2).2 == true));
	ensures ((((p_m_method_3_1).0 == 11) && ((p_m_method_3_1).1 == true) && (18.62 < (p_m_method_3_1).2 < 18.82) && ((p_m_method_3_2).0 == 1) && (-10.66 < (p_m_method_3_2).1 < -10.46) && ((p_m_method_3_2).2 == false)) ==> ((ret_1 == 'I'))) && ((((p_m_method_3_1).0 == 5) && ((p_m_method_3_1).1 == false) && (4.30 < (p_m_method_3_1).2 < 4.50) && ((p_m_method_3_2).0 == 15) && (3.02 < (p_m_method_3_2).1 < 3.22) && ((p_m_method_3_2).2 == true)) ==> ((ret_1 == 'I')));
{
	var v_int_real_bool_5: (int, real, bool) := (1, -10.56, false);
	var v_int_bool_real_5: (int, bool, real) := (11, true, 18.72);
	print "p_m_method_3_1.2", " ", (p_m_method_3_1.2 == 18.72), " ", "p_m_method_3_2.1", " ", (p_m_method_3_2.1 == -10.56), " ", "p_m_method_3_2.2", " ", p_m_method_3_2.2, " ", "p_m_method_3_1.0", " ", p_m_method_3_1.0, " ", "p_m_method_3_2", " ", (p_m_method_3_2 == v_int_real_bool_5), " ", "p_m_method_3_1.1", " ", p_m_method_3_1.1, " ", "p_m_method_3_1", " ", (p_m_method_3_1 == v_int_bool_real_5), " ", "p_m_method_3_2.0", " ", p_m_method_3_2.0, "\n";
	return 'I';
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

method m_method_2(p_m_method_2_1: seq<int>) returns (ret_1: DT_1<bool>)
	requires (|p_m_method_2_1| == 2 && (p_m_method_2_1[0] == 2) && (p_m_method_2_1[1] == 24));
	ensures ((|p_m_method_2_1| == 2 && (p_m_method_2_1[0] == 2) && (p_m_method_2_1[1] == 24)) ==> ((ret_1.DT_1_1? && ((ret_1 == DT_1_1)))));
{
	var v_int_bool_real_1: (int, bool, real) := (11, true, 18.72);
	var v_int_bool_real_2: (int, bool, real) := v_int_bool_real_1;
	var v_int_real_bool_1: (int, real, bool) := (1, -10.56, false);
	var v_int_real_bool_2: (int, real, bool) := v_int_real_bool_1;
	var v_char_2: char := m_method_3(v_int_bool_real_2, v_int_real_bool_2);
	var v_int_9: int, v_bool_1: bool, v_char_3: char := (21 - 22), (if (true) then (false) else (false)), v_char_2;
	var v_int_bool_real_6: (int, bool, real) := (11, true, 18.72);
	assert ((v_char_2 == 'I') && (v_int_9 == -1) && (v_bool_1 == false) && (v_int_bool_real_1.2 == 18.72) && (v_int_bool_real_1 == v_int_bool_real_6));
	expect ((v_char_2 == 'I') && (v_int_9 == -1) && (v_bool_1 == false) && (v_int_bool_real_1.2 == 18.72) && (v_int_bool_real_1 == v_int_bool_real_6));
	var v_DT_1_1_1: DT_1<bool> := DT_1_1;
	var v_DT_1_1_2: DT_1<bool> := DT_1_1;
	var v_seq_6: seq<DT_1<bool>> := [v_DT_1_1_1, v_DT_1_1_2];
	var v_int_10: int := 6;
	var v_seq_177: seq<DT_1<bool>> := v_seq_6;
	var v_int_215: int := v_int_10;
	var v_int_216: int := safe_index_seq(v_seq_177, v_int_215);
	v_int_10 := v_int_216;
	var v_DT_1_1_3: DT_1<bool> := DT_1_1;
	var v_int_bool_real_7: (int, bool, real) := (11, true, 18.72);
	var v_int_bool_real_8: (int, bool, real) := (11, true, 18.72);
	var v_int_real_bool_6: (int, real, bool) := (1, -10.56, false);
	var v_int_real_bool_7: (int, real, bool) := (1, -10.56, false);
	print "v_bool_1", " ", v_bool_1, " ", "v_int_real_bool_1.1", " ", (v_int_real_bool_1.1 == -10.56), " ", "v_char_3", " ", (v_char_3 == 'I'), " ", "v_int_real_bool_1.0", " ", v_int_real_bool_1.0, " ", "v_char_2", " ", (v_char_2 == 'I'), " ", "v_int_bool_real_2", " ", (v_int_bool_real_2 == v_int_bool_real_7), " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_int_bool_real_1", " ", (v_int_bool_real_1 == v_int_bool_real_8), " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_int_bool_real_1.2", " ", (v_int_bool_real_1.2 == 18.72), " ", "v_int_real_bool_1.2", " ", v_int_real_bool_1.2, " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_10", " ", v_int_10, " ", "v_int_bool_real_1.0", " ", v_int_bool_real_1.0, " ", "v_int_bool_real_1.1", " ", v_int_bool_real_1.1, " ", "v_int_9", " ", v_int_9, " ", "v_int_real_bool_2", " ", (v_int_real_bool_2 == v_int_real_bool_6), " ", "v_int_real_bool_1", " ", (v_int_real_bool_1 == v_int_real_bool_7), " ", "v_DT_1_1_1", " ", v_DT_1_1_1, "\n";
	return (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_10]) else (v_DT_1_1_3));
}

method m_method_1(p_m_method_1_1: seq<int>) returns (ret_1: DT_1<bool>)
	requires (|p_m_method_1_1| == 4 && (p_m_method_1_1[0] == 5) && (p_m_method_1_1[1] == 0) && (p_m_method_1_1[2] == 1) && (p_m_method_1_1[3] == 14));
	ensures ((|p_m_method_1_1| == 4 && (p_m_method_1_1[0] == 5) && (p_m_method_1_1[1] == 0) && (p_m_method_1_1[2] == 1) && (p_m_method_1_1[3] == 14)) ==> ((ret_1.DT_1_1? && ((ret_1 == DT_1_1)))));
{
	var v_seq_7: seq<int> := ([] + [2, 24]);
	var v_DT_1_1_4: DT_1<bool> := m_method_2(v_seq_7);
	print "v_seq_7", " ", v_seq_7, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, "\n";
	return v_DT_1_1_4;
}

method m_method_10(p_m_method_10_1: char, p_m_method_10_2: char, p_m_method_10_3: char) returns (ret_1: (bool, (real, real, int)))
	requires ((p_m_method_10_2 == 'L') && (p_m_method_10_3 == 'A') && (p_m_method_10_1 == 'm'));
	ensures (((p_m_method_10_2 == 'L') && (p_m_method_10_3 == 'A') && (p_m_method_10_1 == 'm')) ==> (((ret_1).0 == false) && (21.42 < ((ret_1).1).0 < 21.62) && (-1.89 < ((ret_1).1).1 < -1.69) && (((ret_1).1).2 == 13)));
{
	if false {
		var v_real_real_int_1: (real, real, int) := (-19.92, 20.17, 28);
		var v_bool_real_real_int_1: (bool, (real, real, int)) := (true, v_real_real_int_1);
		return v_bool_real_real_int_1;
	} else {
		var v_real_real_int_2: (real, real, int) := (21.52, -1.79, 13);
		var v_bool_real_real_int_2: (bool, (real, real, int)) := (false, v_real_real_int_2);
		var v_real_real_int_3: (real, real, int) := (21.52, -1.79, 13);
		var v_real_real_int_4: (real, real, int) := (21.52, -1.79, 13);
		var v_bool_real_real_int_5: (bool, (real, real, int)) := (false, v_real_real_int_4);
		var v_real_real_int_5: (real, real, int) := (21.52, -1.79, 13);
		print "v_real_real_int_2.0", " ", (v_real_real_int_2.0 == 21.52), " ", "v_real_real_int_2", " ", (v_real_real_int_2 == v_real_real_int_3), " ", "v_real_real_int_2.2", " ", v_real_real_int_2.2, " ", "v_real_real_int_2.1", " ", (v_real_real_int_2.1 == -1.79), " ", "v_bool_real_real_int_2", " ", (v_bool_real_real_int_2 == v_bool_real_real_int_5), " ", "v_bool_real_real_int_2.1", " ", (v_bool_real_real_int_2.1 == v_real_real_int_5), " ", "v_bool_real_real_int_2.0", " ", v_bool_real_real_int_2.0, " ", "p_m_method_10_3", " ", (p_m_method_10_3 == 'A'), " ", "p_m_method_10_1", " ", (p_m_method_10_1 == 'm'), " ", "p_m_method_10_2", " ", (p_m_method_10_2 == 'L'), "\n";
		return v_bool_real_real_int_2;
	}
}

method m_method_11(p_m_method_11_1: (int, bool, int), p_m_method_11_2: char, p_m_method_11_3: char, p_m_method_11_4: char) returns (ret_1: char, ret_2: char, ret_3: char, ret_4: char, ret_5: char)
	requires ((p_m_method_11_3 == 'K') && (p_m_method_11_4 == 'K') && ((p_m_method_11_1).0 == 25) && ((p_m_method_11_1).1 == false) && ((p_m_method_11_1).2 == 18) && (p_m_method_11_2 == 'K'));
	ensures (((p_m_method_11_3 == 'K') && (p_m_method_11_4 == 'K') && ((p_m_method_11_1).0 == 25) && ((p_m_method_11_1).1 == false) && ((p_m_method_11_1).2 == 18) && (p_m_method_11_2 == 'K')) ==> ((ret_1 == 'I') && (ret_2 == 'I') && (ret_3 == 'K') && (ret_4 == 'w') && (ret_5 == 'O')));
{
	var v_int_bool_real_3: (int, bool, real) := (5, false, 4.40);
	var v_int_bool_real_4: (int, bool, real) := v_int_bool_real_3;
	var v_int_real_bool_3: (int, real, bool) := (15, 3.12, true);
	var v_int_real_bool_4: (int, real, bool) := v_int_real_bool_3;
	var v_char_12: char := m_method_3(v_int_bool_real_4, v_int_real_bool_4);
	var v_seq_15: seq<char> := ['w'];
	var v_int_36: int := 13;
	var v_seq_183: seq<char> := v_seq_15;
	var v_int_227: int := v_int_36;
	var v_int_228: int := safe_index_seq(v_seq_183, v_int_227);
	v_int_36 := v_int_228;
	var v_int_bool_real_9: (int, bool, real) := (5, false, 4.40);
	var v_int_bool_real_10: (int, bool, real) := (5, false, 4.40);
	var v_int_real_bool_8: (int, real, bool) := (15, 3.12, true);
	var v_int_real_bool_9: (int, real, bool) := (15, 3.12, true);
	print "p_m_method_11_1.0", " ", p_m_method_11_1.0, " ", "p_m_method_11_1.2", " ", p_m_method_11_1.2, " ", "p_m_method_11_1.1", " ", p_m_method_11_1.1, " ", "v_int_bool_real_4", " ", (v_int_bool_real_4 == v_int_bool_real_9), " ", "v_char_12", " ", (v_char_12 == 'I'), " ", "v_int_bool_real_3", " ", (v_int_bool_real_3 == v_int_bool_real_10), " ", "v_int_bool_real_3.0", " ", v_int_bool_real_3.0, " ", "v_int_bool_real_3.1", " ", v_int_bool_real_3.1, " ", "v_int_bool_real_3.2", " ", (v_int_bool_real_3.2 == 4.40), " ", "v_int_real_bool_3.1", " ", (v_int_real_bool_3.1 == 3.12), " ", "p_m_method_11_1", " ", p_m_method_11_1, " ", "v_int_real_bool_3.0", " ", v_int_real_bool_3.0, " ", "v_int_real_bool_3.2", " ", v_int_real_bool_3.2, " ", "p_m_method_11_4", " ", (p_m_method_11_4 == 'K'), " ", "v_seq_15", " ", (v_seq_15 == ['w']), " ", "p_m_method_11_2", " ", (p_m_method_11_2 == 'K'), " ", "p_m_method_11_3", " ", (p_m_method_11_3 == 'K'), " ", "v_int_36", " ", v_int_36, " ", "v_int_real_bool_4", " ", (v_int_real_bool_4 == v_int_real_bool_8), " ", "v_int_real_bool_3", " ", (v_int_real_bool_3 == v_int_real_bool_9), "\n";
	return v_char_12, v_char_12, (if (false) then ('s') else ('K')), (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_36]) else ('w')), (if (false) then ('t') else ('O'));
}

method m_method_12(p_m_method_12_1: (real, bool)) returns (ret_1: (int, (int, real, int)))
	requires ((-23.61 < (p_m_method_12_1).0 < -23.41) && ((p_m_method_12_1).1 == false));
	ensures (((-23.61 < (p_m_method_12_1).0 < -23.41) && ((p_m_method_12_1).1 == false)) ==> (((ret_1).0 == 24) && (((ret_1).1).0 == 18) && (21.34 < ((ret_1).1).1 < 21.54) && (((ret_1).1).2 == 1)));
{
	var v_int_39: int := 26;
	var v_int_40: int := 11;
	while (v_int_39 < v_int_40) 
		decreases v_int_40 - v_int_39;
		invariant (v_int_39 <= v_int_40);
	{
		v_int_39 := (v_int_39 + 1);
		var v_int_real_int_12: (int, real, int) := (4, 24.74, 5);
		var v_int_int_real_int_12: (int, (int, real, int)) := (21, v_int_real_int_12);
		return v_int_int_real_int_12;
	}
	var v_int_real_int_13: (int, real, int) := (18, 21.44, 1);
	var v_int_int_real_int_13: (int, (int, real, int)) := (24, v_int_real_int_13);
	var v_real_bool_33: (real, bool) := (-23.51, false);
	var v_int_real_int_16: (int, real, int) := (18, 21.44, 1);
	var v_int_real_int_17: (int, real, int) := (18, 21.44, 1);
	var v_int_int_real_int_17: (int, (int, real, int)) := (24, v_int_real_int_17);
	var v_int_real_int_18: (int, real, int) := (18, 21.44, 1);
	print "p_m_method_12_1", " ", (p_m_method_12_1 == v_real_bool_33), " ", "v_int_39", " ", v_int_39, " ", "v_int_real_int_13", " ", (v_int_real_int_13 == v_int_real_int_16), " ", "v_int_int_real_int_13", " ", (v_int_int_real_int_13 == v_int_int_real_int_17), " ", "p_m_method_12_1.1", " ", p_m_method_12_1.1, " ", "p_m_method_12_1.0", " ", (p_m_method_12_1.0 == -23.51), " ", "v_int_real_int_13.2", " ", v_int_real_int_13.2, " ", "v_int_40", " ", v_int_40, " ", "v_int_real_int_13.1", " ", (v_int_real_int_13.1 == 21.44), " ", "v_int_int_real_int_13.0", " ", v_int_int_real_int_13.0, " ", "v_int_real_int_13.0", " ", v_int_real_int_13.0, " ", "v_int_int_real_int_13.1", " ", (v_int_int_real_int_13.1 == v_int_real_int_18), "\n";
	return v_int_int_real_int_13;
}

method m_method_13(p_m_method_13_1: char, p_m_method_13_2: char, p_m_method_13_3: char, p_m_method_13_4: char) returns (ret_1: seq<bool>)
	requires ((p_m_method_13_3 == 'L') && (p_m_method_13_4 == 't') && (p_m_method_13_1 == 'R') && (p_m_method_13_2 == 'V'));
	ensures (((p_m_method_13_3 == 'L') && (p_m_method_13_4 == 't') && (p_m_method_13_1 == 'R') && (p_m_method_13_2 == 'V')) ==> (|ret_1| == 3 && (ret_1[0] == true) && (ret_1[1] == false) && (ret_1[2] == true)));
{
	print "p_m_method_13_2", " ", (p_m_method_13_2 == 'V'), " ", "p_m_method_13_3", " ", (p_m_method_13_3 == 'L'), " ", "p_m_method_13_1", " ", (p_m_method_13_1 == 'R'), " ", "p_m_method_13_4", " ", (p_m_method_13_4 == 't'), "\n";
	return [true, false, true];
}

method Main() returns ()
{
	if false {
		
	} else {
		var v_seq_3: seq<set<int>> := [];
		var v_seq_4: seq<set<int>> := ((if ((|v_seq_3| > 0)) then (v_seq_3[-26..22]) else (v_seq_3)) + ([{18, 26, 17, 0}] + [{0, -14, 19, -2}, {7, 12, -9}]));
		var v_real_real_1: (real, real) := (27.92, -2.38);
		var v_real_real_2: (real, real) := (-22.77, 15.36);
		var v_real_real_3: (real, real) := (6.48, -12.87);
		var v_real_real_4: (real, real) := (-0.23, -27.33);
		var v_real_real_5: (real, real) := (10.72, -11.72);
		var v_array_1: array<set<(real, real)>> := new set<(real, real)>[3] [{}, {v_real_real_1, v_real_real_2, v_real_real_3, v_real_real_4}, {v_real_real_5}];
		var v_int_7: int := (match 'g' {
			case 'm' => |map[multiset{multiset{}, multiset{-10.13, -29.91, 8.84}, multiset{-23.09, -11.99}} := 2, multiset{multiset{-16.75}, multiset({11.77, 21.17, 24.95, -11.68})} := 27, multiset{multiset{23.64, 20.65, 25.35, -18.56}, multiset{-10.38, 12.15, -7.96, -7.97}, multiset({-0.62, -25.33, -9.95, 0.36}), multiset{16.60}} := 15, multiset{multiset{-3.12, -2.21}, multiset({-17.28, 14.21, 1.60}), multiset{1.09, -26.06, -10.49}} := 17, multiset{multiset({6.77, -29.04, -14.93, 11.47})} := 24]|
			case 'F' => (match 'Q' {
				case _ => 4
			})
			case _ => v_array_1.Length
		});
		var v_seq_178: seq<set<int>> := v_seq_4;
		var v_int_217: int := v_int_7;
		var v_int_218: int := safe_index_seq(v_seq_178, v_int_217);
		v_int_7 := v_int_218;
		var v_seq_5: seq<set<int>> := ([{12, 10, -25}, {}, {7}, {}] + []);
		var v_int_8: int := v_int_7;
		var v_map_1: map<char, set<int>> := map['y' := {11}, 'N' := {1}];
		var v_char_1: char := 'C';
		var v_map_4: map<bool, int> := map[true := 26];
		var v_bool_2: bool := false;
		var v_int_23: int := (if ((v_bool_2 in v_map_4)) then (v_map_4[v_bool_2]) else (11));
		var v_seq_9: seq<int> := m_method_4(v_int_23);
		var v_seq_10: seq<int> := v_seq_9;
		var v_DT_1_1_5: DT_1<bool> := m_method_1(v_seq_10);
		var v_array_6: array<int> := new int[5] [26, 5, 6, 22, 6];
		var v_array_7: array<int> := new int[3] [17, 18, 21];
		var v_array_8: array<int> := new int[3] [26, 5, 2];
		var v_array_9: array<int> := new int[4] [4, 13, 27, 0];
		var v_array_10: array<int> := new int[4] [18, 9, 16, 4];
		var v_array_11: array<int> := new int[3];
		v_array_11[0] := 17;
		v_array_11[1] := 9;
		v_array_11[2] := 9;
		var v_array_12: array<int> := new int[4] [9, 12, 22, 4];
		var v_map_5: map<int, multiset<array<int>>> := map[7 := multiset{v_array_6, v_array_7}, 14 := multiset([]), 22 := multiset([v_array_8, v_array_9, v_array_10]), 29 := multiset([v_array_11, v_array_12]), 6 := multiset([])];
		var v_int_24: int := -22;
		var v_array_13: array<int> := new int[5] [3, 28, -8, 18, 24];
		var v_array_14: array<int> := new int[3] [2, 29, 14];
		var v_array_15: array<int> := new int[5] [0, 0, 25, 11, -15];
		var v_array_16: array<int> := new int[4] [4, 5, 21, 4];
		var v_array_17: array<int> := new int[4] [-21, 10, 0, 2];
		var v_array_18: array<int> := new int[5];
		v_array_18[0] := 19;
		v_array_18[1] := 16;
		v_array_18[2] := 17;
		v_array_18[3] := 16;
		v_array_18[4] := -24;
		var v_array_19: array<int> := new int[5] [2, 26, 14, 3, 16];
		var v_array_20: array<int> := new int[4] [12, -11, 7, 2];
		var v_array_21: array<int> := new int[3] [-25, 15, 18];
		var v_array_22: array<int> := new int[5] [9, 28, -8, 29, 25];
		var v_seq_11: seq<multiset<array<int>>> := [multiset([v_array_16, v_array_17, v_array_18]), multiset{v_array_19, v_array_20, v_array_21, v_array_22}];
		var v_int_25: int := 19;
		var v_seq_179: seq<multiset<array<int>>> := v_seq_11;
		var v_int_219: int := v_int_25;
		var v_int_220: int := safe_index_seq(v_seq_179, v_int_219);
		v_int_25 := v_int_220;
		var v_array_23: array<int> := new int[4] [14, 10, 25, -3];
		var v_array_24: array<int> := new int[4] [27, 29, 18, 20];
		var v_array_25: array<int> := new int[4];
		v_array_25[0] := 18;
		v_array_25[1] := 26;
		v_array_25[2] := 6;
		v_array_25[3] := 13;
		var v_array_26: array<int> := new int[5] [10, 16, 20, 21, -10];
		var v_array_27: array<int> := new int[3] [-1, -15, 26];
		var v_array_28: array<int> := new int[4] [23, 23, 13, 27];
		var v_array_29: array<int> := new int[3];
		v_array_29[0] := 11;
		v_array_29[1] := -24;
		v_array_29[2] := 10;
		var v_array_30: array<int> := new int[4] [5, 24, -17, 26];
		var v_array_31: array<int> := new int[3];
		v_array_31[0] := 28;
		v_array_31[1] := 1;
		v_array_31[2] := 10;
		var v_array_32: array<int> := new int[3];
		v_array_32[0] := -20;
		v_array_32[1] := -12;
		v_array_32[2] := 21;
		var v_array_33: array<int> := new int[5] [10, 17, 9, 18, 23];
		var v_array_34: array<int> := new int[3] [5, 0, 11];
		var v_int_real_1: (int, real) := (8, 27.24);
		var v_real_bool_1: (real, bool) := (-9.14, true);
		var v_bool_int_bool_1: (bool, int, bool) := (true, -29, false);
		var v_int_real_real_bool_bool_int_bool_1: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_1, v_real_bool_1, v_bool_int_bool_1);
		var v_DT_1_1_6: DT_1<bool> := DT_1_1;
		var v_DT_1_1_7: DT_1<bool> := DT_1_1;
		var v_DT_1_1_8: DT_1<bool> := DT_1_1;
		var v_int_real_2: (int, real) := (8, -28.07);
		var v_real_bool_2: (real, bool) := (-17.23, true);
		var v_bool_int_bool_2: (bool, int, bool) := (false, -11, false);
		var v_int_real_real_bool_bool_int_bool_2: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_2, v_real_bool_2, v_bool_int_bool_2);
		var v_DT_1_1_9: DT_1<bool> := DT_1_1;
		var v_DT_1_1_10: DT_1<bool> := DT_1_1;
		var v_DT_1_1_11: DT_1<bool> := DT_1_1;
		var v_DT_1_1_12: DT_1<bool> := DT_1_1;
		var v_DT_1_1_13: DT_1<bool> := DT_1_1;
		var v_DT_1_1_14: DT_1<bool> := DT_1_1;
		var v_DT_1_1_15: DT_1<bool> := DT_1_1;
		var v_int_real_3: (int, real) := (-25, -14.83);
		var v_real_bool_3: (real, bool) := (27.46, false);
		var v_bool_int_bool_3: (bool, int, bool) := (false, 29, true);
		var v_int_real_real_bool_bool_int_bool_3: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_3, v_real_bool_3, v_bool_int_bool_3);
		var v_DT_1_1_16: DT_1<bool> := DT_1_1;
		var v_DT_1_1_17: DT_1<bool> := DT_1_1;
		var v_DT_1_1_18: DT_1<bool> := DT_1_1;
		var v_DT_1_1_19: DT_1<bool> := DT_1_1;
		var v_int_real_4: (int, real) := (18, -27.51);
		var v_real_bool_4: (real, bool) := (-1.42, false);
		var v_bool_int_bool_4: (bool, int, bool) := (true, 17, false);
		var v_int_real_real_bool_bool_int_bool_4: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_4, v_real_bool_4, v_bool_int_bool_4);
		var v_DT_1_1_20: DT_1<bool> := DT_1_1;
		var v_DT_1_1_21: DT_1<bool> := DT_1_1;
		var v_DT_1_1_22: DT_1<bool> := DT_1_1;
		var v_DT_1_1_23: DT_1<bool> := DT_1_1;
		var v_DT_1_1_24: DT_1<bool> := DT_1_1;
		var v_DT_1_1_25: DT_1<bool> := DT_1_1;
		var v_DT_1_1_26: DT_1<bool> := DT_1_1;
		var v_int_real_5: (int, real) := (4, -13.99);
		var v_real_bool_5: (real, bool) := (-11.50, true);
		var v_bool_int_bool_5: (bool, int, bool) := (true, 14, true);
		var v_int_real_real_bool_bool_int_bool_5: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_5, v_real_bool_5, v_bool_int_bool_5);
		var v_int_real_6: (int, real) := (12, 28.54);
		var v_real_bool_6: (real, bool) := (-13.73, true);
		var v_bool_int_bool_6: (bool, int, bool) := (false, 3, true);
		var v_int_real_real_bool_bool_int_bool_6: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_6, v_real_bool_6, v_bool_int_bool_6);
		var v_DT_1_1_27: DT_1<bool> := DT_1_1;
		var v_DT_1_1_28: DT_1<bool> := DT_1_1;
		var v_DT_1_1_29: DT_1<bool> := DT_1_1;
		var v_DT_1_1_30: DT_1<bool> := DT_1_1;
		var v_DT_1_1_31: DT_1<bool> := DT_1_1;
		var v_DT_1_1_32: DT_1<bool> := DT_1_1;
		var v_int_real_7: (int, real) := (25, 24.66);
		var v_real_bool_7: (real, bool) := (5.83, true);
		var v_bool_int_bool_7: (bool, int, bool) := (true, 18, true);
		var v_int_real_real_bool_bool_int_bool_7: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_7, v_real_bool_7, v_bool_int_bool_7);
		var v_DT_1_1_33: DT_1<bool> := DT_1_1;
		var v_DT_1_1_34: DT_1<bool> := DT_1_1;
		var v_int_real_8: (int, real) := (14, 29.08);
		var v_real_bool_8: (real, bool) := (-28.32, false);
		var v_bool_int_bool_8: (bool, int, bool) := (false, 19, false);
		var v_int_real_real_bool_bool_int_bool_8: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_8, v_real_bool_8, v_bool_int_bool_8);
		var v_DT_1_1_35: DT_1<bool> := DT_1_1;
		var v_DT_1_1_36: DT_1<bool> := DT_1_1;
		var v_DT_1_1_37: DT_1<bool> := DT_1_1;
		var v_DT_1_1_38: DT_1<bool> := DT_1_1;
		var v_DT_1_1_39: DT_1<bool> := DT_1_1;
		var v_DT_1_1_40: DT_1<bool> := DT_1_1;
		var v_DT_1_1_41: DT_1<bool> := DT_1_1;
		var v_DT_1_1_42: DT_1<bool> := DT_1_1;
		var v_map_6: map<((int, real), (real, bool), (bool, int, bool)), seq<multiset<DT_1<bool>>>> := (match -19 {
			case -12 => map[v_int_real_real_bool_bool_int_bool_1 := [multiset{v_DT_1_1_6, v_DT_1_1_7, v_DT_1_1_8}], v_int_real_real_bool_bool_int_bool_2 := [multiset({v_DT_1_1_9, v_DT_1_1_10, v_DT_1_1_11}), multiset{v_DT_1_1_12}, multiset{v_DT_1_1_13, v_DT_1_1_14, v_DT_1_1_15}], v_int_real_real_bool_bool_int_bool_3 := [multiset{v_DT_1_1_16, v_DT_1_1_17, v_DT_1_1_18}, multiset({}), multiset({v_DT_1_1_19}), multiset({})], v_int_real_real_bool_bool_int_bool_4 := [multiset({v_DT_1_1_20, v_DT_1_1_21}), multiset{v_DT_1_1_22, v_DT_1_1_23, v_DT_1_1_24, v_DT_1_1_25}, multiset{}, multiset{v_DT_1_1_26}], v_int_real_real_bool_bool_int_bool_5 := []]
			case _ => map[v_int_real_real_bool_bool_int_bool_6 := [multiset{v_DT_1_1_27, v_DT_1_1_28}, multiset({v_DT_1_1_29, v_DT_1_1_30, v_DT_1_1_31}), multiset{}, multiset{v_DT_1_1_32}], v_int_real_real_bool_bool_int_bool_7 := [multiset{}, multiset{v_DT_1_1_33, v_DT_1_1_34}], v_int_real_real_bool_bool_int_bool_8 := [multiset({}), multiset{v_DT_1_1_35, v_DT_1_1_36, v_DT_1_1_37, v_DT_1_1_38}, multiset{v_DT_1_1_39}, multiset({v_DT_1_1_40, v_DT_1_1_41, v_DT_1_1_42})]]
		});
		var v_bool_bool_1: (bool, bool) := (false, false);
		var v_bool_bool_2: (bool, bool) := v_bool_bool_1;
		var v_array_35: array<int> := new int[5] [1, 4, 9, 9, 20];
		var v_array_36: array<int> := v_array_35;
		var v_int_real_real_bool_bool_int_bool_13: ((int, real), (real, bool), (bool, int, bool)) := m_method_6(v_bool_bool_2, v_array_36);
		var v_int_real_real_bool_bool_int_bool_14: ((int, real), (real, bool), (bool, int, bool)) := v_int_real_real_bool_bool_int_bool_13;
		var v_DT_1_1_43: DT_1<bool> := DT_1_1;
		var v_DT_1_1_44: DT_1<bool> := DT_1_1;
		var v_DT_1_1_45: DT_1<bool> := DT_1_1;
		var v_DT_1_1_46: DT_1<bool> := DT_1_1;
		var v_DT_1_1_47: DT_1<bool> := DT_1_1;
		var v_DT_1_1_48: DT_1<bool> := DT_1_1;
		var v_DT_1_1_49: DT_1<bool> := DT_1_1;
		var v_DT_1_1_50: DT_1<bool> := DT_1_1;
		var v_DT_1_1_51: DT_1<bool> := DT_1_1;
		var v_DT_1_1_52: DT_1<bool> := DT_1_1;
		var v_DT_1_1_53: DT_1<bool> := DT_1_1;
		var v_DT_1_1_54: DT_1<bool> := DT_1_1;
		var v_DT_1_1_55: DT_1<bool> := DT_1_1;
		var v_DT_1_1_56: DT_1<bool> := DT_1_1;
		var v_seq_12: seq<multiset<DT_1<bool>>> := (if ((v_int_real_real_bool_bool_int_bool_14 in v_map_6)) then (v_map_6[v_int_real_real_bool_bool_int_bool_14]) else ((if (true) then ([multiset{v_DT_1_1_43, v_DT_1_1_44, v_DT_1_1_45, v_DT_1_1_46}]) else ([multiset{v_DT_1_1_47, v_DT_1_1_48, v_DT_1_1_49, v_DT_1_1_50}, multiset{v_DT_1_1_51, v_DT_1_1_52, v_DT_1_1_53}, multiset({v_DT_1_1_54, v_DT_1_1_55, v_DT_1_1_56})]))));
		var v_int_32: int := ((if (true) then (-1.95) else (11.45))).Floor;
		var v_seq_180: seq<multiset<DT_1<bool>>> := v_seq_12;
		var v_int_221: int := v_int_32;
		var v_int_222: int := safe_index_seq(v_seq_180, v_int_221);
		v_int_32 := v_int_222;
		var v_bool_3: bool := true;
		var v_char_4: char := 'G';
		var v_bool_4: bool := m_method_7(v_bool_3, v_char_4);
		var v_DT_1_1_57: DT_1<bool> := DT_1_1;
		var v_DT_1_1_58: DT_1<bool> := DT_1_1;
		var v_DT_1_1_59: DT_1<bool> := DT_1_1;
		var v_DT_1_1_60: DT_1<bool> := DT_1_1;
		var v_set_1: set<int>, v_DT_1_1_61: DT_1<bool>, v_multiset_1: multiset<array<int>>, v_multiset_2: multiset<DT_1<bool>> := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_7]) else ((if ((|v_seq_5| > 0)) then (v_seq_5[v_int_8]) else ((if ((v_char_1 in v_map_1)) then (v_map_1[v_char_1]) else ({17, 5})))))), v_DT_1_1_5, (((if ((v_int_24 in v_map_5)) then (v_map_5[v_int_24]) else (multiset([v_array_13, v_array_14, v_array_15]))) + (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_25]) else (multiset{v_array_23, v_array_24}))) + ((if (false) then (multiset([v_array_25, v_array_26, v_array_27, v_array_28])) else (multiset([v_array_29, v_array_30]))) * (multiset([v_array_31, v_array_32, v_array_33, v_array_34]) * multiset([])))), (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_32]) else ((if (v_bool_4) then ((multiset({v_DT_1_1_57, v_DT_1_1_58}) * multiset{})) else ((multiset({v_DT_1_1_59}) * multiset{v_DT_1_1_60})))));
		var v_seq_13: seq<int> := v_seq_10;
		var v_int_33: int := ((if (true) then (7) else (2)) * v_array_13[4]);
		var v_int_34: int := safe_index_seq(v_seq_13, v_int_33);
		var v_int_real_int_1: (int, real, int) := (28, -13.05, 9);
		var v_int_int_real_int_1: (int, (int, real, int)) := (-8, v_int_real_int_1);
		var v_int_real_int_2: (int, real, int) := (25, 21.38, 13);
		var v_int_int_real_int_2: (int, (int, real, int)) := (22, v_int_real_int_2);
		var v_int_real_int_3: (int, real, int) := (8, -26.01, 21);
		var v_int_int_real_int_3: (int, (int, real, int)) := (-14, v_int_real_int_3);
		var v_int_real_int_4: (int, real, int) := (6, -8.29, -19);
		var v_int_int_real_int_4: (int, (int, real, int)) := (12, v_int_real_int_4);
		var v_int_real_int_5: (int, real, int) := (10, -25.78, -4);
		var v_int_int_real_int_5: (int, (int, real, int)) := (20, v_int_real_int_5);
		var v_int_real_int_6: (int, real, int) := (13, 19.76, 26);
		var v_int_int_real_int_6: (int, (int, real, int)) := (19, v_int_real_int_6);
		var v_int_real_int_7: (int, real, int) := (11, -15.88, 18);
		var v_int_int_real_int_7: (int, (int, real, int)) := (22, v_int_real_int_7);
		var v_int_real_int_8: (int, real, int) := (18, 11.45, 25);
		var v_int_int_real_int_8: (int, (int, real, int)) := (9, v_int_real_int_8);
		var v_int_real_int_9: (int, real, int) := (10, 14.15, 28);
		var v_int_int_real_int_9: (int, (int, real, int)) := (28, v_int_real_int_9);
		var v_int_real_int_10: (int, real, int) := (8, 29.46, 16);
		var v_int_int_real_int_10: (int, (int, real, int)) := (13, v_int_real_int_10);
		var v_int_real_int_11: (int, real, int) := (4, 10.64, 19);
		var v_int_int_real_int_11: (int, (int, real, int)) := (27, v_int_real_int_11);
		var v_map_9: map<seq<seq<bool>>, (int, (int, real, int))> := (if (v_bool_bool_1.1) then ((if (true) then (map[[[true, false], [], [false, true, false, true], []] := v_int_int_real_int_1, [[false, true, true], [false, true, true, false]] := v_int_int_real_int_2]) else (map[[] := v_int_int_real_int_3, [] := v_int_int_real_int_4]))) else ((map[[] := v_int_int_real_int_5, [[true, false], [true], [false, false, false, true], [true]] := v_int_int_real_int_6] + map[[[false]] := v_int_int_real_int_7, [] := v_int_int_real_int_8, [[false, true, true], []] := v_int_int_real_int_9, [[false, false], [true, true, true], [], [true, true]] := v_int_int_real_int_10, [[true], [false], [true, true]] := v_int_int_real_int_11])));
		var v_int_38: int := v_array_28[2];
		var v_seq_17: seq<seq<bool>> := m_method_8(v_int_38);
		var v_seq_19: seq<seq<bool>> := v_seq_17;
		var v_real_bool_18: (real, bool) := (-23.51, false);
		var v_real_bool_19: (real, bool) := v_real_bool_18;
		var v_int_int_real_int_14: (int, (int, real, int)) := m_method_12(v_real_bool_19);
		var v_int_real_int_14: (int, real, int) := (18, -6.24, 14);
		var v_int_int_real_int_15: (int, (int, real, int)) := (-8, v_int_real_int_14);
		var v_seq_18: seq<(int, (int, real, int))> := [v_int_int_real_int_15];
		var v_int_41: int := 0;
		var v_int_real_int_15: (int, real, int) := (21, -18.00, -14);
		var v_int_int_real_int_16: (int, (int, real, int)) := (6, v_int_real_int_15);
		v_array_9[3], v_int_int_real_int_7 := v_int_34, (if ((v_seq_19 in v_map_9)) then (v_map_9[v_seq_19]) else ((if ((match 'E' {
			case 'K' => true
			case 'h' => false
			case _ => false
		})) then (v_int_int_real_int_14) else ((if ((|v_seq_18| > 0)) then (v_seq_18[v_int_41]) else (v_int_int_real_int_16))))));
		match v_char_4 {
			case 'T' => {
				
			}
				case _ => {
				var v_char_21: char := 'R';
				var v_char_22: char := 'V';
				var v_char_23: char := 'L';
				var v_char_24: char := 't';
				var v_seq_20: seq<bool> := m_method_13(v_char_21, v_char_22, v_char_23, v_char_24);
				var v_seq_22: seq<bool> := v_seq_20;
				var v_seq_21: seq<int> := [];
				var v_int_42: int := 9;
				var v_int_43: int := (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_42]) else (29));
				var v_seq_184: seq<bool> := v_seq_22;
				var v_int_229: int := v_int_43;
				var v_int_230: int := safe_index_seq(v_seq_184, v_int_229);
				v_int_43 := v_int_230;
				var v_bool_5: bool := true;
				var v_char_25: char := 'a';
				var v_bool_6: bool := m_method_7(v_bool_5, v_char_25);
				if (match 'G' {
					case 'j' => v_bool_3
					case 'a' => v_bool_4
					case _ => (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_43]) else (v_bool_6))
				}) {
					assert ((v_array_36 == v_array_35) && (v_real_bool_18.1 == false) && (v_array_24[1] == 29) && (v_array_17[3] == 2));
					expect ((v_array_36 == v_array_35) && (v_real_bool_18.1 == false) && (v_array_24[1] == 29) && (v_array_17[3] == 2));
					var v_seq_23: seq<map<char, bool>> := [];
					var v_int_44: int := 25;
					var v_map_10: map<char, bool> := (if ((|v_seq_23| > 0)) then (v_seq_23[v_int_44]) else (map['g' := true]));
					var v_char_26: char := v_char_4;
					var v_bool_9: bool := (if ((v_char_26 in v_map_10)) then (v_map_10[v_char_26]) else (v_bool_3));
					var v_bool_7: bool := false;
					var v_char_27: char := 'v';
					var v_bool_8: bool := m_method_7(v_bool_7, v_char_27);
					var v_char_28: char := (if (v_bool_8) then ((match 'P' {
						case _ => 'f'
					})) else ((match 'S' {
						case 'O' => 'E'
						case _ => 'r'
					})));
					var v_bool_10: bool := m_method_7(v_bool_9, v_char_28);
					if v_bool_10 {
						return ;
					} else {
						
					}
					var v_seq_24: seq<bool> := (if ((8 > 12)) then (([] + [true, true])) else (([true, false, true] + [true])));
					var v_map_11: map<char, int> := map['W' := 28, 'w' := 23, 'l' := 4, 'v' := 26];
					var v_char_29: char := 'N';
					var v_int_45: int := (match 'T' {
						case 'P' => (if (true) then (17) else (0))
						case 'E' => (if ((v_char_29 in v_map_11)) then (v_map_11[v_char_29]) else (16))
						case _ => (if (true) then (29) else (10))
					});
					var v_seq_185: seq<bool> := v_seq_24;
					var v_int_231: int := v_int_45;
					var v_int_232: int := safe_index_seq(v_seq_185, v_int_231);
					v_int_45 := v_int_232;
					if (if ((|v_seq_24| > 0)) then (v_seq_24[v_int_45]) else (v_bool_bool_1.0)) {
						var v_int_real_int_19: (int, real, int) := (8, -26.01, 21);
						var v_int_int_real_int_18: (int, (int, real, int)) := (-14, v_int_real_int_19);
						var v_int_real_int_20: (int, real, int) := (25, 21.38, 13);
						var v_int_int_real_int_19: (int, (int, real, int)) := (22, v_int_real_int_20);
						var v_int_real_int_21: (int, real, int) := (28, -13.05, 9);
						var v_int_int_real_int_20: (int, (int, real, int)) := (-8, v_int_real_int_21);
						var v_int_real_int_22: (int, real, int) := (18, -6.24, 14);
						var v_int_int_real_int_21: (int, (int, real, int)) := (-8, v_int_real_int_22);
						var v_int_real_int_23: (int, real, int) := (13, 19.76, 26);
						var v_int_int_real_int_22: (int, (int, real, int)) := (19, v_int_real_int_23);
						var v_int_real_int_24: (int, real, int) := (10, -25.78, -4);
						var v_int_int_real_int_23: (int, (int, real, int)) := (20, v_int_real_int_24);
						var v_int_real_int_25: (int, real, int) := (6, -8.29, -19);
						var v_int_int_real_int_24: (int, (int, real, int)) := (12, v_int_real_int_25);
						var v_int_real_int_26: (int, real, int) := (10, 14.15, 28);
						var v_int_int_real_int_25: (int, (int, real, int)) := (28, v_int_real_int_26);
						var v_int_real_int_27: (int, real, int) := (18, 11.45, 25);
						var v_int_int_real_int_26: (int, (int, real, int)) := (9, v_int_real_int_27);
						var v_int_real_int_28: (int, real, int) := (10, -25.78, -4);
						var v_int_real_int_29: (int, real, int) := (8, 29.46, 16);
						var v_int_int_real_int_27: (int, (int, real, int)) := (13, v_int_real_int_29);
						var v_int_real_int_30: (int, real, int) := (4, 10.64, 19);
						var v_int_int_real_int_28: (int, (int, real, int)) := (27, v_int_real_int_30);
						var v_int_real_int_31: (int, real, int) := (18, 21.44, 1);
						var v_int_int_real_int_29: (int, (int, real, int)) := (24, v_int_real_int_31);
						var v_int_real_int_32: (int, real, int) := (18, -6.24, 14);
						var v_int_int_real_int_30: (int, (int, real, int)) := (-8, v_int_real_int_32);
						var v_int_real_int_33: (int, real, int) := (18, -6.24, 14);
						var v_int_real_int_34: (int, real, int) := (21, -18.00, -14);
						var v_int_int_real_int_31: (int, (int, real, int)) := (6, v_int_real_int_34);
						var v_int_real_16: (int, real) := (15, -3.37);
						var v_real_bool_34: (real, bool) := (24.44, true);
						var v_bool_int_bool_14: (bool, int, bool) := (true, 11, true);
						var v_int_real_real_bool_bool_int_bool_16: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_16, v_real_bool_34, v_bool_int_bool_14);
						var v_int_real_17: (int, real) := (15, -3.37);
						var v_real_bool_35: (real, bool) := (24.44, true);
						var v_bool_int_bool_15: (bool, int, bool) := (true, 11, true);
						var v_int_real_real_bool_bool_int_bool_17: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_17, v_real_bool_35, v_bool_int_bool_15);
						var v_int_real_int_35: (int, real, int) := (6, -8.29, -19);
						var v_real_bool_36: (real, bool) := (-23.51, false);
						var v_real_bool_37: (real, bool) := (-23.51, false);
						var v_int_real_int_36: (int, real, int) := (18, -6.24, 14);
						var v_int_real_int_37: (int, real, int) := (8, 29.46, 16);
						var v_int_real_int_38: (int, real, int) := (18, -6.24, 14);
						var v_int_real_int_39: (int, real, int) := (4, 10.64, 19);
						var v_int_real_int_40: (int, real, int) := (21, -18.00, -14);
						var v_int_real_int_41: (int, real, int) := (18, -6.24, 14);
						var v_int_int_real_int_32: (int, (int, real, int)) := (-8, v_int_real_int_41);
						var v_DT_1_1_62: DT_1<bool> := DT_1_1;
						var v_DT_1_1_63: DT_1<bool> := DT_1_1;
						var v_DT_1_1_64: DT_1<bool> := DT_1_1;
						var v_DT_1_1_65: DT_1<bool> := DT_1_1;
						var v_int_real_int_42: (int, real, int) := (13, 19.76, 26);
						var v_DT_1_1_66: DT_1<bool> := DT_1_1;
						var v_DT_1_1_67: DT_1<bool> := DT_1_1;
						var v_DT_1_1_68: DT_1<bool> := DT_1_1;
						var v_DT_1_1_69: DT_1<bool> := DT_1_1;
						var v_int_real_int_43: (int, real, int) := (28, -13.05, 9);
						var v_int_real_int_44: (int, real, int) := (10, 14.15, 28);
						var v_int_real_int_45: (int, real, int) := (4, 10.64, 19);
						var v_int_real_18: (int, real) := (14, 29.08);
						var v_real_bool_38: (real, bool) := (-28.32, false);
						var v_bool_int_bool_16: (bool, int, bool) := (false, 19, false);
						var v_int_real_real_bool_bool_int_bool_18: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_18, v_real_bool_38, v_bool_int_bool_16);
						var v_DT_1_1_70: DT_1<bool> := DT_1_1;
						var v_DT_1_1_71: DT_1<bool> := DT_1_1;
						var v_DT_1_1_72: DT_1<bool> := DT_1_1;
						var v_DT_1_1_73: DT_1<bool> := DT_1_1;
						var v_DT_1_1_74: DT_1<bool> := DT_1_1;
						var v_DT_1_1_75: DT_1<bool> := DT_1_1;
						var v_int_real_19: (int, real) := (25, 24.66);
						var v_real_bool_39: (real, bool) := (5.83, true);
						var v_bool_int_bool_17: (bool, int, bool) := (true, 18, true);
						var v_int_real_real_bool_bool_int_bool_19: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_19, v_real_bool_39, v_bool_int_bool_17);
						var v_DT_1_1_76: DT_1<bool> := DT_1_1;
						var v_DT_1_1_77: DT_1<bool> := DT_1_1;
						var v_int_real_20: (int, real) := (12, 28.54);
						var v_real_bool_40: (real, bool) := (-13.73, true);
						var v_bool_int_bool_18: (bool, int, bool) := (false, 3, true);
						var v_int_real_real_bool_bool_int_bool_20: ((int, real), (real, bool), (bool, int, bool)) := (v_int_real_20, v_real_bool_40, v_bool_int_bool_18);
						var v_DT_1_1_78: DT_1<bool> := DT_1_1;
						var v_DT_1_1_79: DT_1<bool> := DT_1_1;
						var v_DT_1_1_80: DT_1<bool> := DT_1_1;
						var v_DT_1_1_81: DT_1<bool> := DT_1_1;
						var v_int_real_int_46: (int, real, int) := (18, 11.45, 25);
						var v_int_int_real_int_33: (int, (int, real, int)) := (9, v_int_real_int_46);
						var v_int_real_int_47: (int, real, int) := (11, -15.88, 18);
						var v_int_int_real_int_34: (int, (int, real, int)) := (22, v_int_real_int_47);
						var v_int_real_int_48: (int, real, int) := (13, 19.76, 26);
						var v_int_int_real_int_35: (int, (int, real, int)) := (19, v_int_real_int_48);
						var v_int_real_int_49: (int, real, int) := (8, 29.46, 16);
						var v_int_int_real_int_36: (int, (int, real, int)) := (13, v_int_real_int_49);
						var v_int_real_int_50: (int, real, int) := (10, 14.15, 28);
						var v_int_int_real_int_37: (int, (int, real, int)) := (28, v_int_real_int_50);
						var v_int_real_int_51: (int, real, int) := (4, 10.64, 19);
						var v_int_int_real_int_38: (int, (int, real, int)) := (27, v_int_real_int_51);
						var v_int_real_int_52: (int, real, int) := (18, 11.45, 25);
						var v_int_real_int_53: (int, real, int) := (8, 29.46, 16);
						var v_int_real_int_54: (int, real, int) := (8, -26.01, 21);
						var v_int_real_int_55: (int, real, int) := (28, -13.05, 9);
						var v_int_real_int_56: (int, real, int) := (8, -26.01, 21);
						var v_int_real_int_57: (int, real, int) := (25, 21.38, 13);
						var v_int_real_int_58: (int, real, int) := (10, -25.78, -4);
						var v_int_real_int_59: (int, real, int) := (6, -8.29, -19);
						var v_int_real_int_60: (int, real, int) := (11, -15.88, 18);
						var v_int_real_int_61: (int, real, int) := (13, 19.76, 26);
						var v_int_real_int_62: (int, real, int) := (10, 14.15, 28);
						var v_int_real_int_63: (int, real, int) := (18, 11.45, 25);
						var v_int_real_int_64: (int, real, int) := (21, -18.00, -14);
						var v_int_real_int_65: (int, real, int) := (25, 21.38, 13);
						print "v_char_28", " ", (v_char_28 == 'r'), " ", "v_int_45", " ", v_int_45, " ", "v_int_44", " ", v_int_44, " ", "v_char_27", " ", (v_char_27 == 'v'), " ", "v_char_26", " ", (v_char_26 == 'G'), " ", "v_seq_23", " ", (v_seq_23 == []), " ", "v_seq_24", " ", v_seq_24, " ", "v_bool_9", " ", v_bool_9, " ", "v_bool_8", " ", v_bool_8, " ", "v_map_10", " ", (v_map_10 == map['g' := true]), " ", "v_bool_10", " ", v_bool_10, " ", "v_bool_7", " ", v_bool_7, " ", "v_int_int_real_int_3", " ", (v_int_int_real_int_3 == v_int_int_real_int_18), " ", "v_array_13[4]", " ", v_array_13[4], " ", "v_int_int_real_int_2", " ", (v_int_int_real_int_2 == v_int_int_real_int_19), " ", "v_int_int_real_int_1", " ", (v_int_int_real_int_1 == v_int_int_real_int_20), " ", "v_int_int_real_int_7", " ", (v_int_int_real_int_7 == v_int_int_real_int_21), " ", "v_array_20[1]", " ", v_array_20[1], " ", "v_int_int_real_int_6", " ", (v_int_int_real_int_6 == v_int_int_real_int_22), " ", "v_int_int_real_int_5", " ", (v_int_int_real_int_5 == v_int_int_real_int_23), " ", "v_array_14[1]", " ", v_array_14[1], " ", "v_int_int_real_int_4", " ", (v_int_int_real_int_4 == v_int_int_real_int_24), " ", "v_int_real_int_5.1", " ", (v_int_real_int_5.1 == -25.78), " ", "v_int_real_int_5.2", " ", v_int_real_int_5.2, " ", "v_array_25[3]", " ", v_array_25[3], " ", "v_array_26[0]", " ", v_array_26[0], " ", "v_array_32[0]", " ", v_array_32[0], " ", "v_int_real_int_11.1", " ", (v_int_real_int_11.1 == 10.64), " ", "v_int_real_int_11.0", " ", v_int_real_int_11.0, " ", "v_array_19[2]", " ", v_array_19[2], " ", "v_int_int_real_int_9", " ", (v_int_int_real_int_9 == v_int_int_real_int_25), " ", "v_int_int_real_int_8", " ", (v_int_int_real_int_8 == v_int_int_real_int_26), " ", "v_int_41", " ", v_int_41, " ", "v_array_9[0]", " ", v_array_9[0], " ", "v_int_real_int_11.2", " ", v_int_real_int_11.2, " ", "v_array_14[0]", " ", v_array_14[0], " ", "v_array_20[0]", " ", v_array_20[0], " ", "v_array_19[1]", " ", v_array_19[1], " ", "v_array_13[3]", " ", v_array_13[3], " ", "v_int_int_real_int_5.0", " ", v_int_int_real_int_5.0, " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_int_real_int_4.0", " ", v_int_real_int_4.0, " ", "v_int_32", " ", v_int_32, " ", "v_int_real_int_4.1", " ", (v_int_real_int_4.1 == -8.29), " ", "v_set_1", " ", (v_set_1 == {0, 17, 18, 26}), " ", "v_array_26[1]", " ", v_array_26[1], " ", "v_int_38", " ", v_int_38, " ", "v_int_int_real_int_5.1", " ", (v_int_int_real_int_5.1 == v_int_real_int_28), " ", "v_array_32[1]", " ", v_array_32[1], " ", "v_int_int_real_int_10", " ", (v_int_int_real_int_10 == v_int_int_real_int_27), " ", "v_int_int_real_int_11", " ", (v_int_int_real_int_11 == v_int_int_real_int_28), " ", "v_array_18[4]", " ", v_array_18[4], " ", "v_int_int_real_int_14", " ", (v_int_int_real_int_14 == v_int_int_real_int_29), " ", "v_int_int_real_int_15", " ", (v_int_int_real_int_15 == v_int_int_real_int_30), " ", "v_int_int_real_int_15.0", " ", v_int_int_real_int_15.0, " ", "v_array_8[2]", " ", v_array_8[2], " ", "v_int_int_real_int_15.1", " ", (v_int_int_real_int_15.1 == v_int_real_int_33), " ", "v_int_int_real_int_16", " ", (v_int_int_real_int_16 == v_int_int_real_int_31), " ", "v_array_21[0]", " ", v_array_21[0], " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_array_15[0]", " ", v_array_15[0], " ", "v_array_20[3]", " ", v_array_20[3], " ", "v_int_real_real_bool_bool_int_bool_14", " ", (v_int_real_real_bool_bool_int_bool_14 == v_int_real_real_bool_bool_int_bool_16), " ", "v_int_real_int_6.0", " ", v_int_real_int_6.0, " ", "v_int_real_real_bool_bool_int_bool_13", " ", (v_int_real_real_bool_bool_int_bool_13 == v_int_real_real_bool_bool_int_bool_17), " ", "v_int_real_int_6.1", " ", (v_int_real_int_6.1 == 19.76), " ", "v_int_real_int_6.2", " ", v_int_real_int_6.2, " ", "v_array_25[1]", " ", v_array_25[1], " ", "v_array_31[1]", " ", v_array_31[1], " ", "v_array_19[4]", " ", v_array_19[4], " ", "v_array_8[1]", " ", v_array_8[1], " ", "v_array_14[2]", " ", v_array_14[2], " ", "v_array_20[2]", " ", v_array_20[2], " ", "v_int_int_real_int_4.0", " ", v_int_int_real_int_4.0, " ", "v_int_int_real_int_4.1", " ", (v_int_int_real_int_4.1 == v_int_real_int_35), " ", "v_real_bool_18", " ", (v_real_bool_18 == v_real_bool_36), " ", "v_real_bool_19", " ", (v_real_bool_19 == v_real_bool_37), " ", "v_int_real_int_5.0", " ", v_int_real_int_5.0, " ", "v_array_31[2]", " ", v_array_31[2], " ", "v_array_25[2]", " ", v_array_25[2], " ", "v_array_19[3]", " ", v_array_19[3], " ", "v_array_8[0]", " ", v_array_8[0], " ", "v_array_15[2]", " ", v_array_15[2], " ", "v_array_21[2]", " ", v_array_21[2], " ", "v_array_10[1]", " ", v_array_10[1], " ", "v_int_real_int_7.0", " ", v_int_real_int_7.0, " ", "v_int_real_int_7.1", " ", (v_int_real_int_7.1 == -15.88), " ", "v_int_real_int_7.2", " ", v_int_real_int_7.2, " ", "v_array_26[4]", " ", v_array_26[4], " ", "v_array_27[1]", " ", v_array_27[1], " ", "v_bool_bool_1", " ", v_bool_bool_1, " ", "v_bool_bool_2", " ", v_bool_bool_2, " ", "v_array_33[1]", " ", v_array_33[1], " ", "v_array_21[1]", " ", v_array_21[1], " ", "v_array_15[1]", " ", v_array_15[1], " ", "v_array_10[0]", " ", v_array_10[0], " ", "v_array_27[2]", " ", v_array_27[2], " ", "v_int_int_real_int_7.1", " ", (v_int_int_real_int_7.1 == v_int_real_int_36), " ", "v_int_real_int_10", " ", (v_int_real_int_10 == v_int_real_int_37), " ", "v_int_int_real_int_7.0", " ", v_int_int_real_int_7.0, " ", "v_int_real_int_14", " ", (v_int_real_int_14 == v_int_real_int_38), " ", "v_array_33[2]", " ", v_array_33[2], " ", "v_array_9[3]", " ", v_array_9[3], " ", "v_int_real_int_11", " ", (v_int_real_int_11 == v_int_real_int_39), " ", "v_int_real_int_15", " ", (v_int_real_int_15 == v_int_real_int_40), " ", "v_array_16[1]", " ", v_array_16[1], " ", "v_array_15[4]", " ", v_array_15[4], " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_array_10[3]", " ", v_array_10[3], " ", "v_array_22[1]", " ", v_array_22[1], " ", "v_array_11[0]", " ", v_array_11[0], " ", "v_int_real_int_8.2", " ", v_int_real_int_8.2, " ", "v_seq_18", " ", (v_seq_18 == [v_int_int_real_int_32]), " ", "v_bool_4", " ", v_bool_4, " ", "v_seq_19", " ", v_seq_19, " ", "v_int_real_int_8.0", " ", v_int_real_int_8.0, " ", "v_int_real_int_8.1", " ", (v_int_real_int_8.1 == 11.45), " ", "v_int_24", " ", v_int_24, " ", "v_int_23", " ", v_int_23, " ", "v_array_26[2]", " ", v_array_26[2], " ", "v_seq_17", " ", v_seq_17, " ", "v_seq_10", " ", v_seq_10, " ", "v_seq_11", " ", (v_seq_11 == [multiset{v_array_18, v_array_17, v_array_16}, multiset{v_array_22, v_array_19, v_array_20, v_array_21}]), " ", "v_array_32[2]", " ", v_array_32[2], " ", "v_seq_12", " ", (v_seq_12 == [multiset{v_DT_1_1_62, v_DT_1_1_63, v_DT_1_1_64, v_DT_1_1_65}]), " ", "v_int_25", " ", v_int_25, " ", "v_seq_13", " ", v_seq_13, " ", "v_array_9[2]", " ", v_array_9[2], " ", "v_int_real_int_14.2", " ", v_int_real_int_14.2, " ", "v_int_real_int_14.1", " ", (v_int_real_int_14.1 == -6.24), " ", "v_int_real_int_14.0", " ", v_int_real_int_14.0, " ", "v_array_15[3]", " ", v_array_15[3], " ", "v_array_22[0]", " ", v_array_22[0], " ", "v_array_16[0]", " ", v_array_16[0], " ", "v_int_8", " ", v_int_8, " ", "v_array_10[2]", " ", v_array_10[2], " ", "v_int_7", " ", v_int_7, " ", "v_array_26[3]", " ", v_array_26[3], " ", "v_array_27[0]", " ", v_array_27[0], " ", "v_int_int_real_int_6.0", " ", v_int_int_real_int_6.0, " ", "v_array_33[0]", " ", v_array_33[0], " ", "v_int_int_real_int_6.1", " ", (v_int_int_real_int_6.1 == v_int_real_int_42), " ", "v_array_9[1]", " ", v_array_9[1], " ", "v_array_16[3]", " ", v_array_16[3], " ", "v_array_11[2]", " ", v_array_11[2], " ", "v_array_17[0]", " ", v_array_17[0], " ", "v_int_real_int_9.1", " ", (v_int_real_int_9.1 == 14.15), " ", "v_array_22[3]", " ", v_array_22[3], " ", "v_int_real_int_9.2", " ", v_int_real_int_9.2, " ", "v_int_real_int_9.0", " ", v_int_real_int_9.0, " ", "v_array_28[2]", " ", v_array_28[2], " ", "v_array_23[1]", " ", v_array_23[1], " ", "v_array_34[2]", " ", v_array_34[2], " ", "v_int_real_int_15.1", " ", (v_int_real_int_15.1 == -18.00), " ", "v_int_real_int_15.0", " ", v_int_real_int_15.0, " ", "v_array_16[2]", " ", v_array_16[2], " ", "v_int_real_int_15.2", " ", v_int_real_int_15.2, " ", "v_array_22[2]", " ", v_array_22[2], " ", "v_array_11[1]", " ", v_array_11[1], " ", "v_multiset_2", " ", (v_multiset_2 == multiset{v_DT_1_1_66, v_DT_1_1_67, v_DT_1_1_68, v_DT_1_1_69}), " ", "v_int_int_real_int_1.1", " ", (v_int_int_real_int_1.1 == v_int_real_int_43), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{v_array_13, v_array_14, v_array_18, v_array_15, v_array_17, v_array_16}), " ", "v_int_int_real_int_1.0", " ", v_int_int_real_int_1.0, " ", "v_array_29[0]", " ", v_array_29[0], " ", "v_array_28[3]", " ", v_array_28[3], " ", "v_bool_bool_1.1", " ", v_bool_bool_1.1, " ", "v_int_int_real_int_9.1", " ", (v_int_int_real_int_9.1 == v_int_real_int_44), " ", "v_bool_bool_1.0", " ", v_bool_bool_1.0, " ", "v_int_int_real_int_9.0", " ", v_int_int_real_int_9.0, " ", "v_array_23[2]", " ", v_array_23[2], " ", "v_array_35[0]", " ", v_array_35[0], " ", "v_int_int_real_int_11.0", " ", v_int_int_real_int_11.0, " ", "v_int_int_real_int_11.1", " ", (v_int_int_real_int_11.1 == v_int_real_int_45), " ", "v_array_6[0]", " ", v_array_6[0], " ", "v_array_11", " ", (v_array_11 == v_array_11), " ", "v_array_10", " ", (v_array_10 == v_array_10), " ", "v_array_17[2]", " ", v_array_17[2], " ", "v_array_12[1]", " ", v_array_12[1], " ", "v_array_28[0]", " ", v_array_28[0], " ", "v_array_6", " ", (v_array_6 == v_array_6), " ", "v_array_34[0]", " ", v_array_34[0], " ", "v_array_19", " ", (v_array_19 == v_array_19), " ", "v_array_33[3]", " ", v_array_33[3], " ", "v_array_18", " ", (v_array_18 == v_array_18), " ", "v_array_17", " ", (v_array_17 == v_array_17), " ", "v_array_16", " ", (v_array_16 == v_array_16), " ", "v_array_7", " ", (v_array_7 == v_array_7), " ", "v_array_15", " ", (v_array_15 == v_array_15), " ", "v_array_8", " ", (v_array_8 == v_array_8), " ", "v_array_14", " ", (v_array_14 == v_array_14), " ", "v_array_9", " ", (v_array_9 == v_array_9), " ", "v_array_13", " ", (v_array_13 == v_array_13), " ", "v_array_12", " ", (v_array_12 == v_array_12), " ", "v_char_1", " ", (v_char_1 == 'C'), " ", "v_map_5", " ", (v_map_5 == map[22 := multiset{v_array_8, v_array_9, v_array_10}, 6 := multiset{}, 7 := multiset{v_array_7, v_array_6}, 29 := multiset{v_array_11, v_array_12}, 14 := multiset{}]), " ", "v_map_4", " ", (v_map_4 == map[true := 26]), " ", "v_map_6", " ", (v_map_6 == map[v_int_real_real_bool_bool_int_bool_18 := [multiset{}, multiset{v_DT_1_1_70, v_DT_1_1_71, v_DT_1_1_72, v_DT_1_1_73}, multiset{v_DT_1_1_74}, multiset{v_DT_1_1_75}], v_int_real_real_bool_bool_int_bool_19 := [multiset{}, multiset{v_DT_1_1_76, v_DT_1_1_77}], v_int_real_real_bool_bool_int_bool_20 := [multiset{v_DT_1_1_78, v_DT_1_1_79}, multiset{v_DT_1_1_80}, multiset{}, multiset{v_DT_1_1_81}]]), " ", "v_map_9", " ", (v_map_9 == map[[] := v_int_int_real_int_33, [[false]] := v_int_int_real_int_34, [[true, false], [true], [false, false, false, true], [true]] := v_int_int_real_int_35, [[false, false], [true, true, true], [], [true, true]] := v_int_int_real_int_36, [[false, true, true], []] := v_int_int_real_int_37, [[true], [false], [true, true]] := v_int_int_real_int_38]), " ", "v_char_4", " ", (v_char_4 == 'G'), " ", "v_array_17[1]", " ", v_array_17[1], " ", "v_array_12[0]", " ", v_array_12[0], " ", "v_array_22[4]", " ", v_array_22[4], " ", "v_map_1", " ", (v_map_1 == map['y' := {11}, 'N' := {1}]), " ", "v_array_28[1]", " ", v_array_28[1], " ", "v_int_real_int_1.1", " ", (v_int_real_int_1.1 == -13.05), " ", "v_int_real_int_1.2", " ", v_int_real_int_1.2, " ", "v_int_int_real_int_8.0", " ", v_int_int_real_int_8.0, " ", "v_int_int_real_int_8.1", " ", (v_int_int_real_int_8.1 == v_int_real_int_52), " ", "v_int_real_int_1.0", " ", v_int_real_int_1.0, " ", "v_array_23[0]", " ", v_array_23[0], " ", "v_int_int_real_int_10.1", " ", (v_int_int_real_int_10.1 == v_int_real_int_53), " ", "v_array_34[1]", " ", v_array_34[1], " ", "v_array_33[4]", " ", v_array_33[4], " ", "v_int_int_real_int_10.0", " ", v_int_int_real_int_10.0, " ", "v_array_7[1]", " ", v_array_7[1], " ", "v_array_33", " ", (v_array_33 == v_array_33), " ", "v_array_32", " ", (v_array_32 == v_array_32), " ", "v_array_6[4]", " ", v_array_6[4], " ", "v_array_31", " ", (v_array_31 == v_array_31), " ", "v_array_30", " ", (v_array_30 == v_array_30), " ", "v_array_12[3]", " ", v_array_12[3], " ", "v_array_13[0]", " ", v_array_13[0], " ", "v_array_18[1]", " ", v_array_18[1], " ", "v_real_bool_18.1", " ", v_real_bool_18.1, " ", "v_real_bool_18.0", " ", (v_real_bool_18.0 == -23.51), " ", "v_array_24[2]", " ", v_array_24[2], " ", "v_array_30[2]", " ", v_array_30[2], " ", "v_array_35[3]", " ", v_array_35[3], " ", "v_array_36", " ", (v_array_36 == v_array_35), " ", "v_array_35", " ", (v_array_35 == v_array_35), " ", "v_array_7[0]", " ", v_array_7[0], " ", "v_array_34", " ", (v_array_34 == v_array_34), " ", "v_array_22", " ", (v_array_22 == v_array_22), " ", "v_array_7[2]", " ", v_array_7[2], " ", "v_array_21", " ", (v_array_21 == v_array_21), " ", "v_array_20", " ", (v_array_20 == v_array_20), " ", "v_array_17[3]", " ", v_array_17[3], " ", "v_DT_1_1_52", " ", v_DT_1_1_52, " ", "v_DT_1_1_51", " ", v_DT_1_1_51, " ", "v_array_18[0]", " ", v_array_18[0], " ", "v_DT_1_1_50", " ", v_DT_1_1_50, " ", "v_array_12[2]", " ", v_array_12[2], " ", "v_int_int_real_int_3.1", " ", (v_int_int_real_int_3.1 == v_int_real_int_54), " ", "v_int_int_real_int_3.0", " ", v_int_int_real_int_3.0, " ", "v_int_real_int_1", " ", (v_int_real_int_1 == v_int_real_int_55), " ", "v_int_real_int_2.0", " ", v_int_real_int_2.0, " ", "v_int_real_int_2.1", " ", (v_int_real_int_2.1 == 21.38), " ", "v_int_real_int_2.2", " ", v_int_real_int_2.2, " ", "v_int_real_int_3", " ", (v_int_real_int_3 == v_int_real_int_56), " ", "v_int_real_int_2", " ", (v_int_real_int_2 == v_int_real_int_57), " ", "v_array_24[3]", " ", v_array_24[3], " ", "v_array_30[3]", " ", v_array_30[3], " ", "v_int_real_int_5", " ", (v_int_real_int_5 == v_int_real_int_58), " ", "v_int_real_int_4", " ", (v_int_real_int_4 == v_int_real_int_59), " ", "v_array_31[0]", " ", v_array_31[0], " ", "v_int_real_int_7", " ", (v_int_real_int_7 == v_int_real_int_60), " ", "v_array_25[0]", " ", v_array_25[0], " ", "v_int_real_int_6", " ", (v_int_real_int_6 == v_int_real_int_61), " ", "v_DT_1_1_45", " ", v_DT_1_1_45, " ", "v_array_29", " ", (v_array_29 == v_array_29), " ", "v_DT_1_1_44", " ", v_DT_1_1_44, " ", "v_array_28", " ", (v_array_28 == v_array_28), " ", "v_DT_1_1_43", " ", v_DT_1_1_43, " ", "v_array_27", " ", (v_array_27 == v_array_27), " ", "v_array_26", " ", (v_array_26 == v_array_26), " ", "v_array_35[4]", " ", v_array_35[4], " ", "v_DT_1_1_49", " ", v_DT_1_1_49, " ", "v_array_25", " ", (v_array_25 == v_array_25), " ", "v_DT_1_1_48", " ", v_DT_1_1_48, " ", "v_array_24", " ", (v_array_24 == v_array_24), " ", "v_DT_1_1_47", " ", v_DT_1_1_47, " ", "v_array_23", " ", (v_array_23 == v_array_23), " ", "v_DT_1_1_46", " ", v_DT_1_1_46, " ", "v_array_6[2]", " ", v_array_6[2], " ", "v_array_19[0]", " ", v_array_19[0], " ", "v_DT_1_1_61", " ", v_DT_1_1_61, " ", "v_array_13[2]", " ", v_array_13[2], " ", "v_DT_1_1_60", " ", v_DT_1_1_60, " ", "v_int_real_int_9", " ", (v_int_real_int_9 == v_int_real_int_62), " ", "v_int_real_int_8", " ", (v_int_real_int_8 == v_int_real_int_63), " ", "v_int_real_int_4.2", " ", v_int_real_int_4.2, " ", "v_array_30[0]", " ", v_array_30[0], " ", "v_array_29[1]", " ", v_array_29[1], " ", "v_array_23[3]", " ", v_array_23[3], " ", "v_array_24[0]", " ", v_array_24[0], " ", "v_DT_1_1_56", " ", v_DT_1_1_56, " ", "v_int_real_int_10.2", " ", v_int_real_int_10.2, " ", "v_array_35[1]", " ", v_array_35[1], " ", "v_DT_1_1_55", " ", v_DT_1_1_55, " ", "v_int_real_int_10.1", " ", (v_int_real_int_10.1 == 29.46), " ", "v_DT_1_1_54", " ", v_DT_1_1_54, " ", "v_int_real_int_10.0", " ", v_int_real_int_10.0, " ", "v_array_18[3]", " ", v_array_18[3], " ", "v_DT_1_1_53", " ", v_DT_1_1_53, " ", "v_DT_1_1_59", " ", v_DT_1_1_59, " ", "v_DT_1_1_58", " ", v_DT_1_1_58, " ", "v_array_6[1]", " ", v_array_6[1], " ", "v_DT_1_1_57", " ", v_DT_1_1_57, " ", "v_array_6[3]", " ", v_array_6[3], " ", "v_int_int_real_int_16.1", " ", (v_int_int_real_int_16.1 == v_int_real_int_64), " ", "v_array_13[1]", " ", v_array_13[1], " ", "v_array_18[2]", " ", v_array_18[2], " ", "v_int_int_real_int_2.0", " ", v_int_int_real_int_2.0, " ", "v_int_int_real_int_2.1", " ", (v_int_int_real_int_2.1 == v_int_real_int_65), " ", "v_seq_9", " ", v_seq_9, " ", "v_int_real_int_3.0", " ", v_int_real_int_3.0, " ", "v_int_real_int_3.1", " ", (v_int_real_int_3.1 == -26.01), " ", "v_seq_5", " ", (v_seq_5 == [{-25, 10, 12}, {}, {7}, {}]), " ", "v_array_29[2]", " ", v_array_29[2], " ", "v_int_real_int_3.2", " ", v_int_real_int_3.2, " ", "v_seq_4", " ", (v_seq_4 == [{0, 17, 18, 26}, {0, -2, 19, -14}, {7, -9, 12}]), " ", "v_seq_3", " ", (v_seq_3 == []), " ", "v_array_24[1]", " ", v_array_24[1], " ", "v_array_30[1]", " ", v_array_30[1], " ", "v_array_35[2]", " ", v_array_35[2], " ", "v_int_int_real_int_16.0", " ", v_int_int_real_int_16.0, "\n";
						return ;
					}
				}
				return ;
			}
			
		}
		
		match (match 'Q' {
			case _ => v_char_4
		}) {
			case _ => {
				var v_map_46: map<char, bool> := (if (false) then (map['B' := true, 'h' := true, 'y' := true, 'U' := true]) else (map['v' := true]));
				var v_map_44: map<char, char> := map['A' := 'n', 'Q' := 'e', 'A' := 'm', 'E' := 'c', 'A' := 'h'];
				var v_char_63: char := 'V';
				var v_char_65: char := (if ((v_char_63 in v_map_44)) then (v_map_44[v_char_63]) else ('H'));
				var v_map_45: map<char, bool> := map['p' := true, 'z' := true];
				var v_char_64: char := 'f';
				var v_map_47: map<char, bool> := (match 'Z' {
					case _ => map['C' := false, 'E' := false, 'y' := false, 'G' := true]
				});
				var v_char_66: char := (if (true) then ('R') else ('N'));
				if (if ((if ((v_char_65 in v_map_46)) then (v_map_46[v_char_65]) else ((if ((v_char_64 in v_map_45)) then (v_map_45[v_char_64]) else (true))))) then ((if ((v_char_66 in v_map_47)) then (v_map_47[v_char_66]) else ((if (false) then (true) else (true))))) else ((('k' !in map['E' := 'Q']) && v_bool_2))) {
					return ;
				} else {
					v_char_4, v_char_63 := (if ((match 'X' {
						case _ => (match 'k' {
							case _ => false
						})
					})) then ((if ((10 != 13)) then (v_char_4) else ((match 'c' {
						case _ => 'Z'
					})))) else (v_char_1)), v_char_66;
					var v_map_48: map<char, int> := map['U' := 25, 'm' := -26, 'K' := 1, 'x' := 26, 'P' := 1];
					var v_char_67: char := 'J';
					var v_seq_72: seq<int> := [25, 0];
					var v_seq_73: seq<int> := v_seq_72;
					var v_int_100: int := 13;
					var v_int_101: int := safe_index_seq(v_seq_73, v_int_100);
					var v_int_102: int := v_int_101;
					var v_seq_74: seq<int> := (if ((|v_seq_72| > 0)) then (v_seq_72[v_int_102 := 17]) else (v_seq_72));
					var v_map_49: map<char, int> := map['r' := 1, 'a' := 4, 'i' := 2, 'L' := 28, 'M' := 9];
					var v_char_68: char := 'r';
					var v_int_103: int := (if ((v_char_68 in v_map_49)) then (v_map_49[v_char_68]) else (-8));
					var v_int_98: int := ((if ((if (false) then (true) else (false))) then (v_array_27[1]) else ((if ((v_char_67 in v_map_48)) then (v_map_48[v_char_67]) else (13)))) % (if ((|v_seq_74| > 0)) then (v_seq_74[v_int_103]) else (v_int_real_int_1.0)));
					var v_seq_75: seq<bool> := [false, true];
					var v_seq_77: seq<bool> := (if ((|v_seq_75| > 0)) then (v_seq_75[-29..10]) else (v_seq_75));
					var v_seq_76: seq<int> := [8, 12];
					var v_int_104: int := 17;
					var v_int_105: int := (if ((|v_seq_76| > 0)) then (v_seq_76[v_int_104]) else (19));
					var v_int_99: int := (if ((if ((|v_seq_77| > 0)) then (v_seq_77[v_int_105]) else (v_real_bool_18.1))) then ((if ((if (true) then (false) else (true))) then (v_array_17[2]) else (v_array_9[0]))) else (v_array_29[1]));
					while (v_int_98 < v_int_99) 
						decreases v_int_99 - v_int_98;
						invariant (v_int_98 <= v_int_99);
					{
						v_int_98 := (v_int_98 + 1);
						return ;
					}
					var v_seq_78: seq<bool> := [false, false];
					var v_seq_79: seq<bool> := v_seq_78;
					var v_int_106: int := 2;
					var v_int_107: int := safe_index_seq(v_seq_79, v_int_106);
					var v_int_108: int := v_int_107;
					var v_seq_81: seq<bool> := (if ((|v_seq_78| > 0)) then (v_seq_78[v_int_108 := false]) else (v_seq_78));
					var v_seq_80: seq<int> := [];
					var v_int_109: int := 6;
					var v_int_110: int := (if ((|v_seq_80| > 0)) then (v_seq_80[v_int_109]) else (3));
					var v_map_50: map<char, char> := map['Y' := 'X', 'F' := 'o'];
					var v_char_69: char := 'w';
					var v_map_51: map<char, char> := map['d' := 'M', 'y' := 'q', 'r' := 'B', 'p' := 'K', 'U' := 'x'];
					var v_char_70: char := 'Z';
					v_char_64 := (if ((if ((|v_seq_81| > 0)) then (v_seq_81[v_int_110]) else (v_bool_2))) then ((if ((if (true) then (true) else (true))) then ((if (true) then ('N') else ('Z'))) else ((if ((v_char_69 in v_map_50)) then (v_map_50[v_char_69]) else ('N'))))) else ((match 'U' {
						case _ => (if ((v_char_70 in v_map_51)) then (v_map_51[v_char_70]) else ('a'))
					})));
					assert true;
					expect true;
				}
				var v_map_52: map<char, bool> := map['l' := false, 'E' := true, 'C' := true, 'm' := false, 'y' := false];
				var v_char_71: char := 'w';
				if (match 'F' {
					case _ => v_bool_3
				}) {
					
				}
				var v_seq_82: seq<char> := ['G'];
				var v_seq_83: seq<char> := (if ((|v_seq_82| > 0)) then (v_seq_82[20..17]) else (v_seq_82));
				var v_seq_84: seq<char> := v_seq_83;
				var v_int_111: int := (25 / 8);
				var v_int_112: int := safe_index_seq(v_seq_84, v_int_111);
				var v_int_113: int := v_int_112;
				var v_seq_85: seq<char> := (if ((|v_seq_83| > 0)) then (v_seq_83[v_int_113 := (match 'B' {
					case _ => 'D'
				})]) else (v_seq_83));
				var v_map_54: map<char, int> := map['C' := 4, 'S' := 11]['V' := 28];
				var v_map_53: map<char, char> := map['o' := 'J', 'j' := 'j', 'e' := 'H', 'T' := 'Q'];
				var v_char_72: char := 'G';
				var v_char_73: char := (if ((v_char_72 in v_map_53)) then (v_map_53[v_char_72]) else ('x'));
				var v_int_114: int := (if ((v_char_73 in v_map_54)) then (v_map_54[v_char_73]) else ((match 'k' {
					case _ => 21
				})));
				var v_seq_86: seq<char> := [];
				var v_int_115: int := 12;
				var v_seq_87: seq<char> := [];
				var v_int_116: int := 6;
				match (if ((|v_seq_85| > 0)) then (v_seq_85[v_int_114]) else ((match 'V' {
					case _ => (if ((|v_seq_87| > 0)) then (v_seq_87[v_int_116]) else ('m'))
				}))) {
					case _ => {
						var v_map_67: map<char, map<char, char>> := (if (false) then (map['P' := map['w' := 'g', 'K' := 'h', 'd' := 'y', 'Q' := 'H'], 'U' := map['Q' := 'I', 'P' := 'm', 'R' := 'l', 'B' := 'f']]) else (map['I' := map['D' := 'z', 'L' := 'G', 'J' := 'B'], 'T' := map['y' := 'y', 'M' := 'i', 'T' := 'O']]));
						var v_char_86: char := (match 'V' {
							case _ => 'T'
						});
						var v_map_68: map<char, char> := (if ((v_char_86 in v_map_67)) then (v_map_67[v_char_86]) else (map['r' := 'R', 'j' := 'M', 'j' := 'r', 'u' := 'U', 'Q' := 'i']['R' := 'O']));
						var v_char_87: char := v_char_1;
						var v_seq_101: seq<char> := ['t', 't', 'r'];
						var v_seq_102: seq<char> := (if ((|v_seq_101| > 0)) then (v_seq_101[21..3]) else (v_seq_101));
						var v_int_132: int := (if (false) then (5) else (5));
						var v_map_69: map<char, char> := map['y' := 'a', 'e' := 'U', 'w' := 'k', 'i' := 'D', 'E' := 'w']['R' := 'J'][(if (true) then ('s') else ('V')) := (if (true) then ('h') else ('K'))];
						var v_char_88: char := (if ((match 'c' {
							case _ => true
						})) then (v_char_1) else ((match 'c' {
							case _ => 'b'
						})));
						var v_seq_103: seq<char> := ['L'];
						var v_seq_104: seq<char> := (if ((|v_seq_103| > 0)) then (v_seq_103[8..29]) else (v_seq_103));
						var v_int_133: int := (if (true) then (2) else (7));
						v_char_66, v_char_86, v_char_87, v_char_63 := (if ((v_char_87 in v_map_68)) then (v_map_68[v_char_87]) else ((if ((|v_seq_102| > 0)) then (v_seq_102[v_int_132]) else (v_char_63)))), v_char_73, (if ((v_char_88 in v_map_69)) then (v_map_69[v_char_88]) else ((if ((|v_seq_104| > 0)) then (v_seq_104[v_int_133]) else ((if (true) then ('U') else ('l')))))), v_char_73;
						var v_seq_105: seq<bool> := [true, false, true, false];
						var v_seq_106: seq<bool> := v_seq_105;
						var v_int_134: int := 0;
						var v_int_135: int := safe_index_seq(v_seq_106, v_int_134);
						var v_int_136: int := v_int_135;
						var v_seq_108: seq<bool> := (if ((|v_seq_105| > 0)) then (v_seq_105[v_int_136 := false]) else (v_seq_105));
						var v_seq_107: seq<int> := [27];
						var v_int_137: int := 22;
						var v_int_138: int := (if ((|v_seq_107| > 0)) then (v_seq_107[v_int_137]) else (0));
						var v_seq_109: seq<bool> := [false, false];
						var v_int_139: int := 8;
						var v_seq_110: seq<char> := ['m'];
						var v_int_140: int := 6;
						var v_seq_111: seq<char> := [];
						var v_int_141: int := 15;
						var v_map_70: map<char, char> := map['A' := 'K', 'I' := 'Y', 'R' := 'N', 'l' := 'C', 'e' := 'M'];
						var v_char_89: char := 'P';
						v_char_73 := (if ((if ((|v_seq_108| > 0)) then (v_seq_108[v_int_138]) else ((if ((|v_seq_109| > 0)) then (v_seq_109[v_int_139]) else (false))))) then (v_char_1) else ((match 'L' {
							case _ => (if ((v_char_89 in v_map_70)) then (v_map_70[v_char_89]) else ('k'))
						})));
						var v_seq_112: seq<int> := [];
						var v_seq_113: seq<int> := v_seq_112;
						var v_int_144: int := 16;
						var v_int_145: int := safe_index_seq(v_seq_113, v_int_144);
						var v_int_146: int := v_int_145;
						var v_seq_114: seq<int> := [17, 28, 12];
						var v_seq_115: seq<int> := v_seq_114;
						var v_int_147: int := 8;
						var v_int_148: int := safe_index_seq(v_seq_115, v_int_147);
						var v_int_149: int := v_int_148;
						var v_seq_116: seq<int> := (if ((if (true) then (false) else (false))) then ((if ((|v_seq_112| > 0)) then (v_seq_112[v_int_146 := 28]) else (v_seq_112))) else ((if ((|v_seq_114| > 0)) then (v_seq_114[v_int_149 := 14]) else (v_seq_114))));
						var v_int_150: int := v_int_int_real_int_9.0;
						var v_seq_117: seq<int> := [8, 10];
						var v_int_151: int := 16;
						var v_int_142: int := (if ((|v_seq_116| > 0)) then (v_seq_116[v_int_150]) else ((match 'C' {
							case _ => v_int_int_real_int_4.0
						})));
						var v_seq_118: seq<int> := [0, 3, 29, 9];
						var v_seq_119: seq<int> := (if ((|v_seq_118| > 0)) then (v_seq_118[14..0]) else (v_seq_118));
						var v_int_152: int := (match 'v' {
							case _ => 17
						});
						var v_seq_120: seq<int> := [7, 12];
						var v_int_153: int := 22;
						var v_map_71: map<char, int> := map['Y' := 27, 'o' := 9, 'd' := 1, 'v' := 5, 'S' := 10];
						var v_char_90: char := 'G';
						var v_seq_121: seq<int> := [3, 22, -6];
						var v_int_154: int := 29;
						var v_int_143: int := ((if ((|v_seq_119| > 0)) then (v_seq_119[v_int_152]) else ((if ((|v_seq_120| > 0)) then (v_seq_120[v_int_153]) else (0)))) + (match 'H' {
							case _ => |{'F', 'G'}|
						}));
						while (v_int_142 < v_int_143) 
							decreases v_int_143 - v_int_142;
							invariant (v_int_142 <= v_int_143);
						{
							v_int_142 := (v_int_142 + 1);
							return ;
						}
						return ;
					}
					
				}
				
			}
			
		}
		
	}
	var v_map_74: map<char, bool> := map['q' := true, 'y' := true, 'D' := true, 'H' := true, 'n' := true]['S' := true];
	var v_map_72: map<char, char> := map['v' := 'r', 'L' := 'U', 'j' := 'F', 'a' := 'U', 'i' := 'F'];
	var v_char_91: char := 'Y';
	var v_char_93: char := (if ((v_char_91 in v_map_72)) then (v_map_72[v_char_91]) else ('U'));
	var v_map_73: map<char, bool> := map['y' := true, 'Z' := false, 'y' := false, 'P' := true, 'I' := true];
	var v_char_92: char := 't';
	var v_seq_122: seq<bool> := [];
	var v_seq_123: seq<bool> := (if ((|v_seq_122| > 0)) then (v_seq_122[10..-12]) else (v_seq_122));
	var v_int_155: int := (if (false) then (23) else (20));
	var v_seq_124: seq<bool> := [false];
	var v_int_156: int := 27;
	if (match 'G' {
		case _ => (if ((|v_seq_123| > 0)) then (v_seq_123[v_int_155]) else ((if ((|v_seq_124| > 0)) then (v_seq_124[v_int_156]) else (false))))
	}) {
		var v_map_75: map<char, int> := map['y' := 4, 'h' := 16, 'S' := 16, 'U' := 27];
		var v_char_94: char := 'p';
		var v_map_76: map<char, int> := (if (false) then (map['K' := 14, 't' := 11, 'P' := 26, 's' := -29, 'p' := -24]) else (map['n' := 14, 'I' := 24, 'a' := 26]))[(if (true) then ('h') else ('Z')) := (if ((v_char_94 in v_map_75)) then (v_map_75[v_char_94]) else (18))];
		var v_seq_125: seq<char> := [];
		var v_seq_126: seq<char> := v_seq_125;
		var v_int_159: int := 2;
		var v_int_160: int := safe_index_seq(v_seq_126, v_int_159);
		var v_int_161: int := v_int_160;
		var v_seq_127: seq<char> := (if ((|v_seq_125| > 0)) then (v_seq_125[v_int_161 := 'Y']) else (v_seq_125));
		var v_int_162: int := (18.80).Floor;
		var v_char_95: char := (if ((|v_seq_127| > 0)) then (v_seq_127[v_int_162]) else (v_char_94));
		var v_seq_128: seq<int> := [23];
		var v_seq_129: seq<int> := (if ((|v_seq_128| > 0)) then (v_seq_128[10..-8]) else (v_seq_128));
		var v_int_163: int := (-8 + 28);
		var v_seq_130: seq<int> := [23, 9, 8, -8];
		var v_int_164: int := 10;
		var v_int_157: int := (if ((v_char_95 in v_map_76)) then (v_map_76[v_char_95]) else ((if ((|v_seq_129| > 0)) then (v_seq_129[v_int_163]) else ((if ((|v_seq_130| > 0)) then (v_seq_130[v_int_164]) else (-5))))));
		var v_seq_131: seq<int> := [0];
		var v_seq_132: seq<int> := (if ((|v_seq_131| > 0)) then (v_seq_131[7..12]) else (v_seq_131));
		var v_seq_133: seq<int> := v_seq_132;
		var v_int_165: int := v_int_157;
		var v_int_166: int := safe_index_seq(v_seq_133, v_int_165);
		var v_int_167: int := v_int_166;
		var v_seq_135: seq<int> := (if ((|v_seq_132| > 0)) then (v_seq_132[v_int_167 := (4 - 11)]) else (v_seq_132));
		var v_seq_134: seq<int> := [11, 25, 15];
		var v_int_168: int := 1;
		var v_map_77: map<char, int> := map['r' := 2, 'k' := 28];
		var v_char_96: char := 'Z';
		var v_int_169: int := ((if ((|v_seq_134| > 0)) then (v_seq_134[v_int_168]) else (-6)) * (if ((v_char_96 in v_map_77)) then (v_map_77[v_char_96]) else (11)));
		var v_seq_136: seq<int> := [1];
		var v_seq_138: seq<int> := (if ((|v_seq_136| > 0)) then (v_seq_136[28..0]) else (v_seq_136));
		var v_seq_137: seq<int> := [19, 13, 16, 17];
		var v_int_170: int := 5;
		var v_int_171: int := (if ((|v_seq_137| > 0)) then (v_seq_137[v_int_170]) else (15));
		var v_int_158: int := (if ((|v_seq_135| > 0)) then (v_seq_135[v_int_169]) else ((if ((|v_seq_138| > 0)) then (v_seq_138[v_int_171]) else (v_int_164))));
		while (v_int_157 < v_int_158) 
			decreases v_int_158 - v_int_157;
			invariant (v_int_157 <= v_int_158);
		{
			v_int_157 := (v_int_157 + 1);
		}
		return ;
	} else {
		var v_seq_139: seq<bool> := [false, true];
		var v_int_172: int := 9;
		var v_map_79: map<char, char> := map['m' := 'x']['Y' := 'E'];
		var v_map_78: map<char, char> := map['P' := 'z', 't' := 'K', 'b' := 'm', 'q' := 'K'];
		var v_char_97: char := 'M';
		var v_char_98: char := (if ((v_char_97 in v_map_78)) then (v_map_78[v_char_97]) else ('O'));
		var v_seq_140: seq<char> := ['J'];
		var v_int_173: int := 24;
		var v_map_80: map<char, char> := map['D' := 'J', 'f' := 't', 'T' := 'g']['P' := 'R'];
		var v_char_99: char := (match 'u' {
			case _ => 't'
		});
		var v_map_81: map<char, char> := map['m' := 'q', 'v' := 'Z', 'W' := 'R', 'l' := 'd'];
		var v_char_100: char := 'l';
		var v_map_82: map<char, char> := map['b' := 'e', 'x' := 'h', 'h' := 'Z', 'w' := 'j', 'x' := 'j']['v' := 't'][(if ((v_char_100 in v_map_81)) then (v_map_81[v_char_100]) else ('M')) := (match 'G' {
			case _ => 'f'
		})];
		var v_char_101: char := (if ((match 'G' {
			case _ => true
		})) then ((if (true) then ('a') else ('E'))) else (v_char_100));
		var v_seq_141: seq<char> := ['O', 'u', 'd', 'w'];
		var v_int_174: int := 27;
		var v_seq_142: seq<char> := ['T'];
		var v_int_175: int := 5;
		var v_seq_143: seq<char> := ['i', 'z'];
		var v_seq_144: seq<char> := (if ((|v_seq_143| > 0)) then (v_seq_143[12..4]) else (v_seq_143));
		var v_seq_145: seq<char> := v_seq_144;
		var v_int_176: int := (match 'E' {
			case _ => -15
		});
		var v_int_177: int := safe_index_seq(v_seq_145, v_int_176);
		var v_int_178: int := v_int_177;
		var v_seq_146: seq<char> := (if ((|v_seq_144| > 0)) then (v_seq_144[v_int_178 := v_char_101]) else (v_seq_144));
		var v_int_179: int := v_int_172;
		var v_map_83: map<char, char> := map['u' := 'W', 'F' := 'U', 'A' := 'Q', 'B' := 'K', 'h' := 'W'];
		var v_char_102: char := 'e';
		var v_seq_147: seq<char> := ['w', 'S', 'A'];
		var v_int_180: int := 14;
		var v_char_103: char, v_char_104: char, v_char_105: char, v_char_106: char, v_char_107: char := (if (((if ((|v_seq_139| > 0)) then (v_seq_139[v_int_172]) else (true)) <==> (match 'r' {
			case _ => false
		}))) then ((if ((v_char_98 in v_map_79)) then (v_map_79[v_char_98]) else (v_char_97))) else ((match 'N' {
			case _ => v_char_98
		}))), (match 'F' {
			case _ => v_char_98
		}), v_char_98, (if ((v_char_101 in v_map_82)) then (v_map_82[v_char_101]) else ((match 'h' {
			case _ => (if ((|v_seq_142| > 0)) then (v_seq_142[v_int_175]) else ('U'))
		}))), (if ((|v_seq_146| > 0)) then (v_seq_146[v_int_179]) else ((match 'A' {
			case _ => (if ((|v_seq_147| > 0)) then (v_seq_147[v_int_180]) else ('r'))
		})));
	}
	var v_map_84: map<char, int> := map['R' := 29, 'y' := 8, 'W' := 25]['m' := 5];
	var v_seq_148: seq<char> := ['M'];
	var v_int_182: int := 8;
	var v_char_108: char := (if ((|v_seq_148| > 0)) then (v_seq_148[v_int_182]) else ('Z'));
	var v_map_85: map<char, int> := map['Y' := -20, 'u' := 25, 'g' := -11]['C' := 21];
	var v_char_109: char := v_char_108;
	var v_int_213: int, v_int_214: int := ((if ((v_char_108 in v_map_84)) then (v_map_84[v_char_108]) else ((if (true) then (6) else (26)))) + (if ((v_char_109 in v_map_85)) then (v_map_85[v_char_109]) else (v_int_182))), v_int_182;
	for v_int_181 := v_int_213 to v_int_214 
		invariant (v_int_214 - v_int_181 >= 0)
	{
		var v_seq_149: seq<bool> := [true, true];
		var v_seq_150: seq<bool> := (if ((|v_seq_149| > 0)) then (v_seq_149[3..13]) else (v_seq_149));
		var v_int_183: int := (3 / 9);
		var v_map_86: map<char, bool> := map['U' := true];
		var v_char_110: char := 'X';
		var v_map_87: map<char, char> := map['j' := 's', 'B' := 'S'];
		var v_char_111: char := 'K';
		var v_seq_151: seq<char> := [];
		var v_seq_152: seq<char> := v_seq_151;
		var v_int_184: int := 15;
		var v_int_185: int := safe_index_seq(v_seq_152, v_int_184);
		var v_int_186: int := v_int_185;
		var v_seq_154: seq<char> := (if ((|v_seq_151| > 0)) then (v_seq_151[v_int_186 := 'P']) else (v_seq_151));
		var v_seq_153: seq<int> := [22, 4, 14, 10];
		var v_int_187: int := -2;
		var v_int_188: int := (if ((|v_seq_153| > 0)) then (v_seq_153[v_int_187]) else (15));
		var v_map_88: map<char, char> := map['q' := 'R', 'R' := 'R', 'f' := 'b', 'T' := 'L'];
		var v_char_112: char := 'V';
		var v_seq_155: seq<char> := [];
		var v_seq_156: seq<char> := v_seq_155;
		var v_int_189: int := -16;
		var v_int_190: int := safe_index_seq(v_seq_156, v_int_189);
		var v_int_191: int := v_int_190;
		var v_seq_157: seq<char> := (if ((|v_seq_155| > 0)) then (v_seq_155[v_int_191 := 'q']) else (v_seq_155));
		var v_int_192: int := (if (true) then (6) else (28));
		var v_map_89: map<char, char> := map['d' := 'm']['X' := 'O'];
		var v_char_113: char := (match 'K' {
			case _ => 'Y'
		});
		var v_seq_158: seq<char> := [];
		var v_seq_159: seq<char> := v_seq_158;
		var v_int_193: int := 17;
		var v_int_194: int := safe_index_seq(v_seq_159, v_int_193);
		var v_int_195: int := v_int_194;
		var v_seq_160: seq<char> := (if ((|v_seq_158| > 0)) then (v_seq_158[v_int_195 := 'D']) else (v_seq_158));
		var v_map_90: map<char, int> := map['f' := 29];
		var v_char_114: char := 'j';
		var v_seq_161: seq<char> := (if ((|v_seq_160| > 0)) then (v_seq_160[|map['q' := 'R', 'u' := 'J', 'L' := 'V']|..(if ((v_char_114 in v_map_90)) then (v_map_90[v_char_114]) else (10))]) else (v_seq_160));
		var v_int_196: int := v_int_193;
		var v_map_91: map<char, char> := map['L' := 'A', 'q' := 'H'];
		var v_char_115: char := 'L';
		var v_map_92: map<char, char> := map['a' := 'Y', 'V' := 'f', 'x' := 'Z', 'z' := 's', 'W' := 'X'];
		var v_char_116: char := 'j';
		var v_seq_162: seq<char> := [];
		var v_seq_163: seq<char> := v_seq_162;
		var v_int_197: int := 7;
		var v_int_198: int := safe_index_seq(v_seq_163, v_int_197);
		var v_int_199: int := v_int_198;
		var v_seq_164: seq<char> := (if ((|v_seq_162| > 0)) then (v_seq_162[v_int_199 := 'i']) else (v_seq_162));
		var v_seq_166: seq<char> := (if ((|v_seq_164| > 0)) then (v_seq_164[(0 % 9)..0]) else (v_seq_164));
		var v_map_93: map<char, int> := map['P' := 4, 'k' := 20, 'Q' := 22, 'D' := 10, 'e' := 9]['J' := 0];
		var v_seq_165: seq<char> := [];
		var v_int_200: int := -18;
		var v_char_117: char := (if ((|v_seq_165| > 0)) then (v_seq_165[v_int_200]) else ('M'));
		var v_int_201: int := (if ((v_char_117 in v_map_93)) then (v_map_93[v_char_117]) else (v_int_196));
		v_char_109, v_char_108, v_char_112, v_char_117 := (if ((if ((|v_seq_150| > 0)) then (v_seq_150[v_int_183]) else ((if ((v_char_110 in v_map_86)) then (v_map_86[v_char_110]) else (false))))) then ((match 'K' {
			case _ => (match 'e' {
				case _ => 'y'
			})
		})) else ((if ((|v_seq_154| > 0)) then (v_seq_154[v_int_188]) else ((if ((v_char_112 in v_map_88)) then (v_map_88[v_char_112]) else ('F')))))), (match 'v' {
			case _ => (if ((v_char_113 in v_map_89)) then (v_map_89[v_char_113]) else (v_char_108))
		}), (if ((|v_seq_161| > 0)) then (v_seq_161[v_int_196]) else ((match 'H' {
			case _ => (if (true) then ('T') else ('E'))
		}))), (if ((|v_seq_166| > 0)) then (v_seq_166[v_int_201]) else ((match 'n' {
			case _ => v_char_112
		})));
		var v_map_95: map<char, bool> := map['H' := true, 'l' := true, 'R' := false]['a' := true][v_char_108 := (if (true) then (true) else (true))];
		var v_seq_167: seq<char> := ['q'];
		var v_int_202: int := 28;
		var v_char_119: char := (if ((if (false) then (false) else (false))) then ((if ((|v_seq_167| > 0)) then (v_seq_167[v_int_202]) else ('n'))) else ((match 'a' {
			case _ => 'w'
		})));
		var v_map_94: map<char, bool> := map['y' := true, 'k' := true];
		var v_char_118: char := 'L';
		if (if ((v_char_119 in v_map_95)) then (v_map_95[v_char_119]) else ((match 'h' {
			case _ => (match 'q' {
				case _ => true
			})
		}))) {
			
		} else {
			assert true;
			expect true;
		}
		var v_map_96: map<char, char> := map['F' := 'F', 'I' := 'M', 'm' := 'y', 'f' := 'b'];
		var v_char_120: char := 'I';
		var v_map_97: map<char, char> := map['T' := 'G', 'D' := 'F', 'K' := 'q', 'W' := 'f'];
		var v_char_121: char := 'U';
		var v_map_98: map<char, char> := map['h' := 'r', 'Q' := 'H', 'c' := 'L', 'Y' := 'U', 'h' := 'i']['z' := 'o'][(if ((v_char_120 in v_map_96)) then (v_map_96[v_char_120]) else ('S')) := (if ((v_char_121 in v_map_97)) then (v_map_97[v_char_121]) else ('w'))];
		var v_seq_168: seq<bool> := [true, false, false];
		var v_int_203: int := 17;
		var v_seq_169: seq<char> := ['X', 'q', 'I', 'D'];
		var v_int_204: int := 11;
		var v_seq_170: seq<char> := ['p', 'e'];
		var v_int_205: int := 15;
		var v_char_122: char := (if ((if ((|v_seq_168| > 0)) then (v_seq_168[v_int_203]) else (true))) then ((if ((|v_seq_169| > 0)) then (v_seq_169[v_int_204]) else ('o'))) else ((if ((|v_seq_170| > 0)) then (v_seq_170[v_int_205]) else ('c'))));
		var v_map_99: map<char, char> := map['T' := 'N', 'i' := 'K', 'O' := 'w', 'w' := 'M', 'N' := 'X'];
		var v_char_123: char := 'B';
		var v_map_101: map<char, char> := map['l' := 'u']['M' := 'P'][v_char_108 := (if ((v_char_123 in v_map_99)) then (v_map_99[v_char_123]) else ('w'))];
		var v_seq_171: seq<char> := [];
		var v_seq_172: seq<char> := v_seq_171;
		var v_int_206: int := 18;
		var v_int_207: int := safe_index_seq(v_seq_172, v_int_206);
		var v_int_208: int := v_int_207;
		var v_seq_174: seq<char> := (if ((|v_seq_171| > 0)) then (v_seq_171[v_int_208 := 'L']) else (v_seq_171));
		var v_seq_173: seq<int> := [25];
		var v_int_209: int := 23;
		var v_int_210: int := (if ((|v_seq_173| > 0)) then (v_seq_173[v_int_209]) else (23));
		var v_seq_175: seq<char> := ['E'];
		var v_int_211: int := 12;
		var v_char_125: char := (if ((|v_seq_174| > 0)) then (v_seq_174[v_int_210]) else ((if ((|v_seq_175| > 0)) then (v_seq_175[v_int_211]) else ('e'))));
		var v_map_100: map<char, bool> := map['v' := false];
		var v_char_124: char := 's';
		var v_seq_176: seq<char> := ['q'];
		var v_int_212: int := 7;
		v_char_123, v_char_117 := (if ((v_char_122 in v_map_98)) then (v_map_98[v_char_122]) else ((if ((if (false) then (true) else (false))) then ((if (false) then ('W') else ('u'))) else ((match 'G' {
			case _ => 'G'
		}))))), (if ((v_char_125 in v_map_101)) then (v_map_101[v_char_125]) else ((if ((if ((v_char_124 in v_map_100)) then (v_map_100[v_char_124]) else (true))) then ((if (false) then ('O') else ('x'))) else ((if ((|v_seq_176| > 0)) then (v_seq_176[v_int_212]) else ('D'))))));
	}
	return ;
}
