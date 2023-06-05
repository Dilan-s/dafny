// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1 = DT_1_1 | DT_1_3(DT_1_3_1: (real, real, int), DT_1_3_2: map<bool, real>)
datatype DT_2 = DT_2_1 | DT_2_2
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

method m_method_1(p_m_method_1_1: bool) returns (ret_1: bool)
	requires ((p_m_method_1_1 == true));
	ensures (((p_m_method_1_1 == true)) ==> ((ret_1 == true)));
{
	print "p_m_method_1_1", " ", p_m_method_1_1, "\n";
	return true;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_array_1: array<int> := new int[4] [16, 12, 8, 28];
	var v_array_2: array<int> := new int[3];
	v_array_2[0] := 11;
	v_array_2[1] := 5;
	v_array_2[2] := 11;
	var v_seq_3: seq<array<int>> := [v_array_1, v_array_2];
	var v_int_7: int := 21;
	var v_int_8: int := safe_index_seq(v_seq_3, v_int_7);
	if (10 !in {(12 % 18), v_int_8, v_array_1[3], v_array_1[0]}) {
		var v_map_1: map<bool, map<bool, bool>> := map[true := map[true := false, false := false], false := map[true := false, false := true]];
		var v_bool_1: bool := true;
		var v_bool_2: bool := m_method_1(v_bool_1);
		var v_bool_3: bool := v_bool_2;
		var v_seq_4: seq<map<bool, bool>> := [map[false := true, true := false]];
		var v_int_9: int := 29;
		var v_map_2: map<bool, bool> := (if ((v_bool_3 in v_map_1)) then (v_map_1[v_bool_3]) else ((if ((|v_seq_4| > 0)) then (v_seq_4[v_int_9]) else (map[false := true, false := true]))));
		var v_bool_4: bool := v_bool_3;
		var v_seq_5: seq<seq<bool>> := [[], [false, false], [false]];
		var v_int_10: int := 3;
		var v_seq_10: seq<seq<bool>> := v_seq_5;
		var v_int_20: int := v_int_10;
		var v_int_21: int := safe_index_seq(v_seq_10, v_int_20);
		v_int_10 := v_int_21;
		var v_seq_6: seq<bool> := ((if ((|v_seq_5| > 0)) then (v_seq_5[v_int_10]) else ([false])) + (match true {
			case false => [false, false]
			case _ => [true, false, false]
		}));
		var v_seq_12: seq<bool> := v_seq_6;
		var v_int_26: int := v_array_2[0];
		var v_int_27: int := 0;
		var v_int_28: int, v_int_29: int := safe_subsequence(v_seq_12, v_int_26, v_int_27);
		var v_int_24: int, v_int_25: int := v_int_28, v_int_29;
		var v_map_3: map<bool, seq<seq<bool>>> := map[false := [[false, false, false, false]], true := [[true]]];
		var v_bool_5: bool := true;
		var v_seq_7: seq<seq<bool>> := (if ((v_bool_5 in v_map_3)) then (v_map_3[v_bool_5]) else ([]));
		var v_int_11: int := 29;
		var v_seq_11: seq<seq<bool>> := v_seq_7;
		var v_int_22: int := v_int_11;
		var v_int_23: int := safe_index_seq(v_seq_11, v_int_22);
		v_int_11 := v_int_23;
		var v_seq_8: seq<bool> := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_11]) else (v_seq_6));
		var v_int_15: int := v_array_2[0];
		var v_int_12: int := 27;
		var v_int_13: int := 2;
		var v_int_14: int := safe_modulus(v_int_12, v_int_13);
		var v_int_16: int := v_int_14;
		var v_int_17: int := safe_division(v_int_15, v_int_16);
		var v_int_18: int := v_int_17;
		var v_seq_13: seq<bool> := v_seq_8;
		var v_int_30: int := v_int_18;
		var v_int_31: int := safe_index_seq(v_seq_13, v_int_30);
		v_int_18 := v_int_31;
		var v_seq_9: seq<DT_2> := [];
		var v_int_19: int := 5;
		var v_DT_2_2_1: DT_2 := DT_2_2;
		var v_DT_2_2_2: DT_2 := DT_2_2;
		var v_DT_2_2_3: DT_2 := DT_2_2;
		var v_DT_2_2_4: DT_2 := DT_2_2;
		var v_DT_2_2_5: DT_2 := DT_2_2;
		var v_DT_2_2_6: DT_2 := DT_2_2;
		var v_DT_2_2_7: DT_2 := DT_2_2;
		var v_DT_2_2_8: DT_2 := DT_2_2;
		var v_DT_2_2_9: DT_2 := DT_2_2;
		var v_map_4: map<multiset<char>, DT_2> := map[multiset({'i', 'y'}) := v_DT_2_2_8, multiset({}) := v_DT_2_2_9];
		var v_multiset_1: multiset<char> := multiset{'b'};
		var v_DT_2_2_10: DT_2 := DT_2_2;
		var v_DT_2_2_11: DT_2 := DT_2_2;
		var v_DT_2_2_12: DT_2 := DT_2_2;
		var v_DT_2_2_13: DT_2 := DT_2_2;
		var v_DT_2_2_14: DT_2 := DT_2_2;
		var v_DT_2_2_15: DT_2 := DT_2_2;
		v_bool_2, v_seq_6, v_bool_4, v_bool_1 := (if ((v_bool_4 in v_map_2)) then (v_map_2[v_bool_4]) else (v_bool_2)), (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_24..v_int_25]) else (v_seq_6)), (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_18]) else (((if ((|v_seq_9| > 0)) then (v_seq_9[v_int_19]) else (v_DT_2_2_1)) !in (multiset{v_DT_2_2_2, v_DT_2_2_3} - multiset{v_DT_2_2_4, v_DT_2_2_5, v_DT_2_2_6, v_DT_2_2_7})))), (if (v_bool_2) then (v_bool_2) else (((if ((v_multiset_1 in v_map_4)) then (v_map_4[v_multiset_1]) else (v_DT_2_2_10)) in ([v_DT_2_2_11, v_DT_2_2_12, v_DT_2_2_13, v_DT_2_2_14] + [v_DT_2_2_15]))));
		var v_DT_2_2_16: DT_2 := DT_2_2;
		var v_DT_2_2_17: DT_2 := DT_2_2;
		print "v_bool_1", " ", v_bool_1, " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_bool_5", " ", v_bool_5, " ", "v_bool_4", " ", v_bool_4, " ", "v_DT_2_2_11", " ", v_DT_2_2_11, " ", "v_DT_2_2_12", " ", v_DT_2_2_12, " ", "v_DT_2_2_13", " ", v_DT_2_2_13, " ", "v_DT_2_2_14", " ", v_DT_2_2_14, " ", "v_DT_2_2_15", " ", v_DT_2_2_15, " ", "v_int_9", " ", v_int_9, " ", "v_map_4", " ", (v_map_4 == map[multiset{'i', 'y'} := v_DT_2_2_16, multiset{} := v_DT_2_2_17]), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{'b'}), " ", "v_map_1", " ", (v_map_1 == map[false := map[false := true, true := false], true := map[false := false, true := false]]), " ", "v_map_3", " ", (v_map_3 == map[false := [[false, false, false, false]], true := [[true]]]), " ", "v_map_2", " ", (v_map_2 == map[false := false, true := false]), " ", "v_seq_9", " ", v_seq_9, " ", "v_DT_2_2_10", " ", v_DT_2_2_10, " ", "v_int_13", " ", v_int_13, " ", "v_seq_8", " ", v_seq_8, " ", "v_DT_2_2_3", " ", v_DT_2_2_3, " ", "v_seq_7", " ", v_seq_7, " ", "v_int_12", " ", v_int_12, " ", "v_DT_2_2_2", " ", v_DT_2_2_2, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_11", " ", v_int_11, " ", "v_DT_2_2_1", " ", v_DT_2_2_1, " ", "v_seq_5", " ", v_seq_5, " ", "v_int_10", " ", v_int_10, " ", "v_seq_4", " ", (v_seq_4 == [map[false := true, true := false]]), " ", "v_int_17", " ", v_int_17, " ", "v_DT_2_2_7", " ", v_DT_2_2_7, " ", "v_int_16", " ", v_int_16, " ", "v_DT_2_2_6", " ", v_DT_2_2_6, " ", "v_int_15", " ", v_int_15, " ", "v_DT_2_2_5", " ", v_DT_2_2_5, " ", "v_int_14", " ", v_int_14, " ", "v_DT_2_2_4", " ", v_DT_2_2_4, " ", "v_DT_2_2_9", " ", v_DT_2_2_9, " ", "v_DT_2_2_8", " ", v_DT_2_2_8, " ", "v_seq_3", " ", (v_seq_3 == [v_array_1, v_array_2]), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_int_8", " ", v_int_8, " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_int_7", " ", v_int_7, " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_array_1[3]", " ", v_array_1[3], " ", "v_array_2[2]", " ", v_array_2[2], "\n";
	} else {
		
	}
	print "v_seq_3", " ", (v_seq_3 == [v_array_1, v_array_2]), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_int_8", " ", v_int_8, " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_int_7", " ", v_int_7, " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_array_1[3]", " ", v_array_1[3], " ", "v_array_2[2]", " ", v_array_2[2], "\n";
	return ;
}
