// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
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

method m_method_3(p_m_method_3_1: bool, p_m_method_3_2: bool, p_m_method_3_3: bool) returns (ret_1: seq<bool>)
	requires ((p_m_method_3_1 == false) && (p_m_method_3_3 == true) && (p_m_method_3_2 == true));
	ensures (((p_m_method_3_1 == false) && (p_m_method_3_3 == true) && (p_m_method_3_2 == true)) ==> (|ret_1| == 0));
{
	print "p_m_method_3_2", " ", p_m_method_3_2, " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_3", " ", p_m_method_3_3, "\n";
	return [];
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

method m_method_2(p_m_method_2_1: bool, p_m_method_2_2: bool) returns (ret_1: bool)
	requires ((p_m_method_2_2 == true) && (p_m_method_2_1 == true)) || ((p_m_method_2_2 == true) && (p_m_method_2_1 == false));
	ensures (((p_m_method_2_2 == true) && (p_m_method_2_1 == true)) ==> ((ret_1 == true))) && (((p_m_method_2_2 == true) && (p_m_method_2_1 == false)) ==> ((ret_1 == true)));
{
	var v_int_8: int, v_int_9: int := 23, 8;
	for v_int_7 := v_int_8 downto v_int_9 
		invariant (v_int_7 - v_int_9 >= 0)
	{
		var v_map_1: map<bool, bool> := map[true := true, false := false];
		var v_bool_1: bool := true;
		print "v_bool_1", " ", v_bool_1, " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[false := false, true := true]), " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "p_m_method_2_2", " ", p_m_method_2_2, "\n";
		return (if ((v_bool_1 in v_map_1)) then (v_map_1[v_bool_1]) else (true));
	}
	return false;
}

method m_method_1(p_m_method_1_1: bool, p_m_method_1_2: bool, p_m_method_1_3: bool, p_m_method_1_4: bool) returns (ret_1: char)
	requires ((p_m_method_1_1 == true) && (p_m_method_1_3 == true) && (p_m_method_1_2 == true) && (p_m_method_1_4 == true));
	ensures (((p_m_method_1_1 == true) && (p_m_method_1_3 == true) && (p_m_method_1_2 == true) && (p_m_method_1_4 == true)) ==> ((ret_1 == 'j')));
{
	print "p_m_method_1_2", " ", p_m_method_1_2, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "p_m_method_1_4", " ", p_m_method_1_4, " ", "p_m_method_1_3", " ", p_m_method_1_3, "\n";
	return 'j';
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_bool_2: bool := false;
	var v_bool_3: bool := true;
	var v_bool_4: bool := m_method_2(v_bool_2, v_bool_3);
	var v_bool_5: bool := v_bool_4;
	var v_bool_6: bool := v_bool_3;
	var v_bool_7: bool := m_method_2(v_bool_5, v_bool_6);
	var v_bool_14: bool := v_bool_7;
	var v_bool_15: bool := v_bool_5;
	var v_int_10: int := 28;
	var v_int_11: int := 11;
	var v_int_12: int := safe_division(v_int_10, v_int_11);
	var v_int_13: int := 1;
	var v_int_14: int := 11;
	var v_int_15: int := safe_modulus(v_int_13, v_int_14);
	var v_bool_16: bool := (v_int_12 >= v_int_15);
	var v_bool_8: bool := false;
	var v_bool_9: bool := true;
	var v_bool_10: bool := true;
	var v_seq_3: seq<bool> := m_method_3(v_bool_8, v_bool_9, v_bool_10);
	var v_seq_4: seq<bool> := v_seq_3;
	var v_int_16: int := v_int_11;
	var v_bool_11: bool := true;
	var v_bool_12: bool := true;
	var v_bool_13: bool := m_method_2(v_bool_11, v_bool_12);
	var v_bool_17: bool := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_16]) else (v_bool_13));
	var v_char_1: char := m_method_1(v_bool_14, v_bool_15, v_bool_16, v_bool_17);
	var v_bool_18: bool := v_bool_7;
	var v_bool_19: bool := true;
	var v_bool_20: bool := m_method_2(v_bool_18, v_bool_19);
	v_char_1, v_bool_6, v_bool_11 := v_char_1, v_bool_5, !(v_bool_20);
	print "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_bool_9", " ", v_bool_9, " ", "v_bool_8", " ", v_bool_8, " ", "v_bool_5", " ", v_bool_5, " ", "v_bool_4", " ", v_bool_4, " ", "v_bool_7", " ", v_bool_7, " ", "v_bool_6", " ", v_bool_6, " ", "v_bool_20", " ", v_bool_20, " ", "v_char_1", " ", (v_char_1 == 'j'), " ", "v_bool_19", " ", v_bool_19, " ", "v_bool_17", " ", v_bool_17, " ", "v_bool_18", " ", v_bool_18, " ", "v_bool_15", " ", v_bool_15, " ", "v_bool_16", " ", v_bool_16, " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_seq_4", " ", v_seq_4, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_bool_13", " ", v_bool_13, " ", "v_bool_14", " ", v_bool_14, " ", "v_bool_11", " ", v_bool_11, " ", "v_bool_12", " ", v_bool_12, " ", "v_bool_10", " ", v_bool_10, "\n";
}
