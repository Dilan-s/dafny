// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" > "%t"
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

method m_method_3(p_m_method_3_1: int) returns (ret_1: real)
	requires ((p_m_method_3_1 == -19)) || ((p_m_method_3_1 == 7));
	ensures (((p_m_method_3_1 == -19)) ==> ((15.59 < ret_1 < 15.79))) && (((p_m_method_3_1 == 7)) ==> ((15.59 < ret_1 < 15.79)));
{
	print "p_m_method_3_1", " ", p_m_method_3_1, "\n";
	return (if (true) then (15.69) else (28.87));
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

method m_method_2(p_m_method_2_1: int, p_m_method_2_2: int) returns (ret_1: int)
	requires ((p_m_method_2_2 == 29) && (p_m_method_2_1 == 23));
	ensures (((p_m_method_2_2 == 29) && (p_m_method_2_1 == 23)) ==> ((ret_1 == 9)));
{
	print "p_m_method_2_1", " ", p_m_method_2_1, " ", "p_m_method_2_2", " ", p_m_method_2_2, "\n";
	return 9;
}

method m_method_1(p_m_method_1_1: real) returns (ret_1: int, ret_2: bool, ret_3: char, ret_4: real)
	requires ((15.59 < p_m_method_1_1 < 15.79));
	ensures (((15.59 < p_m_method_1_1 < 15.79)) ==> ((ret_1 == 29) && (ret_2 == false) && (ret_3 == 'v') && (15.59 < ret_4 < 15.79)));
{
	var v_map_1: map<real, char> := ((if (false) then (map[-10.12 := 'H']) else (map[-24.67 := 't', -25.97 := 'j', 10.81 := 'z'])) + map[21.85 := 'z', 20.55 := 'F', 27.12 := 'w', -9.12 := 'g']);
	var v_real_1: real := (if ((multiset{3, 10, 3} !! multiset{12})) then (18.70) else ((if (true) then (16.51) else (14.98))));
	var v_seq_3: seq<char> := (['v', 'K'] + []);
	var v_int_7: int := (15 * 19);
	var v_seq_4: seq<char> := v_seq_3;
	var v_int_15: int := v_int_7;
	var v_int_16: int := safe_index_seq(v_seq_4, v_int_15);
	v_int_7 := v_int_16;
	var v_map_2: map<int, real> := (map[6 := -8.41, 17 := -20.22, 25 := 22.88] - {-9})[(if (true) then (24) else (6)) := (if (false) then (-23.75) else (-9.24))];
	var v_int_8: int := 23;
	var v_int_9: int := 29;
	var v_int_10: int := m_method_2(v_int_8, v_int_9);
	var v_int_12: int := (v_int_7 * v_int_10);
	var v_int_11: int := (14 - 7);
	var v_real_2: real := m_method_3(v_int_11);
	print "v_int_12", " ", v_int_12, " ", "v_int_11", " ", v_int_11, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 15.69), " ", "v_int_10", " ", v_int_10, " ", "v_seq_3", " ", (v_seq_3 == ['v', 'K']), " ", "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_real_1", " ", (v_real_1 == 18.70), " ", "v_real_2", " ", (v_real_2 == 15.69), " ", "v_map_1", " ", (v_map_1 == map[27.12 := 'w', 10.81 := 'z', -24.67 := 't', 20.55 := 'F', -9.12 := 'g', 21.85 := 'z', -25.97 := 'j']), " ", "v_map_2", " ", (v_map_2 == map[17 := -20.22, 6 := -8.41, 24 := -9.24, 25 := 22.88]), "\n";
	return 29, false, (if ((v_real_1 in v_map_1)) then (v_map_1[v_real_1]) else ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else ('T')))), (if ((v_int_12 in v_map_2)) then (v_map_2[v_int_12]) else (v_real_2));
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_int_13: int := ((match -4 {
		case 5 => 12.31
		case _ => -18.43
	})).Floor;
	var v_real_3: real := m_method_3(v_int_13);
	var v_real_4: real := v_real_3;
	var v_int_14: int, v_bool_1: bool, v_char_1: char, v_real_5: real := m_method_1(v_real_4);
	v_int_13, v_bool_1, v_char_1, v_real_4 := v_int_14, v_bool_1, v_char_1, v_real_5;
	assert ((v_real_4 == 15.69) && (v_int_13 == 29) && (v_bool_1 == false) && (v_real_5 == 15.69) && (v_char_1 == 'v'));
	expect ((v_real_4 == 15.69) && (v_int_13 == 29) && (v_bool_1 == false) && (v_real_5 == 15.69) && (v_char_1 == 'v'));
	print "v_int_13", " ", v_int_13, " ", "v_bool_1", " ", v_bool_1, " ", "v_char_1", " ", (v_char_1 == 'v'), " ", "v_int_14", " ", v_int_14, " ", "v_real_3", " ", (v_real_3 == 15.69), " ", "v_real_4", " ", (v_real_4 == 15.69), " ", "v_real_5", " ", (v_real_5 == 15.69), "\n";
	return ;
}
