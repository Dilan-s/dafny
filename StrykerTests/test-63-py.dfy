// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1> = DT_1_1 | DT_1_2
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

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_int_7: int := 17;
	var v_seq_4: seq<set<real>> := [];
	var v_seq_3: seq<int> := [16, -17];
	var v_int_9: int := 18;
	var v_seq_12: seq<int> := v_seq_3;
	var v_int_25: int := v_int_9;
	var v_int_26: int := safe_index_seq(v_seq_12, v_int_25);
	v_int_9 := v_int_26;
	var v_int_10: int := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_9]) else (v_int_7));
	var v_int_11: int := safe_index_seq(v_seq_4, v_int_10);
	var v_int_8: int := v_int_11;
	while (v_int_7 < v_int_8) 
		decreases v_int_8 - v_int_7;
		invariant (v_int_7 <= v_int_8);
	{
		v_int_7 := (v_int_7 + 1);
		var v_seq_5: seq<bool> := ([true, false, true, true] + []);
		var v_int_12: int := (if (false) then (-9) else (-19));
		var v_seq_6: seq<bool> := [];
		var v_int_13: int := -7;
		if ((if ((|v_seq_5| > 0)) then (v_seq_5[v_int_12]) else ((1 <= 13))) ==> ((if ((|v_seq_6| > 0)) then (v_seq_6[v_int_13]) else (true)) == (15 >= 13))) {
			
		} else {
			break;
		}
		return ;
	}
	var v_DT_1_1_1: DT_1<char> := DT_1_1;
	var v_seq_7: seq<DT_1<char>> := [v_DT_1_1_1];
	var v_int_16: int := -9;
	var v_seq_13: seq<DT_1<char>> := v_seq_7;
	var v_int_27: int := v_int_16;
	var v_int_28: int := safe_index_seq(v_seq_13, v_int_27);
	v_int_16 := v_int_28;
	var v_DT_1_1_2: DT_1<char> := DT_1_1;
	var v_DT_1_1_3: DT_1<char> := DT_1_1;
	var v_map_1: map<char, DT_1<char>> := map['o' := v_DT_1_1_3];
	var v_char_1: char := 'c';
	var v_DT_1_1_4: DT_1<char> := DT_1_1;
	var v_int_17: int := 0;
	var v_int_18: int := 21;
	var v_int_19: int := safe_division(v_int_17, v_int_18);
	var v_map_3: map<DT_1<char>, int> := map[(if ((|v_seq_7| > 0)) then (v_seq_7[v_int_16]) else (v_DT_1_1_2)) := (if (false) then (-25) else (2))];
	var v_seq_8: seq<DT_1<char>> := [];
	var v_seq_9: seq<DT_1<char>> := v_seq_8;
	var v_int_20: int := -15;
	var v_int_21: int := safe_index_seq(v_seq_9, v_int_20);
	var v_int_22: int := v_int_21;
	var v_DT_1_1_5: DT_1<char> := DT_1_1;
	var v_seq_10: seq<DT_1<char>> := (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_22 := v_DT_1_1_5]) else (v_seq_8));
	var v_int_23: int := 23;
	var v_DT_1_1_6: DT_1<char> := DT_1_1;
	var v_DT_1_1_7: DT_1<char> := DT_1_1;
	var v_DT_1_1_8: DT_1<char> := DT_1_1;
	var v_DT_1_1_9: DT_1<char> := DT_1_1;
	var v_map_2: map<char, DT_1<char>> := map['t' := v_DT_1_1_6, 'V' := v_DT_1_1_7, 'X' := v_DT_1_1_8, 'U' := v_DT_1_1_9];
	var v_char_2: char := 'A';
	var v_DT_1_1_10: DT_1<char> := DT_1_1;
	var v_DT_1_1_11: DT_1<char> := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_23]) else ((if ((v_char_2 in v_map_2)) then (v_map_2[v_char_2]) else (v_DT_1_1_10))));
	var v_seq_11: seq<int> := ([29, -21, 28] + [5, 12, 19, 1]);
	var v_int_24: int := v_int_19;
	var v_int_14: int := (if ((v_DT_1_1_11 in v_map_3)) then (v_map_3[v_DT_1_1_11]) else ((if ((|v_seq_11| > 0)) then (v_seq_11[v_int_24]) else (v_int_24))));
	var v_int_15: int := v_int_18;
	while (v_int_14 < v_int_15) 
		decreases v_int_15 - v_int_14;
		invariant (v_int_14 <= v_int_15);
	{
		v_int_14 := (v_int_14 + 1);
		var v_DT_1_1_12: DT_1<char> := DT_1_1;
		var v_DT_1_1_13: DT_1<char> := DT_1_1;
		var v_DT_1_1_14: DT_1<char> := DT_1_1;
		var v_DT_1_1_15: DT_1<char> := DT_1_1;
		var v_DT_1_1_16: DT_1<char> := DT_1_1;
		var v_DT_1_1_17: DT_1<char> := DT_1_1;
		print "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_DT_1_1_9", " ", v_DT_1_1_9, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_int_24", " ", v_int_24, " ", "v_int_23", " ", v_int_23, " ", "v_int_22", " ", v_int_22, " ", "v_int_21", " ", v_int_21, " ", "v_seq_10", " ", v_seq_10, " ", "v_seq_11", " ", v_seq_11, " ", "v_int_9", " ", v_int_9, " ", "v_DT_1_1_11", " ", v_DT_1_1_11, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_DT_1_1_10", " ", v_DT_1_1_10, " ", "v_int_20", " ", v_int_20, " ", "v_char_1", " ", (v_char_1 == 'c'), " ", "v_char_2", " ", (v_char_2 == 'A'), " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map['o' := v_DT_1_1_12]), " ", "v_map_3", " ", (v_map_3 == map[v_DT_1_1_13 := 2]), " ", "v_seq_9", " ", v_seq_9, " ", "v_map_2", " ", (v_map_2 == map['t' := v_DT_1_1_14, 'U' := v_DT_1_1_15, 'V' := v_DT_1_1_16, 'X' := v_DT_1_1_17]), " ", "v_seq_8", " ", v_seq_8, " ", "v_seq_7", " ", v_seq_7, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_seq_4", " ", (v_seq_4 == []), " ", "v_int_17", " ", v_int_17, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, "\n";
		return ;
	}
}
