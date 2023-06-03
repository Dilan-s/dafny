// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1 = DT_1_1
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

method m_method_4(p_m_method_4_1: int, p_m_method_4_2: int, p_m_method_4_3: int) returns (ret_1: bool)
	requires ((p_m_method_4_2 == 4) && (p_m_method_4_1 == -10) && (p_m_method_4_3 == 2)) || ((p_m_method_4_2 == 11) && (p_m_method_4_1 == -21) && (p_m_method_4_3 == 9));
	ensures (((p_m_method_4_2 == 4) && (p_m_method_4_1 == -10) && (p_m_method_4_3 == 2)) ==> ((ret_1 == false))) && (((p_m_method_4_2 == 11) && (p_m_method_4_1 == -21) && (p_m_method_4_3 == 9)) ==> ((ret_1 == false)));
{
	print "p_m_method_4_1", " ", p_m_method_4_1, " ", "p_m_method_4_3", " ", p_m_method_4_3, " ", "p_m_method_4_2", " ", p_m_method_4_2, "\n";
	return false;
}

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: int) returns (ret_1: char)
	requires ((p_m_method_3_1 == -22) && (p_m_method_3_2 == -22));
	ensures (((p_m_method_3_1 == -22) && (p_m_method_3_2 == -22)) ==> ((ret_1 == 'P')));
{
	var v_seq_3: seq<int> := [0, 2, -28];
	var v_int_12: int := 1;
	var v_int_13: int := 26;
	var v_int_14: int := 5;
	var v_int_15: int := safe_modulus(v_int_13, v_int_14);
	var v_int_16: int, v_int_17: int := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_12]) else (-20)), v_int_15;
	for v_int_11 := v_int_16 downto v_int_17 
		invariant (v_int_11 - v_int_17 >= 0)
	{
		print "v_int_11", " ", v_int_11, " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "p_m_method_3_1", " ", p_m_method_3_1, "\n";
		break;
	}
	var v_int_18: int := 26;
	var v_int_19: int := 4;
	var v_int_20: int := safe_modulus(v_int_18, v_int_19);
	var v_seq_4: seq<int> := [1, 4, 26, 0];
	var v_int_21: int := -2;
	var v_int_22: int := safe_index_seq(v_seq_4, v_int_21);
	var v_int_23: int := 4;
	var v_int_24: int := 21;
	var v_int_25: int := safe_division(v_int_23, v_int_24);
	var v_array_2: array<int> := new int[3] [27, 13, 29];
	v_int_19, v_int_14, v_int_23, v_int_18, v_array_2[2] := v_int_20, v_int_22, v_int_25, v_int_18, v_array_2.Length;
	var v_map_3: map<int, char> := map[4 := 'K', 2 := 'z', 28 := 'r', 7 := 'Y'];
	var v_int_26: int := 3;
	print "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_map_3", " ", (v_map_3 == map[2 := 'z', 4 := 'K', 7 := 'Y', 28 := 'r']), " ", "v_int_13", " ", v_int_13, " ", "v_int_24", " ", v_int_24, " ", "v_int_12", " ", v_int_12, " ", "v_int_23", " ", v_int_23, " ", "v_int_22", " ", v_int_22, " ", "v_int_21", " ", v_int_21, " ", "v_int_17", " ", v_int_17, " ", "v_seq_4", " ", v_seq_4, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_26", " ", v_int_26, " ", "v_int_14", " ", v_int_14, " ", "v_int_25", " ", v_int_25, " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_array_2[1]", " ", v_array_2[1], " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "v_int_20", " ", v_int_20, " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "v_array_2[2]", " ", v_array_2[2], "\n";
	return (if ((v_int_26 in v_map_3)) then (v_map_3[v_int_26]) else ('P'));
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

method m_method_2(p_m_method_2_1: int, p_m_method_2_2: int) returns (ret_1: char)
	requires ((p_m_method_2_2 == -22) && (p_m_method_2_1 == 20));
	ensures (((p_m_method_2_2 == -22) && (p_m_method_2_1 == 20)) ==> ((ret_1 == 'P')));
{
	var v_int_27: int := p_m_method_2_2;
	var v_int_28: int := p_m_method_2_2;
	var v_char_1: char := m_method_3(v_int_27, v_int_28);
	print "v_char_1", " ", (v_char_1 == 'P'), " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "p_m_method_2_2", " ", p_m_method_2_2, "\n";
	return v_char_1;
}

method m_method_1(p_m_method_1_1: int, p_m_method_1_2: int) returns (ret_1: DT_1)
	requires ((p_m_method_1_1 == 21) && (p_m_method_1_2 == 23));
	ensures (((p_m_method_1_1 == 21) && (p_m_method_1_2 == 23)) ==> ((ret_1.DT_1_1? && ((ret_1 == DT_1_1)))));
{
	var v_DT_1_1_11: DT_1 := DT_1_1;
	print "p_m_method_1_2", " ", p_m_method_1_2, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_DT_1_1_11", " ", v_DT_1_1_11, "\n";
	return v_DT_1_1_11;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_DT_1_1_1: DT_1 := DT_1_1;
	var v_DT_1_1_2: DT_1 := DT_1_1;
	var v_DT_1_1_3: DT_1 := DT_1_1;
	var v_DT_1_1_4: DT_1 := DT_1_1;
	var v_DT_1_1_5: DT_1 := DT_1_1;
	var v_DT_1_1_6: DT_1 := DT_1_1;
	var v_DT_1_1_7: DT_1 := DT_1_1;
	var v_map_1: map<int, map<int, DT_1>> := map[5 := map[27 := v_DT_1_1_2], 14 := map[8 := v_DT_1_1_3, 6 := v_DT_1_1_4]];
	var v_int_7: int := -22;
	var v_DT_1_1_8: DT_1 := DT_1_1;
	var v_DT_1_1_9: DT_1 := DT_1_1;
	var v_DT_1_1_10: DT_1 := DT_1_1;
	var v_map_2: map<int, DT_1> := (if ((v_int_7 in v_map_1)) then (v_map_1[v_int_7]) else (map[2 := v_DT_1_1_8, 3 := v_DT_1_1_9, 28 := v_DT_1_1_10]));
	var v_int_10: int := v_int_7;
	var v_int_8: int := 21;
	var v_int_9: int := 23;
	var v_DT_1_1_12: DT_1 := m_method_1(v_int_8, v_int_9);
	var v_array_1: array<DT_1> := new DT_1[3] [v_DT_1_1_1, v_DT_1_1_1, (if ((v_int_10 in v_map_2)) then (v_map_2[v_int_10]) else (v_DT_1_1_12))];
	var v_int_29: int := -21;
	var v_int_30: int := 11;
	var v_int_31: int := 9;
	var v_bool_1: bool := m_method_4(v_int_29, v_int_30, v_int_31);
	var v_int_32: int := 15;
	var v_int_33: int := 3;
	var v_int_34: int := safe_modulus(v_int_32, v_int_33);
	var v_seq_5: seq<int> := [20, 17, 9, 17];
	var v_int_35: int := 6;
	var v_seq_18: seq<int> := v_seq_5;
	var v_int_61: int := v_int_35;
	var v_int_62: int := safe_index_seq(v_seq_18, v_int_61);
	v_int_35 := v_int_62;
	var v_int_36: int := (if (v_bool_1) then (v_int_34) else ((if ((|v_seq_5| > 0)) then (v_seq_5[v_int_35]) else (24))));
	var v_int_37: int := v_int_10;
	var v_char_2: char := m_method_2(v_int_36, v_int_37);
	var v_int_38: int := -10;
	var v_int_39: int := 4;
	var v_int_40: int := 2;
	var v_bool_2: bool := m_method_4(v_int_38, v_int_39, v_int_40);
	var v_array_3: array<DT_1>, v_char_3: char, v_bool_3: bool, v_char_4: char, v_int_41: int := v_array_1, v_char_2, v_bool_1, (if ((match 17 {
		case 26 => v_bool_2
		case _ => v_bool_1
	})) then (v_char_2) else ((match 15 {
		case 21 => v_char_2
		case 18 => (if (true) then ('x') else ('O'))
		case _ => v_char_2
	}))), v_int_8;
	match v_int_36 {
		case 25 => {
			var v_map_4: map<int, map<int, int>> := (if (true) then (map[21 := map[8 := 20, 22 := 26], 26 := map[1 := 2, -27 := 18], 0 := map[14 := 14, 6 := 28, 25 := 25, 9 := 5]]) else (map[-17 := map[14 := 20, -16 := 12, 0 := 17, 23 := 19, 26 := 13], 26 := map[26 := 11], 2 := map[7 := 27, 4 := 22, 18 := 8, 0 := 15, 26 := 22], 27 := map[19 := 28, 16 := 28, 29 := 1]]));
			var v_int_42: int := (if (true) then (-27) else (29));
			var v_map_5: map<int, int> := (if ((v_int_42 in v_map_4)) then (v_map_4[v_int_42]) else ((map[9 := 29, 19 := 27, -21 := 5, -22 := 7, 22 := 27] - {8, 8})));
			var v_int_44: int := ((10 + 2) % v_int_31);
			var v_seq_6: seq<int> := (if (true) then ([28, 11, 16, 17]) else ([15, 16]));
			var v_int_43: int := v_int_29;
			match (if ((v_int_44 in v_map_5)) then (v_map_5[v_int_44]) else ((if ((|v_seq_6| > 0)) then (v_seq_6[v_int_43]) else ((if (false) then (6) else (-20)))))) {
				case _ => {
					return ;
				}
				
			}
			
			if (v_bool_1 && v_bool_1) {
				var v_seq_11: seq<bool> := [];
				var v_int_51: int := 6;
				if ((v_bool_3 || (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_51]) else (false))) <== (if ((if (true) then (false) else (true))) then ((match 'J' {
					case _ => true
				})) else ((13 < 7)))) {
					return ;
				} else {
					return ;
				}
			}
			var v_seq_12: seq<set<char>> := [{}, {'O', 'f'}, {}];
			var v_int_54: int := 18;
			var v_seq_13: seq<array<char>> := [];
			var v_int_55: int := 16;
			var v_array_10: array<char> := new char[5] ['s', 'O', 'P', 'V', 'D'];
			var v_map_6: map<char, int> := map['G' := 29, 'B' := 18, 'U' := 19];
			var v_char_5: char := 'O';
			var v_int_52: int := (if (((if ((|v_seq_12| > 0)) then (v_seq_12[v_int_54]) else ({'s', 'N', 'W', 'S'})) !! (if (true) then ({}) else ({'M', 'a', 's'})))) then ((if ((|v_seq_13| > 0)) then (v_seq_13[v_int_55]) else (v_array_10)).Length) else (((if ((v_char_5 in v_map_6)) then (v_map_6[v_char_5]) else (0)) / (match 'u' {
				case _ => 21
			}))));
			var v_seq_14: seq<seq<bool>> := [];
			var v_int_56: int := 22;
			var v_seq_15: seq<bool> := (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_56]) else ([false, false, true, true]));
			var v_int_57: int := v_int_30;
			var v_map_7: map<char, bool> := map['a' := true, 'f' := false];
			var v_char_6: char := 'Y';
			var v_map_8: map<int, int> := map[7 := 24][10 := 13];
			var v_seq_16: seq<int> := [];
			var v_int_58: int := -9;
			var v_int_60: int := (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_58]) else (15));
			var v_seq_17: seq<int> := [4, 23];
			var v_int_59: int := 15;
			var v_int_53: int := (if ((if ((|v_seq_15| > 0)) then (v_seq_15[v_int_57]) else ((if ((v_char_6 in v_map_7)) then (v_map_7[v_char_6]) else (false))))) then (v_int_34) else ((if ((v_int_60 in v_map_8)) then (v_map_8[v_int_60]) else ((if ((|v_seq_17| > 0)) then (v_seq_17[v_int_59]) else (29))))));
			while (v_int_52 < v_int_53) 
				decreases v_int_53 - v_int_52;
				invariant (v_int_52 <= v_int_53);
			{
				v_int_52 := (v_int_52 + 1);
			}
			return ;
		}
			case _ => {
			var v_DT_1_1_13: DT_1 := DT_1_1;
			var v_DT_1_1_14: DT_1 := DT_1_1;
			var v_DT_1_1_15: DT_1 := DT_1_1;
			var v_DT_1_1_16: DT_1 := DT_1_1;
			var v_DT_1_1_17: DT_1 := DT_1_1;
			var v_DT_1_1_18: DT_1 := DT_1_1;
			print "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_bool_1", " ", v_bool_1, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_DT_1_1_9", " ", v_DT_1_1_9, " ", "v_bool_3", " ", v_bool_3, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_array_3", " ", (v_array_3 == v_array_1), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_int_9", " ", v_int_9, " ", "v_DT_1_1_12", " ", v_DT_1_1_12, " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_DT_1_1_10", " ", v_DT_1_1_10, " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_int_41", " ", v_int_41, " ", "v_char_3", " ", (v_char_3 == 'P'), " ", "v_char_2", " ", (v_char_2 == 'P'), " ", "v_char_4", " ", (v_char_4 == 'P'), " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_int_29", " ", v_int_29, " ", "v_map_1", " ", (v_map_1 == map[5 := map[27 := v_DT_1_1_13], 14 := map[6 := v_DT_1_1_14, 8 := v_DT_1_1_15]]), " ", "v_map_2", " ", (v_map_2 == map[2 := v_DT_1_1_16, 3 := v_DT_1_1_17, 28 := v_DT_1_1_18]), " ", "v_int_35", " ", v_int_35, " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_int_10", " ", v_int_10, " ", "v_int_32", " ", v_int_32, " ", "v_seq_5", " ", v_seq_5, " ", "v_int_37", " ", v_int_37, " ", "v_int_36", " ", v_int_36, " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_int_31", " ", v_int_31, " ", "v_int_30", " ", v_int_30, "\n";
			return ;
		}
		
	}
	
}
