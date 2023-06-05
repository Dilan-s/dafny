// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_2(DT_1_2_1: T_1)
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

method m_method_6(p_m_method_6_1: char) returns (ret_1: char, ret_2: char, ret_3: char, ret_4: char, ret_5: char)
{
	var v_char_32: char := p_m_method_6_1;
	var v_char_33: char := p_m_method_6_1;
	var v_char_34: char := p_m_method_6_1;
	var v_bool_3: bool := m_method_4(v_char_32, v_char_33, v_char_34);
	var v_map_5: map<char, bool> := map['Q' := true, 'x' := true, 'Y' := true, 'u' := true, 'w' := false];
	var v_char_35: char := 'P';
	if (v_bool_3 && (if (v_bool_3) then ((if ((v_char_35 in v_map_5)) then (v_map_5[v_char_35]) else (true))) else ((['j', 'J'] == ['P', 'z', 'Z'])))) {
		var v_map_6: map<char, bool> := map['V' := true, 't' := true, 'K' := true, 'X' := false, 'l' := true]['M' := true];
		var v_char_36: char := v_char_33;
		var v_seq_11: seq<char> := ['v', 'P', 'T', 'C'];
		var v_int_34: int := 10;
		var v_seq_12: seq<map<char, char>> := [];
		var v_int_35: int := 12;
		var v_map_7: map<char, char> := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_35]) else (map['B' := 's']));
		var v_char_37: char := v_char_34;
		var v_seq_13: seq<char> := ['A', 'E', 'S', 'w'];
		var v_seq_14: seq<seq<char>> := [['F', 'L'], ['R'], [], ['Y']];
		var v_int_36: int := 12;
		var v_seq_16: seq<char> := (match 'B' {
			case _ => (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_36]) else (['T']))
		});
		var v_seq_15: seq<int> := (match 'x' {
			case _ => [-2, 15, 13, 16]
		});
		var v_map_8: map<char, int> := map['l' := 14, 'x' := 4, 'q' := 19];
		var v_char_38: char := 'w';
		var v_int_37: int := (if ((v_char_38 in v_map_8)) then (v_map_8[v_char_38]) else (-24));
		var v_int_38: int := (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_37]) else (|['b', 't']|));
		var v_seq_17: seq<char> := (if (true) then (['N']) else (['A']));
		var v_int_39: int := v_int_35;
		var v_map_9: map<char, bool> := map['J' := false, 'e' := true, 'w' := false, 'X' := true];
		var v_char_39: char := 'u';
		var v_seq_19: seq<char> := v_seq_16;
		var v_seq_18: seq<int> := [9, 7];
		var v_int_40: int := 14;
		var v_int_41: int := (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_40]) else (6));
		var v_seq_21: seq<char> := ((if (true) then (['b', 's', 'r']) else (['s', 'T', 'z', 'X'])) + v_seq_17);
		var v_array_1: array<char> := new char[4] ['u', 'b', 'v', 'v'];
		var v_array_2: array<char> := new char[3] ['T', 'a', 'k'];
		var v_seq_20: seq<array<char>> := [v_array_1, v_array_2];
		var v_int_42: int := -13;
		var v_array_3: array<char> := new char[4] ['v', 'X', 'O', 'E'];
		var v_int_43: int := (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_42]) else (v_array_3)).Length;
		return v_char_32, (if ((if ((v_char_36 in v_map_6)) then (v_map_6[v_char_36]) else (('q' !in {'Y', 'w', 'X', 'E'})))) then ((match 'C' {
			case _ => p_m_method_6_1
		})) else ((if ((v_char_37 in v_map_7)) then (v_map_7[v_char_37]) else ((match 'B' {
			case _ => 's'
		}))))), (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_38]) else ((if ((|v_seq_17| > 0)) then (v_seq_17[v_int_39]) else ((if (false) then ('Q') else ('O')))))), (if ((match 'M' {
			case _ => (if ((v_char_39 in v_map_9)) then (v_map_9[v_char_39]) else (false))
		})) then ((if ((|v_seq_19| > 0)) then (v_seq_19[v_int_41]) else ((if (true) then ('l') else ('h'))))) else (v_char_33)), (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_43]) else ((match 's' {
			case _ => (if (false) then ('O') else ('x'))
		})));
	} else {
		var v_map_10: map<char, bool> := (map['Y' := false, 'h' := false, 'i' := true, 'K' := true, 'S' := false] - {'A'});
		var v_char_40: char := v_char_32;
		var v_seq_22: seq<map<char, char>> := [];
		var v_int_44: int := 4;
		var v_map_12: map<char, char> := (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_44]) else (map['G' := 'f', 'f' := 'x', 'C' := 'f']));
		var v_char_42: char := v_char_32;
		var v_map_11: map<char, char> := map['Q' := 'U', 'h' := 'k', 'y' := 'E', 'g' := 'M'];
		var v_char_41: char := 'k';
		var v_seq_23: seq<char> := ['W', 'D', 'N'];
		var v_int_45: int := 12;
		var v_map_13: map<char, char> := map['P' := 'h', 'D' := 'S'];
		var v_char_43: char := 'F';
		var v_seq_24: seq<char> := ['Y'];
		var v_int_46: int := 0;
		var v_map_14: map<char, char> := ((match 'y' {
			case _ => map['c' := 'r']
		}) - ({} * {'u', 's'}));
		var v_seq_25: seq<char> := [];
		var v_seq_26: seq<char> := (if ((|v_seq_25| > 0)) then (v_seq_25[9..10]) else (v_seq_25));
		var v_int_47: int := (-28.07).Floor;
		var v_seq_27: seq<char> := ['n'];
		var v_int_48: int := 15;
		var v_char_44: char := (if ((|v_seq_26| > 0)) then (v_seq_26[v_int_47]) else ((if ((|v_seq_27| > 0)) then (v_seq_27[v_int_48]) else ('c'))));
		var v_seq_28: seq<char> := ['F', 'a'];
		var v_int_49: int := -14;
		var v_seq_29: seq<char> := ['K'];
		var v_int_50: int := 26;
		var v_seq_30: seq<seq<map<char, char>>> := [[], [map['M' := 'g', 'g' := 'C', 'k' := 'a', 'm' := 'O', 'E' := 'F'], map['d' := 'h', 'k' := 'Q', 'g' := 'x', 'M' := 'e', 'c' := 'x'], map['X' := 'z', 'z' := 'K', 'A' := 'G', 'm' := 'Y', 'i' := 'N'], map['g' := 'q', 'G' := 'o', 'p' := 'y']]];
		var v_int_51: int := 16;
		var v_seq_31: seq<map<char, char>> := (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_51]) else ([]));
		var v_int_52: int := v_int_48;
		var v_map_16: map<char, char> := (if ((|v_seq_31| > 0)) then (v_seq_31[v_int_52]) else ((match 'X' {
			case _ => map['f' := 'W']
		})));
		var v_char_46: char := v_char_32;
		var v_map_15: map<char, char> := map['A' := 'U', 's' := 'd', 'W' := 't']['O' := 'o'];
		var v_char_45: char := (match 'r' {
			case _ => 'g'
		});
		return (if ((if ((v_char_40 in v_map_10)) then (v_map_10[v_char_40]) else ((match 'p' {
			case _ => false
		})))) then ((if ((v_char_42 in v_map_12)) then (v_map_12[v_char_42]) else ((if ((v_char_41 in v_map_11)) then (v_map_11[v_char_41]) else ('K'))))) else ((match 'Z' {
			case _ => (match 'M' {
				case _ => 'g'
			})
		}))), (match 'X' {
			case _ => (if (('Z' in map['m' := 'E', 'd' := 'k'])) then ((if ((v_char_43 in v_map_13)) then (v_map_13[v_char_43]) else ('k'))) else ((if ((|v_seq_24| > 0)) then (v_seq_24[v_int_46]) else ('S'))))
		}), (if ((v_char_44 in v_map_14)) then (v_map_14[v_char_44]) else ((match 'q' {
			case _ => (if ((|v_seq_29| > 0)) then (v_seq_29[v_int_50]) else ('r'))
		}))), p_m_method_6_1, (if ((v_char_46 in v_map_16)) then (v_map_16[v_char_46]) else ((if ((v_char_45 in v_map_15)) then (v_map_15[v_char_45]) else ((if (true) then ('y') else ('v'))))));
	}
}

method m_method_5(p_m_method_5_1: char, p_m_method_5_2: char, p_m_method_5_3: char, p_m_method_5_4: char) returns (ret_1: char)
	requires ((p_m_method_5_4 == 'j') && (p_m_method_5_1 == 'l') && (p_m_method_5_3 == 'b') && (p_m_method_5_2 == 'o')) || ((p_m_method_5_4 == 'T') && (p_m_method_5_1 == 'y') && (p_m_method_5_3 == 'F') && (p_m_method_5_2 == 'F')) || ((p_m_method_5_4 == 'x') && (p_m_method_5_1 == 'y') && (p_m_method_5_3 == 'L') && (p_m_method_5_2 == 'D'));
	ensures (((p_m_method_5_4 == 'j') && (p_m_method_5_1 == 'l') && (p_m_method_5_3 == 'b') && (p_m_method_5_2 == 'o')) ==> ((ret_1 == 'l'))) && (((p_m_method_5_4 == 'T') && (p_m_method_5_1 == 'y') && (p_m_method_5_3 == 'F') && (p_m_method_5_2 == 'F')) ==> ((ret_1 == 'y'))) && (((p_m_method_5_4 == 'x') && (p_m_method_5_1 == 'y') && (p_m_method_5_3 == 'L') && (p_m_method_5_2 == 'D')) ==> ((ret_1 == 'y')));
{
	var v_seq_9: seq<int> := (if (true) then ([25, -24, -11, 14]) else ([]));
	var v_int_27: int := 16;
	var v_int_28: int := -2;
	var v_int_29: int := safe_modulus(v_int_27, v_int_28);
	var v_int_30: int := v_int_29;
	var v_int_31: int, v_int_32: int := (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_30]) else (v_int_27)), v_int_29;
	for v_int_26 := v_int_31 downto v_int_32 
		invariant (v_int_26 - v_int_32 >= 0)
	{
		assert ((v_seq_9 == [25, -24, -11, 14]) && (p_m_method_5_3 == 'b') && (v_int_30 == 0)) || ((v_seq_9 == [25, -24, -11, 14]) && (p_m_method_5_3 == 'L') && (v_int_30 == 0)) || ((v_seq_9 == [25, -24, -11, 14]) && (p_m_method_5_3 == 'F') && (v_int_30 == 0));
		expect ((v_seq_9 == [25, -24, -11, 14]) && (p_m_method_5_3 == 'b') && (v_int_30 == 0)) || ((v_seq_9 == [25, -24, -11, 14]) && (p_m_method_5_3 == 'L') && (v_int_30 == 0)) || ((v_seq_9 == [25, -24, -11, 14]) && (p_m_method_5_3 == 'F') && (v_int_30 == 0));
		print "v_int_26", " ", v_int_26, " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "p_m_method_5_4", " ", (p_m_method_5_4 == 'j'), " ", "p_m_method_5_3", " ", (p_m_method_5_3 == 'b'), " ", "v_int_29", " ", v_int_29, " ", "v_int_30", " ", v_int_30, " ", "p_m_method_5_2", " ", (p_m_method_5_2 == 'o'), " ", "p_m_method_5_1", " ", (p_m_method_5_1 == 'l'), " ", "v_seq_9", " ", v_seq_9, "\n";
		break;
	}
	print "v_int_32", " ", v_int_32, " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "p_m_method_5_4", " ", (p_m_method_5_4 == 'j'), " ", "p_m_method_5_3", " ", (p_m_method_5_3 == 'b'), " ", "v_int_29", " ", v_int_29, " ", "v_int_31", " ", v_int_31, " ", "v_int_30", " ", v_int_30, " ", "p_m_method_5_2", " ", (p_m_method_5_2 == 'o'), " ", "p_m_method_5_1", " ", (p_m_method_5_1 == 'l'), " ", "v_seq_9", " ", v_seq_9, "\n";
	return p_m_method_5_1;
}

method m_method_4(p_m_method_4_1: char, p_m_method_4_2: char, p_m_method_4_3: char) returns (ret_1: bool)
	requires ((p_m_method_4_2 == 'g') && (p_m_method_4_1 == 'q') && (p_m_method_4_3 == 'J'));
	ensures (((p_m_method_4_2 == 'g') && (p_m_method_4_1 == 'q') && (p_m_method_4_3 == 'J')) ==> ((ret_1 == false)));
{
	match 'd' {
		case 'D' => {
			var v_char_9: char := 'v';
			var v_int_11: int := 26;
			var v_int_12: int := 15;
			while (v_int_11 < v_int_12) 
				decreases v_int_12 - v_int_11;
				invariant (v_int_11 <= v_int_12);
			{
				v_int_11 := (v_int_11 + 1);
				return true;
			}
			return true;
		}
			case 'l' => {
			var v_int_14: int, v_int_15: int := 25, 8;
			for v_int_13 := v_int_14 to v_int_15 
				invariant (v_int_15 - v_int_13 >= 0)
			{
				
			}
			if true {
				
			}
			if true {
				return true;
			}
			var v_int_16: int := 21;
			var v_int_17: int := 27;
			while (v_int_16 < v_int_17) 
				decreases v_int_17 - v_int_16;
				invariant (v_int_16 <= v_int_17);
			{
				v_int_16 := (v_int_16 + 1);
				return false;
			}
			var v_int_18: int := -4;
			var v_int_19: int := 11;
			while (v_int_18 < v_int_19) 
				decreases v_int_19 - v_int_18;
				invariant (v_int_18 <= v_int_19);
			{
				v_int_18 := (v_int_18 + 1);
				return false;
			}
			if true {
				return false;
			}
			return true;
		}
			case _ => {
			
		}
		
	}
	
	print "p_m_method_4_1", " ", (p_m_method_4_1 == 'q'), " ", "p_m_method_4_3", " ", (p_m_method_4_3 == 'J'), " ", "p_m_method_4_2", " ", (p_m_method_4_2 == 'g'), "\n";
	return false;
}

method m_method_3(p_m_method_3_1: char, p_m_method_3_2: char, p_m_method_3_3: char) returns (ret_1: seq<bool>)
	requires ((p_m_method_3_1 == 'B') && (p_m_method_3_3 == 'R') && (p_m_method_3_2 == 'e'));
	ensures (((p_m_method_3_1 == 'B') && (p_m_method_3_3 == 'R') && (p_m_method_3_2 == 'e')) ==> (|ret_1| == 0));
{
	if false {
		
	}
	var v_int_8: int := 4;
	var v_int_9: int := 23;
	while (v_int_8 < v_int_9) 
		decreases v_int_9 - v_int_8;
		invariant (v_int_8 <= v_int_9);
	{
		v_int_8 := (v_int_8 + 1);
		print "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, " ", "p_m_method_3_2", " ", (p_m_method_3_2 == 'e'), " ", "p_m_method_3_1", " ", (p_m_method_3_1 == 'B'), " ", "p_m_method_3_3", " ", (p_m_method_3_3 == 'R'), "\n";
		return [];
	}
	return [true, false];
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

method m_method_2(p_m_method_2_1: char, p_m_method_2_2: char, p_m_method_2_3: char, p_m_method_2_4: char) returns (ret_1: DT_1<(int, real), int>)
	requires ((p_m_method_2_2 == 'W') && (p_m_method_2_1 == 'I') && (p_m_method_2_4 == 'n') && (p_m_method_2_3 == 'q'));
	ensures (((p_m_method_2_2 == 'W') && (p_m_method_2_1 == 'I') && (p_m_method_2_4 == 'n') && (p_m_method_2_3 == 'q')) ==> ((ret_1.DT_1_2? && (((ret_1.DT_1_2_1).0 == 9) && (-28.38 < (ret_1.DT_1_2_1).1 < -28.18)))));
{
	var v_int_real_2: (int, real) := (9, -28.28);
	var v_DT_1_2_2: DT_1<(int, real), int> := DT_1_2(v_int_real_2);
	var v_int_real_3: (int, real) := (9, -28.28);
	var v_DT_1_2_4: DT_1<(int, real), int> := DT_1_2(v_int_real_3);
	var v_int_real_4: (int, real) := (9, -28.28);
	var v_int_real_5: (int, real) := (9, -28.28);
	print "p_m_method_2_1", " ", (p_m_method_2_1 == 'I'), " ", "v_DT_1_2_2", " ", (v_DT_1_2_2 == v_DT_1_2_4), " ", "v_DT_1_2_2.DT_1_2_1", " ", (v_DT_1_2_2.DT_1_2_1 == v_int_real_4), " ", "v_int_real_2.1", " ", (v_int_real_2.1 == -28.28), " ", "v_int_real_2.0", " ", v_int_real_2.0, " ", "p_m_method_2_3", " ", (p_m_method_2_3 == 'q'), " ", "p_m_method_2_2", " ", (p_m_method_2_2 == 'W'), " ", "p_m_method_2_4", " ", (p_m_method_2_4 == 'n'), " ", "v_int_real_2", " ", (v_int_real_2 == v_int_real_5), "\n";
	return v_DT_1_2_2;
}

method m_method_1(p_m_method_1_1: int, p_m_method_1_2: int, p_m_method_1_3: char, p_m_method_1_4: char) returns (ret_1: bool)
	requires ((p_m_method_1_1 == 0) && (p_m_method_1_3 == 'T') && (p_m_method_1_2 == 0) && (p_m_method_1_4 == 'g'));
	ensures (((p_m_method_1_1 == 0) && (p_m_method_1_3 == 'T') && (p_m_method_1_2 == 0) && (p_m_method_1_4 == 'g')) ==> ((ret_1 == false)));
{
	var v_int_real_1: (int, real) := (8, -7.92);
	var v_DT_1_2_1: DT_1<(int, real), int> := DT_1_2(v_int_real_1);
	var v_char_1: char := 'I';
	var v_char_2: char := 'W';
	var v_char_3: char := 'q';
	var v_char_4: char := 'n';
	var v_DT_1_2_3: DT_1<(int, real), int> := m_method_2(v_char_1, v_char_2, v_char_3, v_char_4);
	var v_DT_1_1_1: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_1: (DT_1<real, int>, char) := (v_DT_1_1_1, 'R');
	var v_DT_1_1_2: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_2: (DT_1<real, int>, char) := (v_DT_1_1_2, 'p');
	var v_DT_1_1_3: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_3: (DT_1<real, int>, char) := (v_DT_1_1_3, 'b');
	var v_seq_3: seq<(DT_1<real, int>, char)> := [v_DT_1_1_char_1, v_DT_1_1_char_2, v_DT_1_1_char_3];
	var v_int_7: int := 17;
	var v_DT_1_1_4: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_4: (DT_1<real, int>, char) := (v_DT_1_1_4, 'C');
	var v_DT_1_1_5: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_5: (DT_1<real, int>, char) := (v_DT_1_1_5, 'e');
	var v_DT_1_1_6: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_6: (DT_1<real, int>, char) := (v_DT_1_1_6, 'L');
	var v_DT_1_1_7: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_7: (DT_1<real, int>, char) := (v_DT_1_1_7, 'Q');
	var v_map_1: map<char, (DT_1<real, int>, char)> := map['X' := v_DT_1_1_char_5, 'J' := v_DT_1_1_char_6, 'C' := v_DT_1_1_char_7];
	var v_char_5: char := 'G';
	var v_DT_1_1_8: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_8: (DT_1<real, int>, char) := (v_DT_1_1_8, 'V');
	v_int_7, v_DT_1_2_3, v_char_5, v_DT_1_1_char_7 := p_m_method_1_1, (if (false) then (v_DT_1_2_1) else (v_DT_1_2_3)), v_char_4, (if ((if (true) then (false) else (false))) then ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else (v_DT_1_1_char_4))) else ((if ((v_char_5 in v_map_1)) then (v_map_1[v_char_5]) else (v_DT_1_1_char_8))));
	var v_char_6: char := 'B';
	var v_char_7: char := 'e';
	var v_char_8: char := 'R';
	var v_seq_4: seq<bool> := m_method_3(v_char_6, v_char_7, v_char_8);
	var v_seq_5: seq<bool> := v_seq_4;
	var v_int_10: int := 26;
	var v_char_10: char := 'q';
	var v_char_11: char := 'g';
	var v_char_12: char := 'J';
	var v_bool_1: bool := m_method_4(v_char_10, v_char_11, v_char_12);
	var v_int_real_6: (int, real) := (8, -7.92);
	var v_DT_1_2_5: DT_1<(int, real), int> := DT_1_2(v_int_real_6);
	var v_int_real_7: (int, real) := (9, -28.28);
	var v_DT_1_2_6: DT_1<(int, real), int> := DT_1_2(v_int_real_7);
	var v_DT_1_1_9: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_9: (DT_1<real, int>, char) := (v_DT_1_1_9, 'V');
	var v_DT_1_1_10: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_10: (DT_1<real, int>, char) := (v_DT_1_1_10, 'V');
	var v_int_real_8: (int, real) := (8, -7.92);
	var v_DT_1_1_11: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_11: (DT_1<real, int>, char) := (v_DT_1_1_11, 'p');
	var v_DT_1_1_12: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_12: (DT_1<real, int>, char) := (v_DT_1_1_12, 'R');
	var v_DT_1_1_13: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_13: (DT_1<real, int>, char) := (v_DT_1_1_13, 'L');
	var v_DT_1_1_14: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_14: (DT_1<real, int>, char) := (v_DT_1_1_14, 'e');
	var v_DT_1_1_15: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_15: (DT_1<real, int>, char) := (v_DT_1_1_15, 'C');
	var v_DT_1_1_16: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_16: (DT_1<real, int>, char) := (v_DT_1_1_16, 'b');
	var v_DT_1_1_17: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_17: (DT_1<real, int>, char) := (v_DT_1_1_17, 'Q');
	var v_DT_1_1_18: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_18: (DT_1<real, int>, char) := (v_DT_1_1_18, 'e');
	var v_DT_1_1_19: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_19: (DT_1<real, int>, char) := (v_DT_1_1_19, 'L');
	var v_int_real_9: (int, real) := (8, -7.92);
	var v_DT_1_1_20: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_20: (DT_1<real, int>, char) := (v_DT_1_1_20, 'R');
	var v_DT_1_1_21: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_21: (DT_1<real, int>, char) := (v_DT_1_1_21, 'p');
	var v_DT_1_1_22: DT_1<real, int> := DT_1_1;
	var v_DT_1_1_char_22: (DT_1<real, int>, char) := (v_DT_1_1_22, 'b');
	print "v_DT_1_2_1", " ", (v_DT_1_2_1 == v_DT_1_2_5), " ", "v_DT_1_2_3", " ", (v_DT_1_2_3 == v_DT_1_2_6), " ", "v_DT_1_1_char_8", " ", (v_DT_1_1_char_8 == v_DT_1_1_char_9), " ", "v_DT_1_1_char_7", " ", (v_DT_1_1_char_7 == v_DT_1_1_char_10), " ", "v_int_real_1", " ", (v_int_real_1 == v_int_real_8), " ", "v_DT_1_1_char_2", " ", (v_DT_1_1_char_2 == v_DT_1_1_char_11), " ", "v_DT_1_1_char_1", " ", (v_DT_1_1_char_1 == v_DT_1_1_char_12), " ", "v_DT_1_1_char_6", " ", (v_DT_1_1_char_6 == v_DT_1_1_char_13), " ", "v_DT_1_1_char_5", " ", (v_DT_1_1_char_5 == v_DT_1_1_char_14), " ", "v_DT_1_1_char_4", " ", (v_DT_1_1_char_4 == v_DT_1_1_char_15), " ", "v_DT_1_1_char_3", " ", (v_DT_1_1_char_3 == v_DT_1_1_char_16), " ", "v_DT_1_1_char_4.0", " ", v_DT_1_1_char_4.0, " ", "v_DT_1_1_char_2.1", " ", (v_DT_1_1_char_2.1 == 'p'), " ", "v_DT_1_1_char_2.0", " ", v_DT_1_1_char_2.0, " ", "v_DT_1_1_char_8.0", " ", v_DT_1_1_char_8.0, " ", "v_DT_1_1_char_6.1", " ", (v_DT_1_1_char_6.1 == 'L'), " ", "v_DT_1_1_char_6.0", " ", v_DT_1_1_char_6.0, " ", "v_DT_1_1_char_4.1", " ", (v_DT_1_1_char_4.1 == 'C'), " ", "v_DT_1_1_char_8.1", " ", (v_DT_1_1_char_8.1 == 'V'), " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_bool_1", " ", v_bool_1, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_char_12", " ", (v_char_12 == 'J'), " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_char_11", " ", (v_char_11 == 'g'), " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "p_m_method_1_4", " ", (p_m_method_1_4 == 'g'), " ", "p_m_method_1_3", " ", (p_m_method_1_3 == 'T'), " ", "v_char_1", " ", (v_char_1 == 'I'), " ", "v_char_3", " ", (v_char_3 == 'q'), " ", "v_char_2", " ", (v_char_2 == 'W'), " ", "v_char_5", " ", (v_char_5 == 'n'), " ", "v_char_4", " ", (v_char_4 == 'n'), " ", "v_char_7", " ", (v_char_7 == 'e'), " ", "v_char_6", " ", (v_char_6 == 'B'), " ", "v_int_7", " ", v_int_7, " ", "v_char_8", " ", (v_char_8 == 'R'), " ", "v_int_real_1.1", " ", (v_int_real_1.1 == -7.92), " ", "v_int_real_1.0", " ", v_int_real_1.0, " ", "v_DT_1_1_char_3.1", " ", (v_DT_1_1_char_3.1 == 'b'), " ", "v_map_1", " ", (v_map_1 == map['C' := v_DT_1_1_char_17, 'X' := v_DT_1_1_char_18, 'J' := v_DT_1_1_char_19]), " ", "v_DT_1_2_1.DT_1_2_1", " ", (v_DT_1_2_1.DT_1_2_1 == v_int_real_9), " ", "v_DT_1_1_char_3.0", " ", v_DT_1_1_char_3.0, " ", "v_DT_1_1_char_1.1", " ", (v_DT_1_1_char_1.1 == 'R'), " ", "v_DT_1_1_char_1.0", " ", v_DT_1_1_char_1.0, " ", "v_DT_1_1_char_7.1", " ", (v_DT_1_1_char_7.1 == 'V'), " ", "v_DT_1_1_char_7.0", " ", v_DT_1_1_char_7.0, " ", "v_DT_1_1_char_5.1", " ", (v_DT_1_1_char_5.1 == 'e'), " ", "v_DT_1_1_char_5.0", " ", v_DT_1_1_char_5.0, " ", "v_seq_5", " ", v_seq_5, " ", "v_int_10", " ", v_int_10, " ", "v_seq_4", " ", v_seq_4, " ", "v_seq_3", " ", (v_seq_3 == [v_DT_1_1_char_20, v_DT_1_1_char_21, v_DT_1_1_char_22]), " ", "v_char_10", " ", (v_char_10 == 'q'), "\n";
	return (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_10]) else (v_bool_1));
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_map_3: map<char, int> := (map['F' := 0] - {'J', 'z'});
	var v_map_2: map<real, char> := map[-22.41 := 'v', -2.66 := 'B', -18.04 := 'g', -18.51 := 'W', -13.54 := 'a'];
	var v_real_1: real := 29.65;
	var v_char_13: char := (if ((v_real_1 in v_map_2)) then (v_map_2[v_real_1]) else ('g'));
	var v_seq_6: seq<char> := ['H'];
	var v_int_20: int := -26;
	var v_int_21: int := safe_index_seq(v_seq_6, v_int_20);
	var v_int_24: int := (if ((v_char_13 in v_map_3)) then (v_map_3[v_char_13]) else (v_int_21));
	var v_int_25: int := v_int_21;
	var v_seq_7: seq<char> := ['Z', 'S', 'O'];
	var v_int_22: int := 24;
	var v_seq_8: seq<char> := ['T'];
	var v_int_23: int := -2;
	var v_seq_86: seq<char> := v_seq_8;
	var v_int_116: int := v_int_23;
	var v_int_117: int := safe_index_seq(v_seq_86, v_int_116);
	v_int_23 := v_int_117;
	var v_char_14: char := (match 'c' {
		case 'a' => (if (true) then ('r') else ('T'))
		case 'G' => (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_22]) else ('b'))
		case _ => (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_23]) else ('v'))
	});
	var v_char_15: char := v_char_13;
	var v_bool_2: bool := m_method_1(v_int_24, v_int_25, v_char_14, v_char_15);
	match v_bool_2 {
		case true => {
			assert true;
			expect true;
			return ;
		}
			case false => {
			var v_char_16: char := 'l';
			var v_char_17: char := 'o';
			var v_char_18: char := 'b';
			var v_char_19: char := 'j';
			var v_char_20: char := m_method_5(v_char_16, v_char_17, v_char_18, v_char_19);
			var v_char_21: char := 'y';
			var v_char_22: char := 'D';
			var v_char_23: char := 'L';
			var v_char_24: char := 'x';
			var v_char_25: char := m_method_5(v_char_21, v_char_22, v_char_23, v_char_24);
			var v_char_27: char := (match 's' {
				case 'V' => v_char_20
				case 'q' => (match 'L' {
					case _ => 'S'
				})
				case _ => v_char_25
			});
			var v_map_4: map<char, seq<char>> := map['u' := ['k'], 'B' := ['w', 'V', 'r', 'D'], 'V' := ['Y', 'P', 's'], 'T' := ['w', 'J'], 't' := []];
			var v_char_26: char := 'F';
			var v_seq_10: seq<char> := (if ((v_char_26 in v_map_4)) then (v_map_4[v_char_26]) else ([]));
			var v_int_33: int := (19.90).Floor;
			var v_char_28: char := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_33]) else (v_char_26));
			var v_char_29: char := v_char_26;
			var v_char_30: char := v_char_14;
			var v_char_31: char := m_method_5(v_char_27, v_char_28, v_char_29, v_char_30);
			match v_char_31 {
				case 'L' => {
					var v_seq_32: seq<char> := (['K', 'Z'] + []);
					var v_int_53: int := (5 % 13);
					var v_seq_33: seq<char> := [];
					var v_int_54: int := 9;
					var v_char_49: char := (if ((|v_seq_32| > 0)) then (v_seq_32[v_int_53]) else ((if ((|v_seq_33| > 0)) then (v_seq_33[v_int_54]) else ('U'))));
					var v_map_17: map<char, char> := map['f' := 'B', 'C' := 'X', 'o' := 'f', 'j' := 'q'];
					var v_char_47: char := 'y';
					var v_char_50: char := (if (v_bool_2) then (v_char_13) else ((if ((v_char_47 in v_map_17)) then (v_map_17[v_char_47]) else ('T'))));
					var v_seq_34: seq<char> := ['C', 'A'];
					var v_int_55: int := 5;
					var v_map_18: map<char, char> := map['K' := 'W'];
					var v_char_48: char := 'v';
					var v_char_51: char := (if ((false == true)) then ((if ((|v_seq_34| > 0)) then (v_seq_34[v_int_55]) else ('d'))) else ((if ((v_char_48 in v_map_18)) then (v_map_18[v_char_48]) else ('i'))));
					var v_char_52: char := (match 'f' {
						case _ => v_char_26
					});
					var v_char_53: char := m_method_5(v_char_49, v_char_50, v_char_51, v_char_52);
					var v_char_54: char := v_char_53;
					var v_char_55: char, v_char_56: char, v_char_57: char, v_char_58: char, v_char_59: char := m_method_6(v_char_54);
					v_char_15, v_char_55, v_char_13, v_char_29, v_char_58 := v_char_55, v_char_56, v_char_57, v_char_58, v_char_59;
					var v_seq_35: seq<seq<char>> := [];
					var v_seq_36: seq<seq<char>> := (if ((|v_seq_35| > 0)) then (v_seq_35[13..-8]) else (v_seq_35));
					var v_map_19: map<char, int> := map['o' := 10];
					var v_char_60: char := 'k';
					var v_int_56: int := (if ((v_char_60 in v_map_19)) then (v_map_19[v_char_60]) else (19));
					var v_seq_39: seq<char> := (if ((|v_seq_36| > 0)) then (v_seq_36[v_int_56]) else ((if (false) then (['Q', 'E', 'u']) else (['m', 'n']))));
					var v_seq_37: seq<bool> := [true, false];
					var v_int_57: int := 0;
					var v_seq_38: seq<int> := [6, 19, 7];
					var v_int_58: int := -2;
					var v_int_59: int := (if ((if ((|v_seq_37| > 0)) then (v_seq_37[v_int_57]) else (false))) then ((if (false) then (0) else (17))) else ((if ((|v_seq_38| > 0)) then (v_seq_38[v_int_58]) else (13))));
					var v_map_20: map<char, bool> := map['G' := false, 'n' := false, 'j' := false, 's' := true];
					var v_char_61: char := 'B';
					var v_map_21: map<char, bool> := map['P' := true];
					var v_char_62: char := 'C';
					var v_map_22: map<char, seq<char>> := map['e' := []];
					var v_char_63: char := 'J';
					var v_seq_40: seq<char> := (if ((v_char_63 in v_map_22)) then (v_map_22[v_char_63]) else ([]));
					var v_array_4: array<char> := new char[3] ['x', 'f', 'J'];
					var v_int_60: int := v_array_4.Length;
					var v_seq_41: seq<char> := (match 'Q' {
						case _ => ['H', 'H', 'A', 'O']
					});
					var v_seq_42: seq<char> := v_seq_41;
					var v_map_23: map<char, int> := map['T' := 27];
					var v_char_64: char := 'J';
					var v_int_61: int := (if ((v_char_64 in v_map_23)) then (v_map_23[v_char_64]) else (0));
					var v_int_62: int := safe_index_seq(v_seq_42, v_int_61);
					var v_int_63: int := v_int_62;
					var v_seq_43: seq<char> := (if ((|v_seq_41| > 0)) then (v_seq_41[v_int_63 := v_char_30]) else (v_seq_41));
					var v_int_64: int := (if ((false == false)) then (v_int_63) else ((match 'C' {
						case _ => -19
					})));
					var v_map_24: map<char, map<char, char>> := map['C' := map['a' := 'X', 'a' := 'U', 'P' := 'R', 'z' := 'O'], 'W' := map['d' := 'N', 'T' := 't'], 'N' := map['u' := 'u', 'U' := 'p', 'b' := 'a', 'j' := 'J'], 'l' := map['i' := 'S'], 't' := map['d' := 'C', 'F' := 'b']];
					var v_char_65: char := 'r';
					var v_map_25: map<char, char> := (if ((v_char_65 in v_map_24)) then (v_map_24[v_char_65]) else (map['U' := 'x', 'C' := 'q', 'n' := 'V', 'h' := 'g', 'e' := 'r']));
					var v_char_66: char := (if (true) then ('x') else ('c'));
					var v_seq_44: seq<char> := ['x', 'o', 'v', 'w'];
					var v_int_65: int := 11;
					v_char_62, v_char_15, v_char_63 := (if ((|v_seq_39| > 0)) then (v_seq_39[v_int_59]) else (v_char_14)), (if ((if ((['K'] <= ['c', 'A'])) then ((if ((v_char_61 in v_map_20)) then (v_map_20[v_char_61]) else (true))) else ((if ((v_char_62 in v_map_21)) then (v_map_21[v_char_62]) else (false))))) then ((if ((|v_seq_40| > 0)) then (v_seq_40[v_int_60]) else (v_char_55))) else (v_char_54)), (if ((|v_seq_43| > 0)) then (v_seq_43[v_int_64]) else ((if ((v_char_66 in v_map_25)) then (v_map_25[v_char_66]) else ((if ((|v_seq_44| > 0)) then (v_seq_44[v_int_65]) else ('u'))))));
					var v_map_26: map<char, set<char>> := map['f' := {'x', 'T', 'w', 'r'}, 'O' := {'c', 'x', 'h'}, 'o' := {'J'}];
					var v_char_67: char := 'e';
					var v_map_27: map<char, char> := (map['f' := 'x', 'E' := 'G', 'M' := 't']['T' := 'd'] - (if ((v_char_67 in v_map_26)) then (v_map_26[v_char_67]) else ({'U'})));
					var v_char_68: char := v_char_15;
					var v_map_28: map<char, bool> := map['T' := false];
					var v_char_69: char := 'm';
					var v_map_29: map<char, bool> := map['o' := true, 'c' := false];
					var v_char_70: char := 'S';
					v_char_48, v_char_54 := (if ((v_char_68 in v_map_27)) then (v_map_27[v_char_68]) else (v_char_60)), (if ((match 'l' {
						case _ => (if ((v_char_70 in v_map_29)) then (v_map_29[v_char_70]) else (true))
					})) then (v_char_65) else (v_char_47));
					var v_seq_45: seq<char> := ['s', 'q', 'K', 'b'];
					var v_seq_46: seq<char> := (if ((|v_seq_45| > 0)) then (v_seq_45[24..16]) else (v_seq_45));
					var v_map_30: map<char, int> := map['F' := 23, 'w' := 17, 'w' := 11];
					var v_char_71: char := 't';
					var v_int_66: int := (if ((v_char_71 in v_map_30)) then (v_map_30[v_char_71]) else (-21));
					var v_map_32: map<char, char> := map['C' := 'g', 'I' := 'B', 'C' := 'G', 'f' := 'j', 'K' := 'y']['b' := 'u'];
					var v_char_73: char := (match 'I' {
						case _ => 'a'
					});
					var v_map_31: map<char, char> := map['I' := 'F', 'D' := 'G', 't' := 'M'];
					var v_char_72: char := 'b';
					var v_map_33: map<char, char> := map['U' := 'U', 'F' := 'B', 'U' := 'e', 't' := 'b']['w' := 'X'];
					var v_char_74: char := (if (true) then ('Q') else ('v'));
					var v_map_34: map<char, char> := map['X' := 'u', 'o' := 'O', 'I' := 'S', 'U' := 's'];
					var v_char_75: char := 'z';
					var v_map_35: map<char, char> := map['f' := 'W']['H' := 'P'];
					var v_char_76: char := (if (true) then ('j') else ('p'));
					var v_seq_47: seq<char> := ['E', 'd'];
					var v_int_67: int := 4;
					v_char_28, v_char_64, v_char_27, v_char_53 := v_char_59, (match 's' {
						case _ => (if ((v_char_73 in v_map_32)) then (v_map_32[v_char_73]) else ((if ((v_char_72 in v_map_31)) then (v_map_31[v_char_72]) else ('J'))))
					}), (match 'X' {
						case _ => (if ((match 'o' {
							case _ => true
						})) then ((if ((v_char_75 in v_map_34)) then (v_map_34[v_char_75]) else ('k'))) else (v_char_28))
					}), (match 'h' {
						case _ => (match 'j' {
							case _ => v_char_65
						})
					});
					assert true;
					expect true;
					var v_map_36: map<char, int> := v_map_3;
					var v_char_77: char := v_array_4[1];
					var v_seq_48: seq<map<char, char>> := [map['P' := 'S', 'A' := 'm', 'q' := 'Q'], map['m' := 'D', 'n' := 'g', 'x' := 'V'], map['X' := 'U'], map['Q' := 'V', 't' := 'g', 'e' := 'g', 'G' := 'd']];
					var v_int_70: int := 1;
					var v_int_68: int := (if ((v_char_77 in v_map_36)) then (v_map_36[v_char_77]) else (|(if ((|v_seq_48| > 0)) then (v_seq_48[v_int_70]) else (map['j' := 'u', 'w' := 'C', 'W' := 'a']))|));
					var v_map_38: map<char, int> := v_map_3;
					var v_char_79: char := v_char_52;
					var v_map_37: map<char, int> := v_map_3;
					var v_seq_49: seq<char> := ['L', 's'];
					var v_int_71: int := 20;
					var v_char_78: char := (if ((|v_seq_49| > 0)) then (v_seq_49[v_int_71]) else ('z'));
					var v_array_5: array<char> := new char[4] ['a', 'M', 'i', 'E'];
					var v_int_69: int := (if ((v_char_79 in v_map_38)) then (v_map_38[v_char_79]) else ((if ((v_char_78 in v_map_37)) then (v_map_37[v_char_78]) else (v_array_5.Length))));
					while (v_int_68 < v_int_69) 
						decreases v_int_69 - v_int_68;
						invariant (v_int_68 <= v_int_69);
					{
						v_int_68 := (v_int_68 + 1);
					}
				}
					case _ => {
					var v_map_39: map<char, char> := map['p' := 'X']['K' := 'G'];
					var v_char_80: char := v_char_13;
					var v_map_41: map<char, char> := map['r' := 'e', 'i' := 'N', 's' := 'N']['I' := 'E'];
					var v_map_40: map<char, char> := map['F' := 'u', 'r' := 'z', 'E' := 'D'];
					var v_char_81: char := 'N';
					var v_char_82: char := (if ((v_char_81 in v_map_40)) then (v_map_40[v_char_81]) else ('z'));
					var v_seq_50: seq<char> := ['N', 'Y'];
					var v_seq_87: seq<char> := v_seq_50;
					var v_int_120: int := 29;
					var v_int_121: int := 0;
					var v_int_122: int, v_int_123: int := safe_subsequence(v_seq_87, v_int_120, v_int_121);
					var v_int_118: int, v_int_119: int := v_int_122, v_int_123;
					var v_seq_51: seq<char> := (if ((|v_seq_50| > 0)) then (v_seq_50[v_int_118..v_int_119]) else (v_seq_50));
					var v_int_72: int := (6 - 24);
					var v_map_42: map<char, char> := map['q' := 'W', 'v' := 'a', 'U' := 'T', 'R' := 'q', 'u' := 'Y'];
					var v_char_83: char := 'p';
					var v_map_43: map<char, char> := map['r' := 'H', 'w' := 'r', 'V' := 'h'];
					var v_char_84: char := 'Q';
					var v_map_44: map<char, char> := map['Q' := 'U', 'G' := 'S', 'x' := 'j', 'M' := 'F'];
					var v_char_85: char := 'p';
					v_char_29, v_char_14, v_char_31 := v_char_30, (match 'e' {
						case 'g' => (if ((v_char_80 in v_map_39)) then (v_map_39[v_char_80]) else (v_char_26))
						case _ => (if ((v_char_82 in v_map_41)) then (v_map_41[v_char_82]) else ((if (false) then ('K') else ('z'))))
					}), (match 'N' {
						case 'O' => (if ((|v_seq_51| > 0)) then (v_seq_51[v_int_72]) else (v_char_31))
						case 'r' => (if (({'a', 'Q', 'p'} != {'v', 'x', 'Q', 'N'})) then ((if ((v_char_83 in v_map_42)) then (v_map_42[v_char_83]) else ('d'))) else (v_char_13))
						case _ => (match 'Y' {
							case 'B' => (if ((v_char_84 in v_map_43)) then (v_map_43[v_char_84]) else ('X'))
							case 'D' => (if ((v_char_85 in v_map_44)) then (v_map_44[v_char_85]) else ('B'))
							case _ => (match 'R' {
								case 'r' => 'B'
								case 'J' => 'e'
								case _ => 'T'
							})
						})
					});
					var v_seq_52: seq<multiset<char>> := [multiset({'a', 'H', 'c', 'n'}), multiset{'T', 'f'}, multiset{'f', 'N', 'p'}];
					var v_seq_88: seq<multiset<char>> := v_seq_52;
					var v_int_126: int := 10;
					var v_int_127: int := 23;
					var v_int_128: int, v_int_129: int := safe_subsequence(v_seq_88, v_int_126, v_int_127);
					var v_int_124: int, v_int_125: int := v_int_128, v_int_129;
					var v_seq_54: seq<multiset<char>> := (if ((|v_seq_52| > 0)) then (v_seq_52[v_int_124..v_int_125]) else (v_seq_52));
					var v_seq_53: seq<int> := [-20, 11, 10];
					var v_int_74: int := 15;
					var v_seq_89: seq<int> := v_seq_53;
					var v_int_130: int := v_int_74;
					var v_int_131: int := safe_index_seq(v_seq_89, v_int_130);
					v_int_74 := v_int_131;
					var v_int_75: int := (if ((|v_seq_53| > 0)) then (v_seq_53[v_int_74]) else (21));
					var v_map_45: map<char, int> := map['Y' := 11, 'I' := 9, 'L' := -10, 'Z' := 2, 's' := 15];
					var v_char_86: char := 'i';
					var v_int_76: int, v_int_77: int := |(if ((|v_seq_54| > 0)) then (v_seq_54[v_int_75]) else ((if (false) then (multiset{'N', 'e'}) else (multiset{}))))|, (if ((v_bool_2 ==> (false || true))) then (((if (false) then (29) else (15)) - (if ((v_char_86 in v_map_45)) then (v_map_45[v_char_86]) else (4)))) else (v_int_20));
					for v_int_73 := v_int_76 to v_int_77 
						invariant (v_int_77 - v_int_73 >= 0)
					{
						print "v_int_73", " ", v_int_73, " ", "v_char_29", " ", (v_char_29 == 'T'), " ", "v_char_14", " ", (v_char_14 == 'z'), " ", "v_seq_54", " ", (v_seq_54 == []), " ", "v_char_31", " ", (v_char_31 == 'T'), " ", "v_char_86", " ", (v_char_86 == 'i'), " ", "v_seq_52", " ", (v_seq_52 == [multiset{'a', 'c', 'H', 'n'}, multiset{'T', 'f'}, multiset{'p', 'f', 'N'}]), " ", "v_seq_53", " ", v_seq_53, " ", "v_map_45", " ", (v_map_45 == map['s' := 15, 'Y' := 11, 'I' := 9, 'Z' := 2, 'L' := -10]), " ", "v_int_75", " ", v_int_75, " ", "v_int_74", " ", v_int_74, " ", "v_char_29", " ", (v_char_29 == 'T'), " ", "v_map_4", " ", (v_map_4 == map['B' := ['w', 'V', 'r', 'D'], 'T' := ['w', 'J'], 't' := [], 'u' := ['k'], 'V' := ['Y', 'P', 's']]), " ", "v_char_28", " ", (v_char_28 == 'F'), " ", "v_int_33", " ", v_int_33, " ", "v_char_27", " ", (v_char_27 == 'y'), " ", "v_char_26", " ", (v_char_26 == 'F'), " ", "v_seq_10", " ", (v_seq_10 == []), " ", "v_char_31", " ", (v_char_31 == 'T'), " ", "v_char_30", " ", (v_char_30 == 'T'), " ", "v_int_24", " ", v_int_24, " ", "v_seq_6", " ", (v_seq_6 == ['H']), " ", "v_int_21", " ", v_int_21, " ", "v_char_15", " ", (v_char_15 == 'g'), " ", "v_bool_2", " ", v_bool_2, " ", "v_char_14", " ", (v_char_14 == 'z'), " ", "v_char_13", " ", (v_char_13 == 'g'), " ", "v_int_25", " ", v_int_25, " ", "v_real_1", " ", (v_real_1 == 29.65), " ", "v_int_20", " ", v_int_20, " ", "v_map_3", " ", (v_map_3 == map['F' := 0]), " ", "v_map_2", " ", (v_map_2 == map[-18.51 := 'W', -2.66 := 'B', -18.04 := 'g', -13.54 := 'a', -22.41 := 'v']), "\n";
						return ;
					}
					assert true;
					expect true;
					return ;
				}
				
			}
			
			return ;
		}
			case _ => {
			var v_seq_55: seq<int> := [10, 15, 28];
			var v_int_78: int := 0;
			if (v_int_21 <= ((4 / 9) - (if ((|v_seq_55| > 0)) then (v_seq_55[v_int_78]) else (0)))) {
				assert true;
				expect true;
				var v_map_46: map<char, map<char, bool>> := map['v' := map['j' := false, 'H' := true], 'T' := map['F' := false, 'j' := false, 'D' := true, 'e' := false], 'B' := map['s' := true, 'K' := true, 's' := false, 'v' := true, 'e' := true], 'k' := map['W' := false, 'c' := false, 'h' := false], 'V' := map['n' := false, 'i' := false, 'O' := true]];
				var v_char_87: char := 'j';
				var v_map_48: map<char, bool> := (if ((v_char_87 in v_map_46)) then (v_map_46[v_char_87]) else (map['Z' := true, 'X' := true, 'r' := false]));
				var v_map_47: map<char, char> := map['D' := 'Q', 'Z' := 'P'];
				var v_char_88: char := 'r';
				var v_char_89: char := (if ((v_char_88 in v_map_47)) then (v_map_47[v_char_88]) else ('b'));
				var v_seq_56: seq<char> := ['y', 'R', 'S'];
				var v_seq_57: seq<char> := v_seq_56;
				var v_int_79: int := 6;
				var v_int_80: int := safe_index_seq(v_seq_57, v_int_79);
				var v_int_81: int := v_int_80;
				var v_seq_58: seq<char> := (if ((|v_seq_56| > 0)) then (v_seq_56[v_int_81 := 'O']) else (v_seq_56));
				var v_int_82: int := v_int_81;
				var v_seq_59: seq<char> := ['Y'];
				var v_seq_61: seq<char> := (if ((|v_seq_59| > 0)) then (v_seq_59[24..29]) else (v_seq_59));
				var v_seq_60: seq<int> := [24, 20];
				var v_int_83: int := -2;
				var v_int_84: int := (if ((|v_seq_60| > 0)) then (v_seq_60[v_int_83]) else (11));
				v_char_89, v_char_13 := v_char_14, (if ((if ((v_char_89 in v_map_48)) then (v_map_48[v_char_89]) else ((match 'd' {
					case _ => false
				})))) then ((if ((|v_seq_58| > 0)) then (v_seq_58[v_int_82]) else ((if (true) then ('Q') else ('z'))))) else ((if ((|v_seq_61| > 0)) then (v_seq_61[v_int_84]) else ((match 'Y' {
					case _ => 'j'
				})))));
				var v_seq_62: seq<int> := [9, 17, 4, -8];
				var v_seq_63: seq<int> := (if ((|v_seq_62| > 0)) then (v_seq_62[26..0]) else (v_seq_62));
				var v_int_86: int := (if (true) then (3) else (21));
				var v_int_87: int, v_int_88: int := v_int_80, (match 'g' {
					case _ => (if ((|v_seq_63| > 0)) then (v_seq_63[v_int_86]) else ((if (true) then (-12) else (24))))
				});
				for v_int_85 := v_int_87 to v_int_88 
					invariant (v_int_88 - v_int_85 >= 0)
				{
					var v_map_49: map<char, char> := map['r' := 't', 'D' := 'a', 'Y' := 'k'];
					var v_char_90: char := 'G';
					if (match 'a' {
						case _ => ((if ((v_char_90 in v_map_49)) then (v_map_49[v_char_90]) else ('r')) != (if (false) then ('C') else ('o')))
					}) {
						return ;
					} else {
						return ;
					}
				}
				if v_bool_2 {
					var v_seq_64: seq<char> := [];
					var v_int_89: int := -16;
					var v_map_51: map<char, char> := map['R' := 'W', 'c' := 'T', 'o' := 'X']['v' := 'B'][(match 'K' {
						case _ => 'c'
					}) := (if ((|v_seq_64| > 0)) then (v_seq_64[v_int_89]) else ('b'))];
					var v_map_50: map<char, bool> := map['n' := true, 'e' := true, 'R' := false, 'o' := true, 't' := false];
					var v_char_91: char := 'b';
					var v_char_92: char := (if ((if ((v_char_91 in v_map_50)) then (v_map_50[v_char_91]) else (false))) then (v_char_13) else ((match 'R' {
						case _ => 'W'
					})));
					var v_seq_65: seq<char> := ['e', 'S'];
					var v_seq_66: seq<char> := (if ((|v_seq_65| > 0)) then (v_seq_65[5..0]) else (v_seq_65));
					var v_int_90: int := (match 'r' {
						case _ => 13
					});
					v_char_87, v_char_89 := (if ((v_char_92 in v_map_51)) then (v_map_51[v_char_92]) else ((if ((|v_seq_66| > 0)) then (v_seq_66[v_int_90]) else ((match 'o' {
						case _ => 'P'
					}))))), v_char_89;
					return ;
				} else {
					assert true;
					expect true;
					var v_map_55: map<char, char> := (match 'V' {
						case _ => map['n' := 'r', 'i' := 'p', 'U' := 'I']
					})[(match 'X' {
						case _ => 'f'
					}) := v_char_15];
					var v_map_53: map<char, char> := map['W' := 'd', 'S' := 'S', 'T' := 'A']['M' := 'L'];
					var v_char_94: char := (match 'E' {
						case _ => 'M'
					});
					var v_map_52: map<char, char> := map['x' := 'W', 'M' := 't', 'N' := 'o'];
					var v_char_93: char := 'y';
					var v_char_96: char := (if ((v_char_94 in v_map_53)) then (v_map_53[v_char_94]) else ((if ((v_char_93 in v_map_52)) then (v_map_52[v_char_93]) else ('L'))));
					var v_seq_67: seq<char> := v_seq_59;
					var v_map_54: map<char, int> := map['x' := 17];
					var v_char_95: char := 'h';
					var v_int_91: int := (if ((v_char_95 in v_map_54)) then (v_map_54[v_char_95]) else (16));
					var v_seq_68: seq<map<char, bool>> := [map['w' := false, 'D' := true, 'F' := false], map['S' := true, 'L' := false, 'm' := true, 'y' := true, 'L' := false], map['Y' := false], map['Q' := true, 'i' := true, 'd' := false, 'j' := false]];
					var v_int_92: int := 6;
					var v_map_57: map<char, bool> := (if ((|v_seq_68| > 0)) then (v_seq_68[v_int_92]) else (map['Z' := true, 'F' := true, 'T' := true]));
					var v_map_56: map<char, char> := map['Z' := 'C'];
					var v_char_97: char := 'I';
					var v_char_98: char := (if ((v_char_97 in v_map_56)) then (v_map_56[v_char_97]) else ('X'));
					var v_seq_69: seq<bool> := [true, true];
					var v_int_93: int := 2;
					var v_seq_71: seq<char> := (match 'S' {
						case _ => ['p', 'o', 's']
					});
					var v_seq_70: seq<int> := [16, 23, -28, 27];
					var v_int_94: int := 1;
					var v_int_95: int := (if ((|v_seq_70| > 0)) then (v_seq_70[v_int_94]) else (15));
					var v_seq_72: seq<char> := [];
					var v_int_96: int := 22;
					var v_seq_73: seq<char> := ['T', 'K', 'k', 'S'];
					var v_seq_74: seq<char> := v_seq_73;
					var v_int_97: int := 27;
					var v_int_98: int := safe_index_seq(v_seq_74, v_int_97);
					var v_int_99: int := v_int_98;
					var v_seq_76: seq<char> := (if ((|v_seq_73| > 0)) then (v_seq_73[v_int_99 := 'S']) else (v_seq_73));
					var v_seq_77: seq<char> := v_seq_76;
					var v_int_101: int := (if (false) then (26) else (26));
					var v_int_102: int := safe_index_seq(v_seq_77, v_int_101);
					var v_int_103: int := v_int_102;
					var v_seq_75: seq<char> := ['F', 'Q', 'E', 'i'];
					var v_int_100: int := 5;
					var v_seq_78: seq<char> := (if ((|v_seq_76| > 0)) then (v_seq_76[v_int_103 := (if ((|v_seq_75| > 0)) then (v_seq_75[v_int_100]) else ('D'))]) else (v_seq_76));
					var v_map_60: map<char, int> := map['m' := 22, 'd' := 0, 'F' := 24, 'a' := 6, 'Q' := 7]['Q' := -21];
					var v_map_58: map<char, char> := map['x' := 'w', 'm' := 'Q', 'I' := 's', 'g' := 'j', 'q' := 'C'];
					var v_char_99: char := 't';
					var v_char_101: char := (if ((v_char_99 in v_map_58)) then (v_map_58[v_char_99]) else ('H'));
					var v_map_59: map<char, int> := map['K' := 2, 'E' := 16, 'D' := 26, 'x' := 19];
					var v_char_100: char := 'n';
					var v_int_104: int := (if ((v_char_101 in v_map_60)) then (v_map_60[v_char_101]) else ((if ((v_char_100 in v_map_59)) then (v_map_59[v_char_100]) else (22))));
					var v_seq_79: seq<seq<char>> := [['t']];
					var v_int_105: int := 5;
					var v_seq_80: seq<char> := (if ((|v_seq_79| > 0)) then (v_seq_79[v_int_105]) else (['T', 'S', 'Y', 'c']));
					var v_int_106: int := (match 'Y' {
						case _ => 11
					});
					var v_seq_81: seq<char> := ['p'];
					var v_int_107: int := 3;
					v_char_87, v_char_13, v_char_15, v_char_88 := (if ((v_char_96 in v_map_55)) then (v_map_55[v_char_96]) else ((if ((|v_seq_67| > 0)) then (v_seq_67[v_int_91]) else (v_char_13)))), (if ((if ((v_char_98 in v_map_57)) then (v_map_57[v_char_98]) else ((if ((|v_seq_69| > 0)) then (v_seq_69[v_int_93]) else (true))))) then ((if ((|v_seq_71| > 0)) then (v_seq_71[v_int_95]) else ((if ((|v_seq_72| > 0)) then (v_seq_72[v_int_96]) else ('X'))))) else (v_char_93)), (if ((|v_seq_78| > 0)) then (v_seq_78[v_int_104]) else ((if ((|v_seq_80| > 0)) then (v_seq_80[v_int_106]) else ((if ((|v_seq_81| > 0)) then (v_seq_81[v_int_107]) else ('T')))))), v_char_15;
					var v_seq_82: seq<array<char>> := [];
					var v_int_109: int := 18;
					var v_array_6: array<char> := new char[5] ['D', 'j', 'e', 'g', 'Q'];
					var v_seq_83: seq<int> := [];
					var v_seq_84: seq<int> := v_seq_83;
					var v_int_110: int := 18;
					var v_int_111: int := safe_index_seq(v_seq_84, v_int_110);
					var v_int_112: int := v_int_111;
					var v_seq_85: seq<int> := (if ((|v_seq_83| > 0)) then (v_seq_83[v_int_112 := 27]) else (v_seq_83));
					var v_map_61: map<char, int> := map['m' := 8];
					var v_char_102: char := 'j';
					var v_int_113: int := (if ((v_char_102 in v_map_61)) then (v_map_61[v_char_102]) else (13));
					var v_int_114: int, v_int_115: int := (if ((v_bool_2 && v_bool_2)) then ((if ((|v_seq_82| > 0)) then (v_seq_82[v_int_109]) else (v_array_6)).Length) else (v_int_97)), (match 'M' {
						case _ => (if ((|v_seq_85| > 0)) then (v_seq_85[v_int_113]) else ((match 'V' {
							case _ => 15
						})))
					});
					for v_int_108 := v_int_114 to v_int_115 
						invariant (v_int_115 - v_int_108 >= 0)
					{
						return ;
					}
				}
				return ;
			} else {
				var v_map_62: map<char, bool> := map['f' := false, 'C' := true, 'B' := false];
				var v_char_103: char := 'k';
				var v_map_63: map<char, bool> := map['k' := false, 'O' := true, 'Y' := true, 'q' := false, 'M' := true];
				var v_char_104: char := 'e';
				if (match 'h' {
					case _ => (if ((if ((v_char_103 in v_map_62)) then (v_map_62[v_char_103]) else (false))) then ((match 'T' {
						case _ => true
					})) else ((if ((v_char_104 in v_map_63)) then (v_map_63[v_char_104]) else (true))))
				}) {
					assert true;
					expect true;
				}
				return ;
			}
		}
		
	}
	
}
