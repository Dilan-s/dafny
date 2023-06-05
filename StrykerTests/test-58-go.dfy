// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method m_method_9(p_m_method_9_1: real, p_m_method_9_2: real, p_m_method_9_3: real, p_m_method_9_4: real) returns (ret_1: array<real>)
{
	var v_array_17: array<real> := new real[4] [18.28, 12.68, -25.69, 16.59];
	return v_array_17;
}

method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_8(p_m_method_8_1: real) returns (ret_1: seq<array<real>>)
{
	var v_real_5: real, v_real_6: real, v_real_7: real, v_real_8: real, v_real_9: real := 2.96, 12.42, -24.66, -6.64, -24.38;
	match false {
		case _ => {
			var v_array_12: array<real> := new real[3] [-12.52, 25.80, 4.27];
			var v_array_13: array<real> := new real[3] [-24.64, 16.14, -9.74];
			var v_array_14: array<real> := new real[4] [-23.97, -20.57, -5.07, -6.24];
			var v_array_15: array<real> := new real[3] [-24.52, -19.91, 15.39];
			return [v_array_12, v_array_13, v_array_14, v_array_15];
		}
		
	}
	
}

method m_method_7(p_m_method_7_1: real) returns (ret_1: array<bool>)
{
	var v_array_5: array<bool> := new bool[4] [true, false, true, false];
	return v_array_5;
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: real, p_m_method_6_2: real, p_m_method_6_3: int) returns (ret_1: seq<array<bool>>)
{
	var v_array_3: array<bool> := new bool[5] [false, true, true, false, true];
	var v_array_4: array<bool> := new bool[3] [false, true, false];
	return [v_array_3, v_array_4];
}

method m_method_5(p_m_method_5_1: real) returns (ret_1: array<bool>)
{
	var v_real_1: real := 25.07;
	var v_real_2: real := 21.21;
	var v_int_12: int := 2;
	var v_seq_5: seq<array<bool>> := m_method_6(v_real_1, v_real_2, v_int_12);
	var v_seq_6: seq<array<bool>> := v_seq_5;
	var v_int_13: int := (2.43).Floor;
	var v_real_3: real := -16.77;
	var v_array_6: array<bool> := m_method_7(v_real_3);
	return (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_13]) else (v_array_6));
}

method m_method_4(p_m_method_4_1: bool) returns (ret_1: (bool, int))
{
	var v_bool_int_1: (bool, int) := (false, 28);
	var v_bool_int_2: (bool, int) := (false, 13);
	var v_bool_int_3: (bool, int) := (false, 17);
	var v_bool_int_4: (bool, int) := (false, 17);
	var v_seq_4: seq<(bool, int)> := [v_bool_int_1, v_bool_int_2, v_bool_int_3, v_bool_int_4];
	var v_int_11: int := 13;
	var v_bool_int_5: (bool, int) := (true, 16);
	return (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_11]) else (v_bool_int_5));
}

method m_method_3(p_m_method_3_1: bool) returns (ret_1: (bool, int))
{
	var v_bool_2: bool := (if (false) then (true) else (false));
	var v_bool_int_6: (bool, int) := m_method_4(v_bool_2);
	return v_bool_int_6;
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

method m_method_2(p_m_method_2_1: array<real>, p_m_method_2_2: char, p_m_method_2_3: int) returns (ret_1: int, ret_2: (bool, int), ret_3: array<bool>, ret_4: char, ret_5: int)
{
	var v_bool_3: bool := (p_m_method_2_1[2] !in map[-12.49 := -29.47, 6.70 := -27.03][-22.76 := -3.74]);
	var v_bool_int_7: (bool, int) := m_method_3(v_bool_3);
	var v_real_4: real := p_m_method_2_1[0];
	var v_array_7: array<bool> := m_method_5(v_real_4);
	return p_m_method_2_3, v_bool_int_7, v_array_7, p_m_method_2_2, p_m_method_2_3;
}

method m_method_1(p_m_method_1_1: array<int>, p_m_method_1_2: int) returns (ret_1: char)
{
	var v_int_7: int := 24;
	var v_int_8: int := 13;
	while (v_int_7 < v_int_8) 
		decreases v_int_8 - v_int_7;
		invariant (v_int_7 <= v_int_8);
	{
		v_int_7 := (v_int_7 + 1);
		if true {
			return 'F';
		}
	}
	assert true;
	expect true;
	return 'c';
}

method m_method_10(p_m_method_10_1: char, p_m_method_10_2: char) returns (ret_1: (real, char))
{
	var v_real_char_21: (real, char) := (-9.56, 'm');
	return v_real_char_21;
}

method m_method_11(p_m_method_11_1: char, p_m_method_11_2: char, p_m_method_11_3: char) returns (ret_1: bool)
{
	var v_char_7: char := 'A';
	var v_bool_4: bool := m_method_12(v_char_7);
	return v_bool_4;
}

method m_method_12(p_m_method_12_1: char) returns (ret_1: bool)
{
	return false;
}

method m_method_13(p_m_method_13_1: char) returns (ret_1: seq<char>)
{
	return ['i', 'O', 'o'];
}

method Main() returns ()
{
	match 0 {
		case 11 => {
			var v_map_1: map<char, map<bool, int>> := (map['n' := map[false := 18, false := 20], 'u' := map[false := 0, false := 22, false := -28, false := 0], 'm' := map[false := 28, false := 17, true := 7, false := 17], 'C' := map[true := 24, true := 5, false := 22, false := 11], 'r' := map[false := 28, false := -9, false := 11]] + map['u' := map[false := 22], 'C' := map[true := 26, false := 19, true := 12]]);
			var v_array_1: array<int> := new int[5] [6, 21, 0, 7, 3];
			var v_array_2: array<int> := v_array_1;
			var v_int_9: int := 25;
			var v_char_1: char := m_method_1(v_array_2, v_int_9);
			var v_char_2: char := v_char_1;
			var v_map_2: map<bool, int> := (if ((v_char_2 in v_map_1)) then (v_map_1[v_char_2]) else (map[true := 14][false := 13]));
			var v_seq_3: seq<bool> := [true, false, true];
			var v_int_10: int := 22;
			var v_bool_1: bool := !((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_10]) else (true)));
			v_int_10 := (if ((v_bool_1 in v_map_2)) then (v_map_2[v_bool_1]) else (v_int_10));
			var v_real_10: real := -26.47;
			var v_seq_7: seq<array<real>> := m_method_8(v_real_10);
			var v_seq_8: seq<array<real>> := v_seq_7;
			var v_int_14: int := v_array_1[1];
			var v_seq_9: seq<array<real>> := [];
			var v_int_15: int := 29;
			var v_array_16: array<real> := new real[5] [-7.76, 22.65, -10.36, -13.05, -17.65];
			var v_seq_10: seq<array<real>> := v_seq_9;
			var v_int_16: int := (-26 * 14);
			var v_real_11: real := 5.36;
			var v_real_12: real := -19.09;
			var v_real_13: real := -24.91;
			var v_real_14: real := 14.67;
			var v_array_18: array<real> := m_method_9(v_real_11, v_real_12, v_real_13, v_real_14);
			var v_array_19: array<real> := (if (v_bool_1) then ((if ((|v_seq_8| > 0)) then (v_seq_8[v_int_14]) else ((if ((|v_seq_9| > 0)) then (v_seq_9[v_int_15]) else (v_array_16))))) else ((if ((|v_seq_10| > 0)) then (v_seq_10[v_int_16]) else (v_array_18))));
			var v_real_char_1: (real, char) := (18.98, 'j');
			var v_real_char_2: (real, char) := (20.29, 'Y');
			var v_real_char_3: (real, char) := (-27.55, 'r');
			var v_real_char_4: (real, char) := (-23.07, 'l');
			var v_real_char_5: (real, char) := (1.02, 'k');
			var v_real_char_6: (real, char) := (-12.44, 'D');
			var v_real_char_7: (real, char) := (13.85, 'Q');
			var v_real_char_8: (real, char) := (-12.78, 'j');
			var v_seq_11: seq<map<(real, char), char>> := [map[v_real_char_1 := 'I', v_real_char_2 := 'I', v_real_char_3 := 'E'], map[v_real_char_4 := 'U', v_real_char_5 := 'Y', v_real_char_6 := 'k'], map[v_real_char_7 := 'G', v_real_char_8 := 'b']];
			var v_int_17: int := 26;
			var v_real_char_9: (real, char) := (-2.46, 'T');
			var v_real_char_10: (real, char) := (8.15, 'C');
			var v_real_char_11: (real, char) := (18.21, 'k');
			var v_real_char_12: (real, char) := (6.97, 'V');
			var v_real_char_13: (real, char) := (-1.31, 'F');
			var v_real_char_14: (real, char) := (-2.93, 'l');
			var v_real_char_15: (real, char) := (-22.82, 'B');
			var v_map_3: map<(real, char), char> := ((if ((|v_seq_11| > 0)) then (v_seq_11[v_int_17]) else (map[v_real_char_9 := 'F'])) + (map[v_real_char_10 := 'g', v_real_char_11 := 'a'] + map[v_real_char_12 := 'Q', v_real_char_13 := 'K', v_real_char_14 := 'w', v_real_char_15 := 'd']));
			var v_real_char_16: (real, char) := (-15.11, 'S');
			var v_real_char_17: (real, char) := (-27.86, 'P');
			var v_real_char_18: (real, char) := (-19.88, 'C');
			var v_real_char_19: (real, char) := (-29.69, 't');
			var v_real_char_20: (real, char) := (6.96, 'D');
			var v_seq_13: seq<(real, char)> := ([v_real_char_16] + [v_real_char_17, v_real_char_18, v_real_char_19, v_real_char_20]);
			var v_seq_12: seq<int> := [6, 11];
			var v_int_18: int := 8;
			var v_int_19: int := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_18]) else (1));
			var v_char_3: char := 's';
			var v_char_4: char := 'Y';
			var v_real_char_22: (real, char) := m_method_10(v_char_3, v_char_4);
			var v_real_char_23: (real, char) := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_19]) else (v_real_char_22));
			var v_char_5: char := (if ((v_real_char_23 in v_map_3)) then (v_map_3[v_real_char_23]) else (v_real_char_16.1));
			var v_int_20: int := v_array_1[1];
			var v_int_21: int, v_bool_int_8: (bool, int), v_array_20: array<bool>, v_char_6: char, v_int_22: int := m_method_2(v_array_19, v_char_5, v_int_20);
			v_int_20, v_bool_int_8, v_array_20, v_char_3, v_array_1[2] := v_int_21, v_bool_int_8, v_array_20, v_char_6, v_int_22;
			var v_char_10: char := v_real_char_15.1;
			var v_map_4: map<char, char> := map['s' := 'I', 'x' := 'b', 's' := 'c', 'P' := 'g', 'O' := 'N'];
			var v_char_8: char := 'l';
			var v_char_11: char := (if ((v_char_8 in v_map_4)) then (v_map_4[v_char_8]) else ('x'));
			var v_array_21: array<int> := new int[4] [9, 0, 20, 1];
			var v_array_22: array<int> := v_array_21;
			var v_int_23: int := 27;
			var v_char_9: char := m_method_1(v_array_22, v_int_23);
			var v_char_12: char := v_char_9;
			var v_bool_5: bool := m_method_11(v_char_10, v_char_11, v_char_12);
			if (match 'z' {
				case _ => v_bool_1
			}) {
				match v_real_char_6.1 {
					case _ => {
						return ;
					}
					
				}
				
				if v_bool_1 {
					assert true;
					expect true;
					return ;
				} else {
					var v_seq_24: seq<char> := ['U', 'F', 'y'];
					var v_seq_25: seq<char> := v_seq_24;
					var v_int_40: int := 21;
					var v_int_41: int := safe_index_seq(v_seq_25, v_int_40);
					var v_int_42: int := v_int_41;
					var v_seq_26: seq<char> := (if ((|v_seq_24| > 0)) then (v_seq_24[v_int_42 := 'K']) else (v_seq_24));
					var v_int_43: int := v_int_18;
					var v_map_10: map<char, char> := map['N' := 'B', 'y' := 'X', 'l' := 'V', 'd' := 'E'];
					var v_char_23: char := 'g';
					var v_map_12: map<char, char> := (match 'D' {
						case _ => v_map_10
					});
					var v_char_25: char := v_real_char_11.1;
					var v_map_11: map<char, seq<char>> := map['t' := ['n'], 'K' := ['F', 'E'], 'I' := []];
					var v_char_24: char := 'F';
					var v_seq_27: seq<char> := (if ((v_char_24 in v_map_11)) then (v_map_11[v_char_24]) else (['x']));
					var v_int_44: int := v_int_10;
					v_char_23, v_char_4, v_char_25 := (if (v_bool_1) then (v_char_3) else ((if ((|v_seq_26| > 0)) then (v_seq_26[v_int_43]) else ((if ((v_char_23 in v_map_10)) then (v_map_10[v_char_23]) else ('b')))))), v_real_char_13.1, (if ((v_char_25 in v_map_12)) then (v_map_12[v_char_25]) else ((if ((|v_seq_27| > 0)) then (v_seq_27[v_int_44]) else (v_char_24))));
					return ;
				}
			}
			var v_map_13: map<char, bool> := (if (false) then (map['e' := true, 'w' := false]) else (map['c' := false, 'D' := false, 'v' := false, 's' := true]));
			var v_char_26: char := (if (false) then ('k') else ('N'));
			var v_seq_28: seq<bool> := [];
			var v_int_45: int := 1;
			var v_seq_29: seq<char> := ['i', 'd', 'c', 'Q'];
			var v_int_46: int := 24;
			var v_seq_30: seq<char> := ['l', 'q', 'v', 'K'];
			var v_int_47: int := -27;
			var v_seq_31: seq<char> := v_seq_29;
			var v_int_48: int := (if (v_bool_1) then ((6 / 0)) else ((11 % 29)));
			var v_seq_32: seq<char> := ['m', 'W', 'o'];
			var v_seq_33: seq<char> := v_seq_32;
			var v_int_49: int := 5;
			var v_int_50: int := safe_index_seq(v_seq_33, v_int_49);
			var v_int_51: int := v_int_50;
			var v_seq_34: seq<char> := (if ((|v_seq_32| > 0)) then (v_seq_32[v_int_51 := 'R']) else (v_seq_32));
			var v_int_52: int := |{'v'}|;
			var v_seq_35: seq<bool> := [false, true, true];
			var v_int_53: int := -10;
			var v_seq_36: seq<char> := (match 'j' {
				case _ => []
			});
			var v_array_32: array<char> := new char[5] ['m', 'N', 'I', 'e', 't'];
			var v_int_54: int := v_array_32.Length;
			var v_map_14: map<char, bool> := map['r' := false];
			var v_char_27: char := 'V';
			var v_seq_37: seq<char> := [];
			var v_int_55: int := 28;
			var v_seq_38: seq<map<char, char>> := [map['p' := 'W', 'd' := 'm'], map['p' := 'I', 'K' := 'Y', 'Y' := 'B', 'X' := 'q', 'Y' := 'm']];
			var v_int_56: int := 22;
			var v_seq_39: seq<char> := [];
			var v_int_57: int := -18;
			var v_seq_40: seq<char> := [];
			var v_int_58: int := 22;
			var v_map_16: map<char, char> := (if ((|v_seq_38| > 0)) then (v_seq_38[v_int_56]) else (map['X' := 'r', 's' := 'E', 'x' := 'v']))[(if ((|v_seq_39| > 0)) then (v_seq_39[v_int_57]) else ('b')) := (if ((|v_seq_40| > 0)) then (v_seq_40[v_int_58]) else ('w'))];
			var v_map_15: map<char, char> := (match 'K' {
				case _ => map['q' := 'b', 's' := 'f']
			});
			var v_char_28: char := v_char_4;
			var v_char_29: char := (if ((v_char_28 in v_map_15)) then (v_map_15[v_char_28]) else ((if (false) then ('p') else ('W'))));
			var v_seq_41: seq<char> := ['Z', 'L', 'b'];
			var v_seq_42: seq<char> := v_seq_41;
			var v_int_59: int := 9;
			var v_int_60: int := safe_index_seq(v_seq_42, v_int_59);
			var v_int_61: int := v_int_60;
			var v_seq_43: seq<char> := (if ((|v_seq_41| > 0)) then (v_seq_41[v_int_61 := 's']) else (v_seq_41));
			var v_int_62: int := v_array_1[4];
			var v_seq_44: seq<char> := ((['X', 'W', 'B', 'i'] + []) + v_seq_33);
			var v_map_18: map<char, int> := map['a' := 20, 'u' := 5]['w' := 7];
			var v_char_31: char := v_real_char_5.1;
			var v_map_17: map<char, int> := map['z' := 5, 'O' := 7, 'G' := 8, 'U' := -20, 'L' := 8];
			var v_char_30: char := 'u';
			var v_int_63: int := (if ((v_char_31 in v_map_18)) then (v_map_18[v_char_31]) else ((if ((v_char_30 in v_map_17)) then (v_map_17[v_char_30]) else (16))));
			var v_map_19: map<char, char> := map['q' := 'q', 'z' := 'I', 'G' := 'W', 'I' := 'h'];
			var v_char_32: char := 'H';
			var v_map_20: map<char, char> := map['V' := 'I', 'W' := 'I', 'C' := 'B', 'a' := 'p', 'k' := 'V'];
			var v_char_33: char := 'v';
			v_array_32[4], v_char_28, v_char_31, v_char_33, v_char_4 := (if ((if ((v_char_26 in v_map_13)) then (v_map_13[v_char_26]) else (v_bool_1))) then (v_real_char_8.1) else ((if ((if ((|v_seq_28| > 0)) then (v_seq_28[v_int_45]) else (true))) then ((if ((|v_seq_29| > 0)) then (v_seq_29[v_int_46]) else ('o'))) else ((if ((|v_seq_30| > 0)) then (v_seq_30[v_int_47]) else ('x')))))), (if ((|v_seq_31| > 0)) then (v_seq_31[v_int_48]) else ((if ((|v_seq_34| > 0)) then (v_seq_34[v_int_52]) else ((if (true) then ('u') else ('T')))))), (if ((if ((if ((|v_seq_35| > 0)) then (v_seq_35[v_int_53]) else (true))) then (('z' !in map['U' := 'L', 't' := 'e', 'E' := 'm'])) else ((if (true) then (true) else (true))))) then ((if ((|v_seq_36| > 0)) then (v_seq_36[v_int_54]) else ((if (true) then ('Y') else ('h'))))) else ((if ((if ((v_char_27 in v_map_14)) then (v_map_14[v_char_27]) else (false))) then ((if (false) then ('U') else ('B'))) else ((if ((|v_seq_37| > 0)) then (v_seq_37[v_int_55]) else ('d')))))), (if ((v_char_29 in v_map_16)) then (v_map_16[v_char_29]) else ((if ((|v_seq_43| > 0)) then (v_seq_43[v_int_62]) else (v_real_char_2.1)))), (if ((|v_seq_44| > 0)) then (v_seq_44[v_int_63]) else ((if ((if (true) then (true) else (false))) then ((if ((v_char_32 in v_map_19)) then (v_map_19[v_char_32]) else ('K'))) else ((if ((v_char_33 in v_map_20)) then (v_map_20[v_char_33]) else ('v'))))));
		}
			case _ => {
			var v_map_21: map<char, char> := map['F' := 'z', 'g' := 'R', 'M' := 'V', 'v' := 'I']['G' := 'Z'];
			var v_char_34: char := (match 'G' {
				case 'B' => 'd'
				case 'I' => 'd'
				case _ => 'h'
			});
			var v_seq_45: seq<char> := ['w'];
			var v_int_64: int := 4;
			var v_map_22: map<char, char> := map['h' := 'L', 'S' := 'N', 'P' := 'p', 'G' := 'n'];
			var v_char_35: char := 'q';
			var v_seq_46: seq<char> := [];
			var v_int_65: int := -21;
			var v_map_23: map<char, bool> := map['e' := true, 'T' := false, 'q' := true];
			var v_char_36: char := 'E';
			var v_map_24: map<char, char> := map['H' := 'j'];
			var v_char_37: char := 'o';
			var v_seq_47: seq<char> := ['z', 's', 'o', 'R'];
			var v_int_66: int := 20;
			var v_seq_51: seq<char> := v_seq_47;
			var v_int_70: int := v_int_66;
			var v_int_71: int := safe_index_seq(v_seq_51, v_int_70);
			v_int_66 := v_int_71;
			var v_map_25: map<char, char> := map['n' := 'c'];
			var v_char_38: char := 'l';
			var v_seq_48: seq<char> := [];
			var v_int_67: int := 17;
			var v_map_26: map<char, char> := map['c' := 'G'];
			var v_char_39: char := 'u';
			var v_map_27: map<char, char> := (match 't' {
				case 'y' => map['M' := 'S']
				case 'H' => map['H' := 'V', 'H' := 'F', 'x' := 'U']
				case _ => map['s' := 'X', 'L' := 'N']
			});
			var v_seq_49: seq<char> := [];
			var v_int_68: int := 23;
			var v_char_40: char := (if ((|v_seq_49| > 0)) then (v_seq_49[v_int_68]) else ('C'));
			var v_seq_50: seq<char> := [];
			var v_int_69: int := 29;
			var v_char_41: char, v_char_42: char, v_char_43: char := (match 'x' {
				case 'c' => (if ((v_char_34 in v_map_21)) then (v_map_21[v_char_34]) else ((if ((|v_seq_45| > 0)) then (v_seq_45[v_int_64]) else ('t'))))
				case 'B' => (match 'J' {
					case _ => (if (false) then ('l') else ('Q'))
				})
				case _ => (if ((if ((v_char_36 in v_map_23)) then (v_map_23[v_char_36]) else (false))) then ((if ((v_char_37 in v_map_24)) then (v_map_24[v_char_37]) else ('f'))) else ((if ((|v_seq_47| > 0)) then (v_seq_47[v_int_66]) else ('r'))))
			}), (match 'U' {
				case 'w' => (match 'm' {
					case _ => (match 'X' {
						case _ => 'H'
					})
				})
				case _ => (match 'O' {
					case 'V' => (if ((|v_seq_48| > 0)) then (v_seq_48[v_int_67]) else ('y'))
					case _ => (if ((v_char_39 in v_map_26)) then (v_map_26[v_char_39]) else ('K'))
				})
			}), (match 'o' {
				case 'P' => (if ((v_char_40 in v_map_27)) then (v_map_27[v_char_40]) else ((match 'w' {
					case _ => 'K'
				})))
				case _ => (match 'j' {
					case 'U' => (match 'T' {
						case _ => 'z'
					})
					case 'n' => (match 's' {
						case _ => 'y'
					})
					case _ => (if ((|v_seq_50| > 0)) then (v_seq_50[v_int_69]) else ('c'))
				})
			});
			print "v_char_43", " ", (v_char_43 == 'c'), " ", "v_char_42", " ", (v_char_42 == 'K'), " ", "v_char_41", " ", (v_char_41 == 'z'), "\n";
		}
		
	}
	
}
