// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_2
datatype DT_2<T_3> = DT_2_1 | DT_2_3(DT_2_3_1: T_3, DT_2_3_2: T_3, DT_2_3_3: T_3)
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

method m_method_2(p_m_method_2_1: int, p_m_method_2_2: DT_2<real>) returns (ret_1: DT_1<array<real>, (bool, int)>)
	requires ((p_m_method_2_2.DT_2_3? && ((10.18 < p_m_method_2_2.DT_2_3_1 < 10.38) && (-27.47 < p_m_method_2_2.DT_2_3_2 < -27.27) && (-2.74 < p_m_method_2_2.DT_2_3_3 < -2.54))) && (p_m_method_2_1 == 27));
	ensures (((p_m_method_2_2.DT_2_3? && ((10.18 < p_m_method_2_2.DT_2_3_1 < 10.38) && (-27.47 < p_m_method_2_2.DT_2_3_2 < -27.27) && (-2.74 < p_m_method_2_2.DT_2_3_3 < -2.54))) && (p_m_method_2_1 == 27)) ==> ((ret_1.DT_1_2? && ((ret_1 == DT_1_2)))));
{
	var v_int_22: int := 24;
	var v_int_23: int := (match 9 {
		case 25 => 27
		case _ => 10
	});
	while (v_int_22 < v_int_23) 
		decreases v_int_23 - v_int_22;
		invariant (v_int_22 <= v_int_23);
	{
		v_int_22 := (v_int_22 + 1);
		var v_char_5: char := (match 8 {
			case _ => 'y'
		});
		var v_int_24: int, v_bool_3: bool, v_int_25: int, v_int_26: int := (if (true) then (5) else (-21)), (5 in map[17 := 2, 22 := -27, 26 := 21, 11 := 16]), p_m_method_2_1, v_int_23;
		if (match 28 {
			case _ => true
		}) {
			var v_int_28: int, v_int_29: int := p_m_method_2_1, v_int_23;
			for v_int_27 := v_int_28 to v_int_29 
				invariant (v_int_29 - v_int_27 >= 0)
			{
				
			}
			var v_DT_1_2_8: DT_1<array<real>, (bool, int)> := DT_1_2;
			var v_DT_1_2_9: DT_1<array<real>, (bool, int)> := DT_1_2;
			var v_seq_4: seq<DT_1<array<real>, (bool, int)>> := [v_DT_1_2_8, v_DT_1_2_9];
			var v_int_30: int := 3;
			var v_DT_1_2_10: DT_1<array<real>, (bool, int)> := DT_1_2;
			return (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_30]) else (v_DT_1_2_10));
		} else {
			
		}
		break;
	}
	assert ((p_m_method_2_2.DT_2_3_3 == -2.64));
	expect ((p_m_method_2_2.DT_2_3_3 == -2.64));
	var v_DT_1_2_11: DT_1<array<real>, (bool, int)> := DT_1_2;
	var v_DT_1_2_12: DT_1<array<real>, (bool, int)> := DT_1_2;
	var v_DT_2_3_7: DT_2<real> := DT_2_3(10.28, -27.37, -2.64);
	print "v_int_23", " ", v_int_23, " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_int_22", " ", v_int_22, " ", "p_m_method_2_2.DT_2_3_3", " ", (p_m_method_2_2.DT_2_3_3 == -2.64), " ", "p_m_method_2_2.DT_2_3_2", " ", (p_m_method_2_2.DT_2_3_2 == -27.37), " ", "v_DT_1_2_12", " ", v_DT_1_2_12, " ", "p_m_method_2_2.DT_2_3_1", " ", (p_m_method_2_2.DT_2_3_1 == 10.28), " ", "v_DT_1_2_11", " ", v_DT_1_2_11, " ", "p_m_method_2_2", " ", (p_m_method_2_2 == v_DT_2_3_7), "\n";
	return (if (false) then (v_DT_1_2_11) else (v_DT_1_2_12));
}

method m_method_1(p_m_method_1_1: char) returns (ret_1: DT_1<array<real>, (bool, int)>)
	requires ((p_m_method_1_1 == 'K'));
	ensures (((p_m_method_1_1 == 'K')) ==> ((ret_1.DT_1_2? && ((ret_1 == DT_1_2)))));
{
	var v_int_19: int, v_int_20: int := 23, -9;
	for v_int_7 := v_int_19 downto v_int_20 
		invariant (v_int_7 - v_int_20 >= 0)
	{
		var v_int_8: int := 19;
		var v_int_9: int := 1;
		while (v_int_8 < v_int_9) 
			decreases v_int_9 - v_int_8;
			invariant (v_int_8 <= v_int_9);
		{
			v_int_8 := (v_int_8 + 1);
			if false {
				
			}
			var v_int_11: int, v_int_12: int := 27, 15;
			for v_int_10 := v_int_11 to v_int_12 
				invariant (v_int_12 - v_int_10 >= 0)
			{
				var v_DT_1_2_1: DT_1<array<real>, (bool, int)> := DT_1_2;
				return v_DT_1_2_1;
			}
			assert true;
			expect true;
			var v_int_14: int, v_int_15: int := 24, -2;
			for v_int_13 := v_int_14 to v_int_15 
				invariant (v_int_15 - v_int_13 >= 0)
			{
				
			}
			if false {
				var v_DT_1_2_2: DT_1<array<real>, (bool, int)> := DT_1_2;
				return v_DT_1_2_2;
			}
		}
		if true {
			var v_char_1: char := 'B';
			var v_DT_1_2_3: DT_1<array<real>, (bool, int)> := DT_1_2;
			print "v_char_1", " ", (v_char_1 == 'B'), " ", "v_DT_1_2_3", " ", v_DT_1_2_3, " ", "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 'K'), "\n";
			return v_DT_1_2_3;
		} else {
			var v_char_2: char, v_char_3: char, v_bool_1: bool, v_bool_2: bool, v_int_16: int := 'r', 'w', true, false, 4;
			var v_int_17: int := 21;
			var v_int_18: int := 6;
			while (v_int_17 < v_int_18) 
				decreases v_int_18 - v_int_17;
				invariant (v_int_17 <= v_int_18);
			{
				v_int_17 := (v_int_17 + 1);
				var v_DT_1_2_4: DT_1<array<real>, (bool, int)> := DT_1_2;
				return v_DT_1_2_4;
			}
			var v_DT_1_2_5: DT_1<array<real>, (bool, int)> := DT_1_2;
			return v_DT_1_2_5;
		}
	}
	var v_DT_1_2_6: DT_1<array<real>, (bool, int)> := DT_1_2;
	return v_DT_1_2_6;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_char_4: char := 'K';
	var v_DT_1_2_7: DT_1<array<real>, (bool, int)> := m_method_1(v_char_4);
	var v_seq_3: seq<DT_1<array<real>, (bool, int)>> := [v_DT_1_2_7];
	var v_int_21: int := (18.35).Floor;
	var v_seq_7: seq<DT_1<array<real>, (bool, int)>> := v_seq_3;
	var v_int_35: int := v_int_21;
	var v_int_36: int := safe_index_seq(v_seq_7, v_int_35);
	v_int_21 := v_int_36;
	var v_int_32: int := (4 + 23);
	var v_DT_2_3_1: DT_2<real> := DT_2_3(10.28, -27.37, -2.64);
	var v_DT_2_3_2: DT_2<real> := DT_2_3(12.19, 0.32, 17.34);
	var v_DT_2_3_3: DT_2<real> := DT_2_3(-16.33, -0.67, -9.75);
	var v_DT_2_3_4: DT_2<real> := DT_2_3(-11.12, -0.34, -8.85);
	var v_seq_5: seq<DT_2<real>> := [v_DT_2_3_1, v_DT_2_3_2, v_DT_2_3_3, v_DT_2_3_4];
	var v_int_31: int := 25;
	var v_seq_6: seq<DT_2<real>> := v_seq_5;
	var v_int_33: int := v_int_31;
	var v_int_34: int := safe_index_seq(v_seq_6, v_int_33);
	v_int_31 := v_int_34;
	var v_DT_2_3_5: DT_2<real> := DT_2_3(21.18, -24.15, -11.67);
	var v_DT_2_3_6: DT_2<real> := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_31]) else (v_DT_2_3_5));
	var v_DT_1_2_13: DT_1<array<real>, (bool, int)> := m_method_2(v_int_32, v_DT_2_3_6);
	v_DT_1_2_7 := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_21]) else (v_DT_1_2_13));
	var v_DT_2_3_8: DT_2<real> := DT_2_3(12.19, 0.32, 17.34);
	var v_DT_2_3_9: DT_2<real> := DT_2_3(10.28, -27.37, -2.64);
	var v_DT_2_3_10: DT_2<real> := DT_2_3(10.28, -27.37, -2.64);
	var v_DT_2_3_11: DT_2<real> := DT_2_3(12.19, 0.32, 17.34);
	var v_DT_2_3_12: DT_2<real> := DT_2_3(-16.33, -0.67, -9.75);
	var v_DT_2_3_13: DT_2<real> := DT_2_3(-11.12, -0.34, -8.85);
	var v_DT_2_3_14: DT_2<real> := DT_2_3(10.28, -27.37, -2.64);
	var v_DT_2_3_15: DT_2<real> := DT_2_3(21.18, -24.15, -11.67);
	var v_DT_2_3_16: DT_2<real> := DT_2_3(-11.12, -0.34, -8.85);
	var v_DT_2_3_17: DT_2<real> := DT_2_3(-16.33, -0.67, -9.75);
	print "v_DT_2_3_1.DT_2_3_2", " ", (v_DT_2_3_1.DT_2_3_2 == -27.37), " ", "v_DT_2_3_4.DT_2_3_1", " ", (v_DT_2_3_4.DT_2_3_1 == -11.12), " ", "v_DT_2_3_1.DT_2_3_3", " ", (v_DT_2_3_1.DT_2_3_3 == -2.64), " ", "v_DT_2_3_4.DT_2_3_2", " ", (v_DT_2_3_4.DT_2_3_2 == -0.34), " ", "v_DT_1_2_7", " ", v_DT_1_2_7, " ", "v_DT_2_3_1.DT_2_3_1", " ", (v_DT_2_3_1.DT_2_3_1 == 10.28), " ", "v_DT_2_3_4.DT_2_3_3", " ", (v_DT_2_3_4.DT_2_3_3 == -8.85), " ", "v_int_21", " ", v_int_21, " ", "v_DT_2_3_3.DT_2_3_1", " ", (v_DT_2_3_3.DT_2_3_1 == -16.33), " ", "v_DT_2_3_3.DT_2_3_3", " ", (v_DT_2_3_3.DT_2_3_3 == -9.75), " ", "v_DT_2_3_3.DT_2_3_2", " ", (v_DT_2_3_3.DT_2_3_2 == -0.67), " ", "v_char_4", " ", (v_char_4 == 'K'), " ", "v_DT_2_3_5.DT_2_3_3", " ", (v_DT_2_3_5.DT_2_3_3 == -11.67), " ", "v_DT_2_3_2.DT_2_3_3", " ", (v_DT_2_3_2.DT_2_3_3 == 17.34), " ", "v_DT_2_3_5.DT_2_3_2", " ", (v_DT_2_3_5.DT_2_3_2 == -24.15), " ", "v_DT_2_3_2.DT_2_3_2", " ", (v_DT_2_3_2.DT_2_3_2 == 0.32), " ", "v_DT_2_3_5.DT_2_3_1", " ", (v_DT_2_3_5.DT_2_3_1 == 21.18), " ", "v_DT_2_3_2.DT_2_3_1", " ", (v_DT_2_3_2.DT_2_3_1 == 12.19), " ", "v_DT_2_3_2", " ", (v_DT_2_3_2 == v_DT_2_3_8), " ", "v_DT_2_3_1", " ", (v_DT_2_3_1 == v_DT_2_3_9), " ", "v_seq_5", " ", (v_seq_5 == [v_DT_2_3_10, v_DT_2_3_11, v_DT_2_3_12, v_DT_2_3_13]), " ", "v_int_32", " ", v_int_32, " ", "v_DT_2_3_6", " ", (v_DT_2_3_6 == v_DT_2_3_14), " ", "v_seq_3", " ", v_seq_3, " ", "v_DT_2_3_5", " ", (v_DT_2_3_5 == v_DT_2_3_15), " ", "v_DT_2_3_4", " ", (v_DT_2_3_4 == v_DT_2_3_16), " ", "v_DT_2_3_3", " ", (v_DT_2_3_3 == v_DT_2_3_17), " ", "v_DT_1_2_13", " ", v_DT_1_2_13, " ", "v_int_31", " ", v_int_31, "\n";
	return ;
}
