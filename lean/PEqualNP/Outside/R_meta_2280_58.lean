import Mathlib.Data.List.OfFn
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

-- Bit fourteen supplies the first OR. The first twenty-one rows contain one edge each.
-- The other thirty-seven rows are maximal independent sets.
-- The first hypothesis follows from valid_ofCirc, exists_nf and enc_sat in the LRAT library.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2280_58
    (encodeRows : ∀ (n s : ℕ) (rows : List ℕ) (label : ℕ → Bool) (C : Circuit),
      Monotone2 C → C.size ≤ s → (∀ r ∈ rows, r < 2 ^ n) →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = label r) →
      FormulaSat (enc n s label rows))
    (incident :
      let rows : List ℕ := [16513, 16641, 17409, 16514, 514, 8194, 260, 4100, 8196, 16520, 2056, 4104, 1040, 2064, 8208,
        544, 1056, 4128, 320, 576, 2112, 16511, 16628, 314, 16816, 16925, 17044, 792, 1102,
        17604, 1290, 1548, 18471, 18596, 2338, 18949, 3078, 20100, 20563, 20688, 4370, 21009,
        21392, 5186, 22531, 7426, 24681, 24800, 8488, 25097, 9288, 9992, 26657, 27040, 28737,
        29888, 31233, 32640]
      ¬ FormulaSat (enc 15 25 (fun r => decide (r ∈ rows.take 21)) rows))
    (nonincident :
      let rows : List ℕ := [16513, 16641, 17409, 130, 16898, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208,
        16928, 1056, 4128, 320, 16960, 2112, 16511, 244, 314, 432, 16925, 17044, 17176, 1102,
        1220, 1290, 17932, 18471, 2212, 2338, 18949, 3078, 20100, 20563, 4304, 4370, 21009,
        21392, 5186, 22531, 7426, 24681, 8416, 8488, 25097, 9288, 26376, 26657, 10656, 28737,
        13504, 31233, 32640]
      ¬ FormulaSat (enc 15 25 (fun r => decide (r ∈ rows.take 21)) rows)) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)), x5 = (7 : Fin (14 : ℕ)) ∨ x5 = (9 : Fin (14 : ℕ)) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x8 : Fin (14 : ℕ) → Bool), x3 x8 → (x4.eval (List.ofFn x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x8 (0 : Fin (14 : ℕ)), x8 x5]]) = Bool.true ↔ x2 x8)) → (26 : ℕ) ≤ x4.size := by
  intro edges edge boundary C j hj hmono htest
  let pairs : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11),
        (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let hits := fun x : Fin 14 → Bool => pairs.any fun p => x p.1 && x p.2
  have agree : ∀ u v : Fin 14, (u.val, v.val) ∈ edges ↔ (u, v) ∈ pairs := by
    decide +kernel
  have hit_iff (x : Fin 14 → Bool) : edge x ↔ hits x = true := by
    dsimp only [edge]
    simp_rw [agree]
    simp [hits, List.any_eq_true, Prod.exists]
  let critical := fun x : Fin 14 → Bool =>
    (hits x = true ∧ ∀ i, x i = true → hits (Function.update x i false) = false) ∨
    (hits x = false ∧ ∀ i, x i = false → hits (Function.update x i true) = true)
  have crit_iff (x : Fin 14 → Bool) : boundary x ↔ critical x := by
    simp [boundary, critical, hit_iff]
  let good := fun (k : Fin 14) (rows : List ℕ) =>
    ∀ r ∈ rows,
      let x := fun i : Fin 14 => r.testBit i.val
      r < 2 ^ 15 ∧ r.testBit 14 = (x 0 || x k) ∧ critical x ∧
        (hits x = true ↔ r ∈ rows.take 21)
  have useRows (rows : List ℕ) (valid : good j rows)
      (unsat : ¬ FormulaSat (enc 15 25 (fun r => decide (r ∈ rows.take 21)) rows)) :
      26 ≤ C.size := by
    by_contra short
    apply unsat
    apply encodeRows 15 25 rows _ C hmono (by omega) (fun r hr => (valid r hr).1)
    intro r hr
    let x := fun i : Fin 14 => r.testBit i.val
    obtain ⟨_, hbit, hc, ht⟩ := valid r hr
    have inputs : List.ofFn (fun i : Fin 15 => r.testBit i.val) =
        List.ofFn x ++ [GateOp.or.eval [x 0, x j]] := by
      rw [List.ofFn_succ']
      change List.ofFn x ++ [r.testBit 14] = _
      rw [hbit]
      have hop (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
        cases a <;> cases b <;> rfl
      rw [hop]
    rw [inputs]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      (htest x ((crit_iff x).2 hc)).trans ((hit_iff x).trans ht)
  rcases hj with rfl | rfl
  · apply useRows _ _ incident
    decide +kernel
  · apply useRows _ _ nonincident
    decide +kernel
