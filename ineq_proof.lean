/-
  Bất đẳng thức:  a,b,c ≥ 0, a+b+c = 3  ⟹
      a/(a²+1) + b/(b²+1) + c/(c²+1) ≤ (2/5)(ab+bc+ca+3/4).

  Chứng minh (p=a+b+c=3, q=ab+bc+ca, r=abc):
    10·(VP·Π − Tử) = F(q,r) := (4q+3)r² + (12−34q)r + q(4q²−5q+4),   Π = ∏(a²+1) > 0.
    Δ := (a−b)²(b−c)²(c−a)² = 9q²−4q³+(54q−108)r−27r² ≥ 0,  0 ≤ q ≤ 3,  0 ≤ r,  9r ≤ q².
    * q ≤ 1/3 : mọi số hạng của F đều ≥ 0.
    * q = 3   : F = 15(1−r)(5−r) ≥ 0 vì r ≤ 1.
    * 1/3 < q < 3 : chứng chỉ (s = 3−q, c₂ = q(87−4q)/2, μ = (4q²+69q−18)/54)
         2c₂·s·F = 2c₂·μ·Δ + (q((87−4q)r − (4q²+27q−42)))² + (4/27)·s³·q²·(4q−9)²  ≥ 0.
    Dấu bằng ⟺ (a,b,c) = (1,1,1), hoán vị của (3,0,0), hoán vị của (1/2,1/2,2).

  Kiểm chứng: Lean v4.35.0 stable (chỉ core, không Mathlib; dùng `grind`).
  Định lý được chứng minh cho MỌI trường có thứ tự `α` (tổng quát hoá ℚ, ℝ).
-/
set_option linter.unusedSectionVars false

section Ineq
variable {α : Type} [Lean.Grind.Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Lean.Grind.OrderedRing α] [Std.LawfulOrderLT α]

theorem mnn {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := Lean.Grind.OrderedRing.mul_nonneg hx hy
theorem mpos {x y : α} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := Lean.Grind.OrderedRing.mul_pos hx hy
theorem sqnn (x : α) : 0 ≤ x ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
theorem cube_nonneg {x : α} (h : 0 ≤ x) : 0 ≤ x ^ 3 := by
  have := mnn h (sqnn x)
  grind
theorem lt_mul_pos {x y z : α} (h : x < y) (hz : 0 < z) : x * z < y * z := by
  have := mpos (show 0 < y - x by grind) hz
  grind
theorem mul_eq_zero' {x y : α} (h : x * y = 0) : x = 0 ∨ y = 0 := by grind
theorem sum_zero {x y z : α} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 0) : z = 0 := by grind
theorem sq_eq_zero' (x : α) (h : x ^ 2 = 0) : x = 0 := by
  by_cases hp : 0 < x
  · have := mpos hp hp
    grind
  · by_cases hx : x = 0
    · exact hx
    · have hn : 0 < -x := by grind
      have := mpos hn hn
      grind

/-- Assoc-shift helper: from `x * d = a` deduce `x * (d * P) = a * P`. -/
theorem div_mul_assoc {x a b c : α} (h : x * (a ^ 2 + 1) = a) :
    x * ((a ^ 2 + 1) * ((b ^ 2 + 1) * (c ^ 2 + 1))) = a * ((b ^ 2 + 1) * (c ^ 2 + 1)) := by
  grind

/-- If `a+b+c = 3`, `ab+bc+ca = 9/4`, `abc = 1/2`, then each of `a, b, c`
is a root of `(t - 2) * (t - 1/2) ^ 2`. -/
theorem cubic_roots (a b c q r : α) (habc : a + b + c = 3) (hq : a * b + b * c + c * a = q)
    (hr : a * b * c = r) (hqr : q = 9 / 4) (hrr : r = 1 / 2) :
    (a - 2) * (a - 1 / 2) ^ 2 = 0 ∧ (b - 2) * (b - 1 / 2) ^ 2 = 0 ∧ (c - 2) * (c - 1 / 2) ^ 2 = 0 := by
  subst hqr
  subst hrr
  have ha2 : a ^ 2 * (a + b + c - 3) = 0 := by rw [habc]; grind
  have hb2 : b ^ 2 * (a + b + c - 3) = 0 := by rw [habc]; grind
  have hc2 : c ^ 2 * (a + b + c - 3) = 0 := by rw [habc]; grind
  grind

/-- Core lemma in the (q,r) variables, q = ab+bc+ca, r = abc (with a+b+c = 3). -/
theorem F_nonneg (q r : α) (hq0 : 0 ≤ q) (hq3 : q ≤ 3) (hr : 0 ≤ r)
    (hr9 : 9 * r ≤ q ^ 2)
    (hΔ : 0 ≤ 9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2) :
    0 ≤ (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4) := by
  by_cases h1 : q ≤ 1 / 3
  · -- small q: every term is nonnegative
    have e1 : 0 ≤ (4 * q + 3) * r ^ 2 :=
      mnn (by grind) (sqnn r)
    have e2 : 0 ≤ (12 - 34 * q) * r := mnn (by grind) hr
    have e3 : 0 ≤ q * (4 * q ^ 2 - 5 * q + 4) :=
      mnn hq0 (by
        have := Lean.Grind.OrderedRing.sq_nonneg (R := α) (a := 2 * q - 5 / 4)
        grind)
    grind
  · have h1' : 1 / 3 < q := by grind
    by_cases h3 : q = 3
    · -- q = 3 : F = 15 (1 - r)(5 - r) and r ≤ 1
      subst h3
      have hr1 : r ≤ 1 := by grind
      have : 0 ≤ (1 - r) * (5 - r) := mnn (by grind) (by grind)
      grind
    · have hs : 0 < 3 - q := by grind
      have hq : 0 < q := by grind
      have hc2 : 0 < q * (87 - 4 * q) := mpos hq (by grind)
      have hμ : 0 ≤ 4 * q ^ 2 + 69 * q - 18 := by
        have : 0 ≤ q ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
        grind
      -- the certificate
      have cert : 2 * (q * (87 - 4 * q)) * ((3 - q) * ((4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4)))
          = 2 * (q * (87 - 4 * q)) * (((4 * q ^ 2 + 69 * q - 18) / 54) * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2))
            + (q * ((87 - 4 * q) * r - (4 * q ^ 2 + 27 * q - 42))) ^ 2
            + 4 / 27 * (3 - q) ^ 3 * q ^ 2 * (4 * q - 9) ^ 2 := by
        grind
      have t1 : 0 ≤ 2 * (q * (87 - 4 * q)) * (((4 * q ^ 2 + 69 * q - 18) / 54) * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2)) :=
        mnn (by grind) (mnn (by grind) hΔ)
      have t2 : 0 ≤ (q * ((87 - 4 * q) * r - (4 * q ^ 2 + 27 * q - 42))) ^ 2 :=
        Lean.Grind.OrderedRing.sq_nonneg
      have t3 : 0 ≤ 4 / 27 * (3 - q) ^ 3 * q ^ 2 * (4 * q - 9) ^ 2 :=
        mnn (mnn (mnn (by grind) (cube_nonneg (by grind))) Lean.Grind.OrderedRing.sq_nonneg) Lean.Grind.OrderedRing.sq_nonneg
      have hprod : 0 ≤ (2 * (q * (87 - 4 * q)) * (3 - q)) * ((4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4)) := by
        grind
      by_cases hF : 0 ≤ (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4)
      · exact hF
      have hlt : (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4) < 0 := by grind
      have hpos : 0 < 2 * (q * (87 - 4 * q)) * (3 - q) := mpos (by grind) hs
      have := lt_mul_pos hlt hpos
      grind

/-- Facts about q = ab+bc+ca, r = abc when a+b+c = 3, a,b,c ≥ 0. -/
theorem pqr_facts (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3) :
    0 ≤ a * b + b * c + c * a ∧ a * b + b * c + c * a ≤ 3 ∧ 0 ≤ a * b * c ∧
    9 * (a * b * c) ≤ (a * b + b * c + c * a) ^ 2 ∧
    0 ≤ 9 * (a * b + b * c + c * a) ^ 2 - 4 * (a * b + b * c + c * a) ^ 3
        + (54 * (a * b + b * c + c * a) - 108) * (a * b * c) - 27 * (a * b * c) ^ 2 := by
  have hab : 0 ≤ a * b := mnn ha hb
  have hbc : 0 ≤ b * c := mnn hb hc
  have hca : 0 ≤ c * a := mnn hc ha
  have hr : 0 ≤ a * b * c := mnn hab hc
  have s1 : 0 ≤ (a - b) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  have s2 : 0 ≤ (b - c) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  have s3 : 0 ≤ (c - a) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  have t1 : 0 ≤ (a * b - b * c) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  have t2 : 0 ≤ (b * c - c * a) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  have t3 : 0 ≤ (c * a - a * b) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  have hc' : c = 3 - a - b := by grind
  refine ⟨by grind, ?_, hr, ?_, ?_⟩
  · -- q ≤ 3  (since 9 = (a+b+c)^2 ≥ 3q)
    subst hc'; grind
  · -- 9 r ≤ q^2  (since q^2 - 3 p r = 1/2 Σ (ab-bc)^2)
    subst hc'; grind
  · -- Δ = ((a-b)(b-c)(c-a))^2 ≥ 0
    have e : 9 * (a * b + b * c + c * a) ^ 2 - 4 * (a * b + b * c + c * a) ^ 3
        + (54 * (a * b + b * c + c * a) - 108) * (a * b * c) - 27 * (a * b * c) ^ 2
        = ((a - b) * (b - c) * (c - a)) ^ 2 := by
      subst hc'; grind
    have : 0 ≤ ((a - b) * (b - c) * (c - a)) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
    grind

/-- Polynomial identity: 10 (R·Π − N) = F(q,r). -/
theorem poly_id (a b c : α) (h : a + b + c = 3) :
    10 * (2 / 5 * (a * b + b * c + c * a + 3 / 4) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1))
      - (a * ((b ^ 2 + 1) * (c ^ 2 + 1)) + b * ((a ^ 2 + 1) * (c ^ 2 + 1)) + c * ((a ^ 2 + 1) * (b ^ 2 + 1))))
    = (4 * (a * b + b * c + c * a) + 3) * (a * b * c) ^ 2 + (12 - 34 * (a * b + b * c + c * a)) * (a * b * c)
      + (a * b + b * c + c * a) * (4 * (a * b + b * c + c * a) ^ 2 - 5 * (a * b + b * c + c * a) + 4) := by
  have hc' : c = 3 - a - b := by grind
  subst hc'
  grind

/-- The inequality. -/
theorem main_ineq (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pqr_facts a b c ha hb hc h
  have hF := F_nonneg _ _ h1 h2 h3 h4 h5
  have hid := poly_id a b c h
  have pa : 0 < a ^ 2 + 1 := by
    have : 0 ≤ a ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
    grind
  have pb : 0 < b ^ 2 + 1 := by
    have : 0 ≤ b ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
    grind
  have pc : 0 < c ^ 2 + 1 := by
    have : 0 ≤ c ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
    grind
  have hPi : 0 < (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := mpos (mpos pa pb) pc
  -- x = a/(a^2+1) etc.
  have hx : a / (a ^ 2 + 1) * (a ^ 2 + 1) = a := Lean.Grind.Field.div_mul_cancel (by grind)
  have hy : b / (b ^ 2 + 1) * (b ^ 2 + 1) = b := Lean.Grind.Field.div_mul_cancel (by grind)
  have hz : c / (c ^ 2 + 1) * (c ^ 2 + 1) = c := Lean.Grind.Field.div_mul_cancel (by grind)
  generalize a / (a ^ 2 + 1) = x at hx ⊢
  generalize b / (b ^ 2 + 1) = y at hy ⊢
  generalize c / (c ^ 2 + 1) = z at hz ⊢
  have e1 : x * ((a ^ 2 + 1) * ((b ^ 2 + 1) * (c ^ 2 + 1))) = a * ((b ^ 2 + 1) * (c ^ 2 + 1)) :=
    div_mul_assoc hx
  have e2 : y * ((b ^ 2 + 1) * ((a ^ 2 + 1) * (c ^ 2 + 1))) = b * ((a ^ 2 + 1) * (c ^ 2 + 1)) :=
    div_mul_assoc hy
  have e3 : z * ((c ^ 2 + 1) * ((a ^ 2 + 1) * (b ^ 2 + 1))) = c * ((a ^ 2 + 1) * (b ^ 2 + 1)) :=
    div_mul_assoc hz
  -- (x+y+z)·Π = N ≤ R·Π
  have hN : (x + y + z) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1))
      ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) := by
    grind
  by_cases hle : x + y + z ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4)
  · exact hle
  · have hlt : 2 / 5 * (a * b + b * c + c * a + 3 / 4) < x + y + z := by grind
    have := lt_mul_pos hlt hPi
    grind

/-! ## Equality cases -/

/-- In the (q,r)-variables, F = 0 happens only at (0,0), (3,1), (9/4,1/2). -/
theorem F_zero_cases (q r : α) (hq0 : 0 ≤ q) (hq3 : q ≤ 3) (hr : 0 ≤ r)
    (hr9 : 9 * r ≤ q ^ 2)
    (hΔ : 0 ≤ 9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2)
    (hF : (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4) = 0) :
    (q = 0 ∧ r = 0) ∨ (q = 3 ∧ r = 1) ∨ (q = 9 / 4 ∧ r = 1 / 2) := by
  by_cases h1 : q ≤ 1 / 3
  · left
    have e1 : 0 ≤ (4 * q + 3) * r ^ 2 :=
      mnn (by grind) (sqnn r)
    have e2 : 0 ≤ (12 - 34 * q) * r := mnn (by grind) hr
    have hpos : 0 < 4 * q ^ 2 - 5 * q + 4 := by
      have := Lean.Grind.OrderedRing.sq_nonneg (R := α) (a := 2 * q - 5 / 4)
      grind
    have e3 : 0 ≤ q * (4 * q ^ 2 - 5 * q + 4) := mnn hq0 (by grind)
    have hq : q = 0 := by
      by_cases hq' : q = 0
      · exact hq'
      · have : 0 < q := by grind
        have := mpos this hpos
        grind
    subst hq
    refine ⟨rfl, ?_⟩
    grind
  · have h1' : 1 / 3 < q := by grind
    by_cases h3 : q = 3
    · right; left
      subst h3
      have hr1 : r ≤ 1 := by grind
      refine ⟨rfl, ?_⟩
      by_cases hr' : r = 1
      · exact hr'
      · have hp : 0 < (1 - r) * (5 - r) := mpos (by grind) (by grind)
        grind
    · right; right
      have hs : 0 < 3 - q := by grind
      have hq : 0 < q := by grind
      have hc2 : 0 < q * (87 - 4 * q) := mpos hq (by grind)
      have hμ : 0 ≤ 4 * q ^ 2 + 69 * q - 18 := by
        have : 0 ≤ q ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
        grind
      have cert : 2 * (q * (87 - 4 * q)) * ((3 - q) * ((4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4)))
          = 2 * (q * (87 - 4 * q)) * (((4 * q ^ 2 + 69 * q - 18) / 54) * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2))
            + (q * ((87 - 4 * q) * r - (4 * q ^ 2 + 27 * q - 42))) ^ 2
            + 4 / 27 * (3 - q) ^ 3 * q ^ 2 * (4 * q - 9) ^ 2 := by
        grind
      have t1 : 0 ≤ 2 * (q * (87 - 4 * q)) * (((4 * q ^ 2 + 69 * q - 18) / 54) * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2)) :=
        mnn (by grind) (mnn (by grind) hΔ)
      have t2 : 0 ≤ (q * ((87 - 4 * q) * r - (4 * q ^ 2 + 27 * q - 42))) ^ 2 :=
        Lean.Grind.OrderedRing.sq_nonneg
      have t3 : 0 ≤ 4 / 27 * (3 - q) ^ 3 * q ^ 2 * (4 * q - 9) ^ 2 :=
        mnn (mnn (mnn (by grind) (cube_nonneg (by grind))) Lean.Grind.OrderedRing.sq_nonneg) Lean.Grind.OrderedRing.sq_nonneg
      have hLHS : 2 * (q * (87 - 4 * q)) * ((3 - q) * ((4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4))) = 0 := by
        rw [hF]
        grind
      have t3z : 4 / 27 * (3 - q) ^ 3 * q ^ 2 * (4 * q - 9) ^ 2 = 0 :=
        sum_zero t1 t2 t3 (cert.symm.trans hLHS)
      have hq94 : q = 9 / 4 := by
        have h27 : 0 < 4 / 27 * (3 - q) ^ 3 * q ^ 2 := by
          have a1 : 0 < (3 - q) ^ 3 := by
            have := mpos (mpos hs hs) hs
            grind
          have a2 : 0 < q ^ 2 := by
            have := mpos hq hq
            grind
          have := mpos a1 a2
          grind
        have hz : (4 * q - 9) ^ 2 = 0 := by
          rcases mul_eq_zero' t3z with h | h
          · grind
          · exact h
        have := sq_eq_zero' _ hz
        grind
      subst hq94
      refine ⟨rfl, ?_⟩
      have : (r - 1 / 2) * (r - 39 / 8) = 0 := by grind
      rcases mul_eq_zero' this with h | h <;> grind

/-- The inequality's equality cases: exactly (1,1,1), perms of (3,0,0), perms of (1/2,1/2,2). -/
theorem equality_cases (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3)
    (heq : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) = 2 / 5 * (a * b + b * c + c * a + 3 / 4)) :
    (a = 1 ∧ b = 1 ∧ c = 1) ∨
    (a = 3 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 3 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 3) ∨
    (a = 1 / 2 ∧ b = 1 / 2 ∧ c = 2) ∨ (a = 1 / 2 ∧ b = 2 ∧ c = 1 / 2) ∨ (a = 2 ∧ b = 1 / 2 ∧ c = 1 / 2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pqr_facts a b c ha hb hc h
  have hid := poly_id a b c h
  have pa : 0 < a ^ 2 + 1 := by
    have : 0 ≤ a ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
    grind
  have pb : 0 < b ^ 2 + 1 := by
    have : 0 ≤ b ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
    grind
  have pc : 0 < c ^ 2 + 1 := by
    have : 0 ≤ c ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
    grind
  have hx : a / (a ^ 2 + 1) * (a ^ 2 + 1) = a := Lean.Grind.Field.div_mul_cancel (by grind)
  have hy : b / (b ^ 2 + 1) * (b ^ 2 + 1) = b := Lean.Grind.Field.div_mul_cancel (by grind)
  have hz : c / (c ^ 2 + 1) * (c ^ 2 + 1) = c := Lean.Grind.Field.div_mul_cancel (by grind)
  generalize a / (a ^ 2 + 1) = x at hx heq
  generalize b / (b ^ 2 + 1) = y at hy heq
  generalize c / (c ^ 2 + 1) = z at hz heq
  have e1 : x * ((a ^ 2 + 1) * ((b ^ 2 + 1) * (c ^ 2 + 1))) = a * ((b ^ 2 + 1) * (c ^ 2 + 1)) :=
    div_mul_assoc hx
  have e2 : y * ((b ^ 2 + 1) * ((a ^ 2 + 1) * (c ^ 2 + 1))) = b * ((a ^ 2 + 1) * (c ^ 2 + 1)) :=
    div_mul_assoc hy
  have e3 : z * ((c ^ 2 + 1) * ((a ^ 2 + 1) * (b ^ 2 + 1))) = c * ((a ^ 2 + 1) * (b ^ 2 + 1)) :=
    div_mul_assoc hz
  -- equality  ⇒  F(q,r) = 0
  have hF0 : (4 * (a * b + b * c + c * a) + 3) * (a * b * c) ^ 2 + (12 - 34 * (a * b + b * c + c * a)) * (a * b * c)
      + (a * b + b * c + c * a) * (4 * (a * b + b * c + c * a) ^ 2 - 5 * (a * b + b * c + c * a) + 4) = 0 := by
    have hm : (x + y + z) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1))
        = 2 / 5 * (a * b + b * c + c * a + 3 / 4) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) := by
      rw [heq]
    grind
  have hcases := F_zero_cases _ _ h1 h2 h3 h4 h5 hF0
  have hc' : c = 3 - a - b := by grind
  rcases hcases with ⟨hq, hr⟩ | ⟨hq, hr⟩ | ⟨hq, hr⟩
  · -- q = 0 : two of the variables vanish
    have hab : a * b = 0 := by
      have := mnn ha hb
      have := mnn hb hc
      have := mnn hc ha
      grind
    have hbc : b * c = 0 := by
      have := mnn ha hb
      have := mnn hb hc
      have := mnn hc ha
      grind
    have hca : c * a = 0 := by
      have := mnn ha hb
      have := mnn hb hc
      have := mnn hc ha
      grind
    rcases mul_eq_zero' hab with h1 | h1 <;> rcases mul_eq_zero' hbc with h2 | h2 <;>
      rcases mul_eq_zero' hca with h3 | h3 <;> grind
  · -- q = 3 : a = b = c = 1
    left
    have s1 : (a - b) ^ 2 = 0 := by
      have t1 : 0 ≤ (a - b) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      have t2 : 0 ≤ (b - c) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      have t3 : 0 ≤ (c - a) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      subst hc'
      grind
    have s2 : (b - c) ^ 2 = 0 := by
      have t1 : 0 ≤ (a - b) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      have t2 : 0 ≤ (b - c) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      have t3 : 0 ≤ (c - a) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      subst hc'
      grind
    have u1 := sq_eq_zero' _ s1
    have u2 := sq_eq_zero' _ s2
    grind
  · -- q = 9/4, r = 1/2 : a,b,c are roots of (x-2)(x-1/2)^2
    obtain ⟨ra, rb, rc⟩ := cubic_roots a b c _ _ h hq hr rfl rfl
    have fa : a = 2 ∨ a = 1 / 2 := by
      rcases mul_eq_zero' ra with h | h
      · left; grind
      · right; have := sq_eq_zero' _ h; grind
    have fb : b = 2 ∨ b = 1 / 2 := by
      rcases mul_eq_zero' rb with h | h
      · left; grind
      · right; have := sq_eq_zero' _ h; grind
    have fc : c = 2 ∨ c = 1 / 2 := by
      rcases mul_eq_zero' rc with h | h
      · left; grind
      · right; have := sq_eq_zero' _ h; grind
    rcases fa with h1 | h1 <;> rcases fb with h2 | h2 <;> rcases fc with h3 | h3 <;> grind

/-! Conversely, the inequality is an equality at each of these points. -/
theorem eq_111 : (1:α) / (1 ^ 2 + 1) + 1 / (1 ^ 2 + 1) + 1 / (1 ^ 2 + 1) = 2 / 5 * (1 * 1 + 1 * 1 + 1 * 1 + 3 / 4) := by grind
theorem eq_300 : (3:α) / (3 ^ 2 + 1) + 0 / (0 ^ 2 + 1) + 0 / (0 ^ 2 + 1) = 2 / 5 * (3 * 0 + 0 * 0 + 0 * 3 + 3 / 4) := by grind
theorem eq_030 : (0:α) / (0 ^ 2 + 1) + 3 / (3 ^ 2 + 1) + 0 / (0 ^ 2 + 1) = 2 / 5 * (0 * 3 + 3 * 0 + 0 * 0 + 3 / 4) := by grind
theorem eq_003 : (0:α) / (0 ^ 2 + 1) + 0 / (0 ^ 2 + 1) + 3 / (3 ^ 2 + 1) = 2 / 5 * (0 * 0 + 0 * 3 + 3 * 0 + 3 / 4) := by grind
theorem eq_hh2 : (1 / 2:α) / ((1 / 2) ^ 2 + 1) + (1 / 2) / ((1 / 2) ^ 2 + 1) + 2 / (2 ^ 2 + 1) = 2 / 5 * ((1 / 2) * (1 / 2) + (1 / 2) * 2 + 2 * (1 / 2) + 3 / 4) := by grind
theorem eq_h2h : (1 / 2:α) / ((1 / 2) ^ 2 + 1) + 2 / (2 ^ 2 + 1) + (1 / 2) / ((1 / 2) ^ 2 + 1) = 2 / 5 * ((1 / 2) * 2 + 2 * (1 / 2) + (1 / 2) * (1 / 2) + 3 / 4) := by grind
theorem eq_2hh : (2:α) / (2 ^ 2 + 1) + (1 / 2) / ((1 / 2) ^ 2 + 1) + (1 / 2) / ((1 / 2) ^ 2 + 1) = 2 / 5 * (2 * (1 / 2) + (1 / 2) * (1 / 2) + (1 / 2) * 2 + 3 / 4) := by grind

/-! ### Bridges cho https://comparator.live.lean-lang.org

Tên + signature phải khớp **chính xác** với các theorem trong `Challenge.lean`
(xem `problem.md`, mục "Challenge"). Comparator đối chiếu statement đã chứng minh
với statement tin cậy trong challenge. -/

/-- Bất đẳng thức chính — khớp `ineq_challenge` trong challenge. -/
theorem ineq_challenge (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1)
      ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) :=
  main_ineq a b c ha hb hc habc

/-- (Tuỳ chọn) Phân loại đẳng thức — khớp `ineq_challenge_eq` trong challenge. -/
theorem ineq_challenge_eq (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3)
    (heq : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1)
      = 2 / 5 * (a * b + b * c + c * a + 3 / 4)) :
    (a = 1 ∧ b = 1 ∧ c = 1) ∨
    (a = 3 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 3 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 3) ∨
    (a = 1 / 2 ∧ b = 1 / 2 ∧ c = 2) ∨ (a = 1 / 2 ∧ b = 2 ∧ c = 1 / 2) ∨ (a = 2 ∧ b = 1 / 2 ∧ c = 1 / 2) :=
  equality_cases a b c ha hb hc h heq

end Ineq

/-- Instantiation over ℚ (core `Rat`). -/
theorem main_ineq_rat (a b c : Rat) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) :=
  main_ineq a b c ha hb hc h
