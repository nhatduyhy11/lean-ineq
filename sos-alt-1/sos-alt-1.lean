/-
  Hướng thay thế (sos-alt-1): cùng chứng chỉ pqr-SOS như `ineq_proof.lean` nhưng mọi
  bước đại số được tách thành ĐẲNG THỨC RING CÓ TÊN (section 2) — người đọc kiểm chứng
  được bằng khai triển hai vế, không phụ thuộc `grind` opaque cho các Identity.
    F(q,r) := (4q+3)r² + (12−34q)r + q(4q²−5q+4),  q = ab+bc+ca, r = abc, Π = ∏(a²+1).
    10·(VP·Π − Tử) = F(q,r);  các chặn 0 ≤ q ≤ 3, 0 ≤ r, 9r ≤ q², Δ ≥ 0 đều tường minh.
    * q ≤ 1/3 : mọi số hạng của F đều ≥ 0.
    * q = 3   : F = 15(1−r)(5−r) ≥ 0 vì r ≤ 1.
    * 1/3<q<3 : 2·q(87−4q)·(3−q)·F = 2·q(87−4q)·μ·Δ + □² + (4/27)(3−q)³q²(4q−9)².
  Dấu bằng ⟺ (1,1,1), hoán vị của (3,0,0), hoán vị của (1/2,1/2,2).

  Kiểm chứng: Lean v4.35.0 stable (chỉ core, không Mathlib; dùng `grind`).
-/
set_option linter.unusedSectionVars false

section Ineq
variable {α : Type} [Lean.Grind.Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Lean.Grind.OrderedRing α] [Std.LawfulOrderLT α]

/-! ### 1. Các bổ đề sơ cấp tường minh cho trường có thứ tự -/

theorem mnn {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y :=
  Lean.Grind.OrderedRing.mul_nonneg hx hy

theorem mpos {x y : α} (hx : 0 < x) (hy : 0 < y) : 0 < x * y :=
  Lean.Grind.OrderedRing.mul_pos hx hy

theorem sqnn (x : α) : 0 ≤ x ^ 2 :=
  Lean.Grind.OrderedRing.sq_nonneg

theorem add_nn {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y := by
  grind

theorem add3_nn {x y z : α} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 0 ≤ x + y + z :=
  add_nn (add_nn hx hy) hz

theorem cube_nn {x : α} (hx : 0 ≤ x) : 0 ≤ x ^ 3 := by
  have h : x ^ 3 = x * x ^ 2 := by grind
  rw [h]
  exact mnn hx (sqnn x)

theorem lt_mul_pos {x y z : α} (h : x < y) (hz : 0 < z) : x * z < y * z := by
  have := mpos (show 0 < y - x by grind) hz
  grind

theorem nonneg_of_mul_pos_left {c x : α} (hc : 0 < c) (h : 0 ≤ c * x) : 0 ≤ x := by
  by_cases hx : 0 ≤ x
  · exact hx
  · have hlt : x < 0 := by grind
    have hneg : 0 < -x := by grind
    have := mpos hc hneg
    grind

/-- Assoc-shift helper: từ `x * d = a` suy ra `x * (d * P) = a * P`. -/
theorem div_mul_assoc {x a b c : α} (h : x * (a ^ 2 + 1) = a) :
    x * ((a ^ 2 + 1) * ((b ^ 2 + 1) * (c ^ 2 + 1))) = a * ((b ^ 2 + 1) * (c ^ 2 + 1)) := by
  grind

theorem mul_eq_zero' {x y : α} (h : x * y = 0) : x = 0 ∨ y = 0 := by grind

theorem sum_zero {x y z : α} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 0) : z = 0 := by
  grind

theorem sq_eq_zero' (x : α) (h : x ^ 2 = 0) : x = 0 := by
  by_cases hp : 0 < x
  · have := mpos hp hp
    grind
  · by_cases hx : x = 0
    · exact hx
    · have hn : 0 < -x := by grind
      have := mpos hn hn
      grind

/-! ### 2. Các hằng đẳng thức đại số (Pure Ring Identities)
    Con người có thể kiểm tra trực tiếp bằng cách khai triển hai vế. -/

/-- Đồng nhất thức quy đồng mẫu số:
    10 * (VP * Π - Tử_VT) = F(q, r) -/
theorem id_main_reduction (a b c : α) (h : a + b + c = 3) :
    10 * (2 / 5 * (a * b + b * c + c * a + 3 / 4) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1))
      - (a * ((b ^ 2 + 1) * (c ^ 2 + 1)) + b * ((a ^ 2 + 1) * (c ^ 2 + 1)) + c * ((a ^ 2 + 1) * (b ^ 2 + 1))))
    = (4 * (a * b + b * c + c * a) + 3) * (a * b * c) ^ 2
      + (12 - 34 * (a * b + b * c + c * a)) * (a * b * c)
      + (a * b + b * c + c * a) * (4 * (a * b + b * c + c * a) ^ 2 - 5 * (a * b + b * c + c * a) + 4) := by
  have hc : c = 3 - a - b := by grind
  subst hc
  grind

/-- Hằng đẳng thức 1: 3 - q = ((a-b)^2 + (b-c)^2 + (c-a)^2) / 6 khi a+b+c = 3 -/
theorem id_q_le_3 (a b c : α) (h : a + b + c = 3) :
    3 - (a * b + b * c + c * a) = ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 6 := by
  have hc : c = 3 - a - b := by grind
  subst hc
  grind

/-- Hằng đẳng thức 2: q^2 - 9r = ((ab-bc)^2 + (bc-ca)^2 + (ca-ab)^2) / 2 khi a+b+c = 3 -/
theorem id_q2_ge_9r (a b c : α) (h : a + b + c = 3) :
    (a * b + b * c + c * a) ^ 2 - 9 * (a * b * c)
      = ((a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2) / 2 := by
  have hc : c = 3 - a - b := by grind
  subst hc
  grind

/-- Hằng đẳng thức 3: Biểu diễn biệt thức Δ = ((a-b)(b-c)(c-a))^2 theo q và r -/
theorem id_discriminant (a b c : α) (h : a + b + c = 3) :
    9 * (a * b + b * c + c * a) ^ 2 - 4 * (a * b + b * c + c * a) ^ 3
      + (54 * (a * b + b * c + c * a) - 108) * (a * b * c) - 27 * (a * b * c) ^ 2
    = ((a - b) * (b - c) * (c - a)) ^ 2 := by
  have hc : c = 3 - a - b := by grind
  subst hc
  grind

/-- Hằng đẳng thức 4 (Hoàn thành bình phương cho tam thức bậc 2):
    4q^2 - 5q + 4 = (2q - 5/4)^2 + 39/16 -/
theorem id_quad_pos (q : α) :
    4 * q ^ 2 - 5 * q + 4 = (2 * q - 5 / 4) ^ 2 + 39 / 16 := by
  grind

/-- Hằng đẳng thức 5 (Tại biên q = 3):
    F(3, r) = 15 * (1 - r) * (5 - r) -/
theorem id_F_at_q3 (r : α) :
    (4 * (3 : α) + 3) * r ^ 2 + (12 - 34 * (3 : α)) * r + (3 : α) * (4 * (3 : α) ^ 2 - 5 * (3 : α) + 4)
      = 15 * ((1 - r) * (5 - r)) := by
  grind

/-- Hằng đẳng thức 6 (Biểu diễn hệ số μ > 0 khi q > 1/3):
    4q^2 + 69q - 18 = 4*(q - 1/3)^2 + 215/3*(q - 1/3) + 49/9 -/
theorem id_mu_pos (q : α) :
    4 * q ^ 2 + 69 * q - 18 = 4 * (q - 1 / 3) ^ 2 + 215 / 3 * (q - 1 / 3) + 49 / 9 := by
  grind

/-- Hằng đẳng thức 7 (Phân tích SOS trung tâm cho miền 1/3 < q < 3):
    Nhân cả 2 vế của F(q, r) với trọng số dương 2 * q * (87 - 4q) * (3 - q) để hoàn thành bình phương theo r -/
theorem id_sos_certificate (q r : α) :
    (2 * (q * (87 - 4 * q)) * (3 - q))
      * ((4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4))
    = (2 * (q * (87 - 4 * q)) * ((4 * q ^ 2 + 69 * q - 18) / 54))
        * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2)
      + (q * ((87 - 4 * q) * r - (4 * q ^ 2 + 27 * q - 42))) ^ 2
      + (4 / 27 * (3 - q) ^ 3) * q ^ 2 * (4 * q - 9) ^ 2 := by
  grind

/-! ### 3. Chứng minh tường minh các tính chất của (q, r) -/

theorem pqr_bounds_explicit (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3) :
    0 ≤ a * b + b * c + c * a ∧
    a * b + b * c + c * a ≤ 3 ∧
    0 ≤ a * b * c ∧
    9 * (a * b * c) ≤ (a * b + b * c + c * a) ^ 2 ∧
    0 ≤ 9 * (a * b + b * c + c * a) ^ 2 - 4 * (a * b + b * c + c * a) ^ 3
        + (54 * (a * b + b * c + c * a) - 108) * (a * b * c) - 27 * (a * b * c) ^ 2 := by
  have hab : 0 ≤ a * b := mnn ha hb
  have hbc : 0 ≤ b * c := mnn hb hc
  have hca : 0 ≤ c * a := mnn hc ha
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 1. q = ab + bc + ca ≥ 0
    exact add3_nn hab hbc hca
  · -- 2. q ≤ 3 vì 3 - q = ((a-b)^2 + (b-c)^2 + (c-a)^2) / 6 ≥ 0
    have hid := id_q_le_3 a b c h
    have hsum : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 :=
      add3_nn (sqnn (a - b)) (sqnn (b - c)) (sqnn (c - a))
    grind
  · -- 3. r = abc ≥ 0
    exact mnn hab hc
  · -- 4. 9r ≤ q^2 vì q^2 - 9r = ((ab-bc)^2 + (bc-ca)^2 + (ca-ab)^2) / 2 ≥ 0
    have hid := id_q2_ge_9r a b c h
    have hsum : 0 ≤ (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2 :=
      add3_nn (sqnn (a * b - b * c)) (sqnn (b * c - c * a)) (sqnn (c * a - a * b))
    grind
  · -- 5. Δ = ((a-b)(b-c)(c-a))^2 ≥ 0
    rw [id_discriminant a b c h]
    exact sqnn ((a - b) * (b - c) * (c - a))

/-! ### 4. Chứng minh tường minh F(q, r) ≥ 0 -/

theorem F_nonneg_explicit (q r : α) (hq0 : 0 ≤ q) (hq3 : q ≤ 3) (hr : 0 ≤ r)
    (hr9 : 9 * r ≤ q ^ 2)
    (hΔ : 0 ≤ 9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2) :
    0 ≤ (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4) := by
  by_cases h1 : q ≤ 1 / 3
  · -- NHÁNH 1: 0 ≤ q ≤ 1/3 -> Cả 3 số hạng của F(q, r) đều không âm
    have term1 : 0 ≤ (4 * q + 3) * r ^ 2 :=
      mnn (by grind) (sqnn r)
    have term2 : 0 ≤ (12 - 34 * q) * r :=
      mnn (by grind) hr
    have h_quad : 0 ≤ 4 * q ^ 2 - 5 * q + 4 := by
      rw [id_quad_pos q]
      exact add_nn (sqnn (2 * q - 5 / 4)) (by grind)
    have term3 : 0 ≤ q * (4 * q ^ 2 - 5 * q + 4) :=
      mnn hq0 h_quad
    exact add3_nn term1 term2 term3

  · -- Khi q > 1/3
    by_cases h3 : q = 3
    · -- NHÁNH 2: q = 3 -> F(3, r) = 15 * (1 - r) * (5 - r) ≥ 0 (do 9r ≤ 9 => r ≤ 1)
      subst h3
      rw [id_F_at_q3 r]
      have hr1 : r ≤ 1 := by grind
      have h_prod : 0 ≤ (1 - r) * (5 - r) := mnn (by grind) (by grind)
      exact mnn (by grind) h_prod

    · -- NHÁNH 3: 1/3 < q < 3 -> Dùng phân tích SOS tường minh (id_sos_certificate)
      have hq_pos : 0 < q := by grind
      have hs_pos : 0 < 3 - q := by grind
      have h87_pos : 0 < 87 - 4 * q := by grind
      have hc2_pos : 0 < q * (87 - 4 * q) := mpos hq_pos h87_pos
      have h_weight_pos : 0 < 2 * (q * (87 - 4 * q)) * (3 - q) :=
        mpos (by grind) hs_pos

      -- Chứng minh tường minh hệ số μ = (4q^2 + 69q - 18) / 54 > 0
      have h_mu_num : 0 ≤ 4 * q ^ 2 + 69 * q - 18 := by
        rw [id_mu_pos q]
        have p1 : 0 ≤ 4 * (q - 1 / 3) ^ 2 := mnn (by grind) (sqnn (q - 1 / 3))
        have p2 : 0 ≤ 215 / 3 * (q - 1 / 3) := mnn (by grind) (by grind)
        exact add3_nn p1 p2 (by grind)

      -- Đánh giá 3 số hạng không âm ở vế phải của chứng chỉ SOS
      have sos_term1 : 0 ≤ (2 * (q * (87 - 4 * q)) * ((4 * q ^ 2 + 69 * q - 18) / 54))
          * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2) := by
        have h_coeff : 0 ≤ 2 * (q * (87 - 4 * q)) * ((4 * q ^ 2 + 69 * q - 18) / 54) :=
          mnn (by grind) (by grind)
        exact mnn h_coeff hΔ

      have sos_term2 : 0 ≤ (q * ((87 - 4 * q) * r - (4 * q ^ 2 + 27 * q - 42))) ^ 2 :=
        sqnn _

      have sos_term3 : 0 ≤ (4 / 27 * (3 - q) ^ 3) * q ^ 2 * (4 * q - 9) ^ 2 := by
        have h_s3 : 0 ≤ 4 / 27 * (3 - q) ^ 3 := mnn (by grind) (cube_nn (by grind))
        exact mnn (mnn h_s3 (sqnn q)) (sqnn (4 * q - 9))

      -- Cộng 3 số hạng không âm của VP để suy ra Weight * F(q, r) ≥ 0
      have h_weighted_F : 0 ≤ (2 * (q * (87 - 4 * q)) * (3 - q))
          * ((4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4)) := by
        rw [id_sos_certificate q r]
        exact add3_nn sos_term1 sos_term2 sos_term3

      -- Khử nhân tử dương Weight > 0 để thu được F(q, r) ≥ 0
      exact nonneg_of_mul_pos_left h_weight_pos h_weighted_F

/-! ### 5. Phân loại dấu bằng (equality cases) -/

/-- Nếu `a+b+c = 3`, `ab+bc+ca = 9/4`, `abc = 1/2` thì mỗi số `a, b, c`
là nghiệm của tam thức `(t - 2) * (t - 1/2) ^ 2`. -/
theorem cubic_roots (a b c q r : α) (habc : a + b + c = 3) (hq : a * b + b * c + c * a = q)
    (hr : a * b * c = r) (hqr : q = 9 / 4) (hrr : r = 1 / 2) :
    (a - 2) * (a - 1 / 2) ^ 2 = 0 ∧ (b - 2) * (b - 1 / 2) ^ 2 = 0 ∧ (c - 2) * (c - 1 / 2) ^ 2 = 0 := by
  subst hqr
  subst hrr
  have ha2 : a ^ 2 * (a + b + c - 3) = 0 := by rw [habc]; grind
  have hb2 : b ^ 2 * (a + b + c - 3) = 0 := by rw [habc]; grind
  have hc2 : c ^ 2 * (a + b + c - 3) = 0 := by rw [habc]; grind
  grind

/-- Trong biến `(q, r)`: `F = 0` chỉ xảy ra tại `(0, 0)`, `(3, 1)`, `(9/4, 1/2)`. -/
theorem F_zero_cases (q r : α) (hq0 : 0 ≤ q) (hq3 : q ≤ 3) (hr : 0 ≤ r)
    (hr9 : 9 * r ≤ q ^ 2)
    (hΔ : 0 ≤ 9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2)
    (hF : (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4) = 0) :
    (q = 0 ∧ r = 0) ∨ (q = 3 ∧ r = 1) ∨ (q = 9 / 4 ∧ r = 1 / 2) := by
  by_cases h1 : q ≤ 1 / 3
  · -- NHÁNH 1: q ≤ 1/3 — cả 3 số hạng của F đều ≥ 0, tổng = 0 → số hạng thứ 3 > 0 → mâu thuẫn
    left
    have hquad_pos : 0 < 4 * q ^ 2 - 5 * q + 4 := by
      rw [id_quad_pos q]
      have hs : 0 ≤ (2 * q - 5 / 4) ^ 2 := sqnn _
      grind
    have e1 : 0 ≤ (4 * q + 3) * r ^ 2 := mnn (by grind) (sqnn r)
    have e2 : 0 ≤ (12 - 34 * q) * r := mnn (by grind) hr
    have e3 : 0 ≤ q * (4 * q ^ 2 - 5 * q + 4) := mnn hq0 (by grind)
    have hq : q = 0 := by
      by_cases hq' : q = 0
      · exact hq'
      · have hqp : 0 < q := by grind
        have hpp : 0 < q * (4 * q ^ 2 - 5 * q + 4) := mpos hqp hquad_pos
        grind
    subst hq
    refine ⟨rfl, ?_⟩
    grind
  · have h1' : 1 / 3 < q := by grind
    by_cases h3 : q = 3
    · -- NHÁNH 2: q = 3 — F = 15(1−r)(5−r) = 0 và r ≤ 1 → r = 1
      right; left
      subst h3
      have hr1 : r ≤ 1 := by grind
      have hF15 : 15 * ((1 - r) * (5 - r)) = 0 := by
        rw [← id_F_at_q3 r]
        exact hF
      refine ⟨rfl, ?_⟩
      by_cases hr' : r = 1
      · exact hr'
      · have hp : 0 < (1 - r) * (5 - r) := mpos (by grind) (by grind)
        grind
    · -- NHÁNH 3: 1/3 < q < 3 — trọng số·F = t1 + t2 + t3 = 0 → t3 = 0 → q = 9/4 → r = 1/2
      right; right
      have hs : 0 < 3 - q := by grind
      have hqp : 0 < q := by grind
      have hc2 : 0 < q * (87 - 4 * q) := mpos hqp (by grind)
      have hμ : 0 ≤ 4 * q ^ 2 + 69 * q - 18 := by
        rw [id_mu_pos q]
        exact add3_nn (mnn (by grind) (sqnn (q - 1 / 3))) (mnn (by grind) (by grind))
          (by grind)
      have t1 : 0 ≤ 2 * (q * (87 - 4 * q)) * ((4 * q ^ 2 + 69 * q - 18) / 54)
          * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2) :=
        mnn (mnn (by grind) (by grind)) hΔ
      have t2 : 0 ≤ (q * ((87 - 4 * q) * r - (4 * q ^ 2 + 27 * q - 42))) ^ 2 := sqnn _
      have t3 : 0 ≤ (4 / 27 * (3 - q) ^ 3) * q ^ 2 * (4 * q - 9) ^ 2 := by
        have hc3 : 0 ≤ 4 / 27 * (3 - q) ^ 3 := mnn (by grind) (cube_nn (by grind))
        exact mnn (mnn hc3 (sqnn q)) (sqnn (4 * q - 9))
      have hLHS : (2 * (q * (87 - 4 * q)) * (3 - q))
          * ((4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4)) = 0 := by
        rw [hF]
        grind
      have hsplit : 2 * (q * (87 - 4 * q)) * ((4 * q ^ 2 + 69 * q - 18) / 54)
          * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2)
          + (q * ((87 - 4 * q) * r - (4 * q ^ 2 + 27 * q - 42))) ^ 2
          + (4 / 27 * (3 - q) ^ 3) * q ^ 2 * (4 * q - 9) ^ 2 = 0 :=
        (id_sos_certificate q r).symm.trans hLHS
      have t3z : (4 / 27 * (3 - q) ^ 3) * q ^ 2 * (4 * q - 9) ^ 2 = 0 :=
        sum_zero t1 t2 t3 hsplit
      have hq94 : q = 9 / 4 := by
        have hcubepos : 0 < (3 - q) ^ 3 := by
          have := mpos (mpos hs hs) hs
          grind
        have hq2pos : 0 < q ^ 2 := by
          have := mpos hqp hqp
          grind
        have h27 : 0 < 4 / 27 * (3 - q) ^ 3 * q ^ 2 := by
          have hprod : 0 < (3 - q) ^ 3 * q ^ 2 := mpos hcubepos hq2pos
          grind
        rcases mul_eq_zero' t3z with hz | hz
        · grind
        · have h9 : 4 * q - 9 = 0 := sq_eq_zero' _ hz
          grind
      subst hq94
      refine ⟨rfl, ?_⟩
      have hrfac : (r - 1 / 2) * (r - 39 / 8) = 0 := by grind
      rcases mul_eq_zero' hrfac with h | h <;> grind

/-- Trường hợp dấu bằng: đúng tại `(1,1,1)`, các hoán vị của `(3,0,0)` và `(1/2,1/2,2)`. -/
theorem equality_cases (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3)
    (heq : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) = 2 / 5 * (a * b + b * c + c * a + 3 / 4)) :
    (a = 1 ∧ b = 1 ∧ c = 1) ∨
    (a = 3 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 3 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 3) ∨
    (a = 1 / 2 ∧ b = 1 / 2 ∧ c = 2) ∨ (a = 1 / 2 ∧ b = 2 ∧ c = 1 / 2) ∨ (a = 2 ∧ b = 1 / 2 ∧ c = 1 / 2) := by
  obtain ⟨hq0, hq3, hr0, hr9, hΔ⟩ := pqr_bounds_explicit a b c ha hb hc h
  have hid := id_main_reduction a b c h
  have pa : 0 < a ^ 2 + 1 := by have := sqnn a; grind
  have pb : 0 < b ^ 2 + 1 := by have := sqnn b; grind
  have pc : 0 < c ^ 2 + 1 := by have := sqnn c; grind
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
  -- dấu bằng  ⇒  F(q, r) = 0
  have hF0 : (4 * (a * b + b * c + c * a) + 3) * (a * b * c) ^ 2
      + (12 - 34 * (a * b + b * c + c * a)) * (a * b * c)
      + (a * b + b * c + c * a) * (4 * (a * b + b * c + c * a) ^ 2 - 5 * (a * b + b * c + c * a) + 4) = 0 := by
    have hm : (x + y + z) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1))
        = 2 / 5 * (a * b + b * c + c * a + 3 / 4) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) := by
      rw [heq]
    grind
  have hcases := F_zero_cases _ _ hq0 hq3 hr0 hr9 hΔ hF0
  rcases hcases with ⟨hq, hr⟩ | ⟨hq, hr⟩ | ⟨hq, hr⟩
  · -- q = 0: ab = bc = ca = 0 → có đúng một biến bằng 3
    have habc0 : a * b = 0 ∧ b * c = 0 ∧ c * a = 0 := by
      have s1 : 0 ≤ a * b := mnn ha hb
      have s2 : 0 ≤ b * c := mnn hb hc
      have s3 : 0 ≤ c * a := mnn hc ha
      grind
    obtain ⟨hab, hbc, hca⟩ := habc0
    rcases mul_eq_zero' hab with h1 | h1 <;> rcases mul_eq_zero' hbc with h2 | h2 <;>
      rcases mul_eq_zero' hca with h3 | h3 <;> grind
  · -- q = 3: 3 − q = Σ(a−b)²/6 = 0 → a = b = c = 1
    left
    have hidq := id_q_le_3 a b c h
    have s1 : (a - b) ^ 2 = 0 := by
      have t1 : 0 ≤ (a - b) ^ 2 := sqnn _
      have t2 : 0 ≤ (b - c) ^ 2 := sqnn _
      have t3 : 0 ≤ (c - a) ^ 2 := sqnn _
      grind
    have s2 : (b - c) ^ 2 = 0 := by
      have t1 : 0 ≤ (a - b) ^ 2 := sqnn _
      have t2 : 0 ≤ (b - c) ^ 2 := sqnn _
      have t3 : 0 ≤ (c - a) ^ 2 := sqnn _
      grind
    have u1 : a - b = 0 := sq_eq_zero' _ s1
    have u2 : b - c = 0 := sq_eq_zero' _ s2
    grind
  · -- q = 9/4, r = 1/2: a, b, c là nghiệm của (x−2)(x−1/2)²
    obtain ⟨ra, rb, rc⟩ := cubic_roots a b c _ _ h hq hr rfl rfl
    have fa : a = 2 ∨ a = 1 / 2 := by
      rcases mul_eq_zero' ra with hx | hx
      · left; grind
      · right; have := sq_eq_zero' _ hx; grind
    have fb : b = 2 ∨ b = 1 / 2 := by
      rcases mul_eq_zero' rb with hx | hx
      · left; grind
      · right; have := sq_eq_zero' _ hx; grind
    have fc : c = 2 ∨ c = 1 / 2 := by
      rcases mul_eq_zero' rc with hx | hx
      · left; grind
      · right; have := sq_eq_zero' _ hx; grind
    rcases fa with h1 | h1 <;> rcases fb with h2 | h2 <;> rcases fc with h3 | h3 <;> grind

/-- Ngược lại, BDT là đẳng thức tại từng điểm liệt kê ở trên. -/
theorem eq_111 : (1:α) / (1 ^ 2 + 1) + 1 / (1 ^ 2 + 1) + 1 / (1 ^ 2 + 1) = 2 / 5 * (1 * 1 + 1 * 1 + 1 * 1 + 3 / 4) := by grind
theorem eq_300 : (3:α) / (3 ^ 2 + 1) + 0 / (0 ^ 2 + 1) + 0 / (0 ^ 2 + 1) = 2 / 5 * (3 * 0 + 0 * 0 + 0 * 3 + 3 / 4) := by grind
theorem eq_030 : (0:α) / (0 ^ 2 + 1) + 3 / (3 ^ 2 + 1) + 0 / (0 ^ 2 + 1) = 2 / 5 * (0 * 3 + 3 * 0 + 0 * 0 + 3 / 4) := by grind
theorem eq_003 : (0:α) / (0 ^ 2 + 1) + 0 / (0 ^ 2 + 1) + 3 / (3 ^ 2 + 1) = 2 / 5 * (0 * 0 + 0 * 3 + 3 * 0 + 3 / 4) := by grind
theorem eq_hh2 : (1 / 2:α) / ((1 / 2) ^ 2 + 1) + (1 / 2) / ((1 / 2) ^ 2 + 1) + 2 / (2 ^ 2 + 1) = 2 / 5 * ((1 / 2) * (1 / 2) + (1 / 2) * 2 + 2 * (1 / 2) + 3 / 4) := by grind
theorem eq_h2h : (1 / 2:α) / ((1 / 2) ^ 2 + 1) + 2 / (2 ^ 2 + 1) + (1 / 2) / ((1 / 2) ^ 2 + 1) = 2 / 5 * ((1 / 2) * 2 + 2 * (1 / 2) + (1 / 2) * (1 / 2) + 3 / 4) := by grind
theorem eq_2hh : (2:α) / (2 ^ 2 + 1) + (1 / 2) / ((1 / 2) ^ 2 + 1) + (1 / 2) / ((1 / 2) ^ 2 + 1) = 2 / 5 * (2 * (1 / 2) + (1 / 2) * (1 / 2) + (1 / 2) * 2 + 3 / 4) := by grind

/-! ### 6. Định lý chính (Main Theorem) -/

theorem main_ineq (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) := by
  obtain ⟨hq0, hq3, hr0, hr9, hΔ⟩ := pqr_bounds_explicit a b c ha hb hc h
  have hF := F_nonneg_explicit (a * b + b * c + c * a) (a * b * c) hq0 hq3 hr0 hr9 hΔ
  have hid := id_main_reduction a b c h

  -- Mẫu số chung Π = (a^2 + 1)(b^2 + 1)(c^2 + 1) > 0
  have pa : 0 < a ^ 2 + 1 := by have := sqnn a; grind
  have pb : 0 < b ^ 2 + 1 := by have := sqnn b; grind
  have pc : 0 < c ^ 2 + 1 := by have := sqnn c; grind
  have hPi : 0 < (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := mpos (mpos pa pb) pc

  -- Quy đồng từng phân thức
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

  -- Suy ra (x + y + z) * Π ≤ VP * Π từ F(q, r) ≥ 0
  have hN : (x + y + z) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1))
      ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) := by
    grind

  -- Chia hai vế cho Π > 0
  by_cases hle : x + y + z ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4)
  · exact hle
  · have hlt : 2 / 5 * (a * b + b * c + c * a + 3 / 4) < x + y + z := by grind
    have := lt_mul_pos hlt hPi
    grind

/-- Bridge khớp signature của Challenge.lean -/
theorem ineq_challenge (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1)
      ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) :=
  main_ineq a b c ha hb hc habc

/-- Phân loại đẳng thức — khớp `ineq_challenge_eq` trong Challenge. -/
theorem ineq_challenge_eq (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 3)
    (heq : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1)
      = 2 / 5 * (a * b + b * c + c * a + 3 / 4)) :
    (a = 1 ∧ b = 1 ∧ c = 1) ∨
    (a = 3 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 3 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 3) ∨
    (a = 1 / 2 ∧ b = 1 / 2 ∧ c = 2) ∨ (a = 1 / 2 ∧ b = 2 ∧ c = 1 / 2) ∨ (a = 2 ∧ b = 1 / 2 ∧ c = 1 / 2) :=
  equality_cases a b c ha hb hc habc heq

end Ineq

/-- Instantiation over ℚ (core `Rat`). -/
theorem main_ineq_rat (a b c : Rat) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) :=
  main_ineq a b c ha hb hc h