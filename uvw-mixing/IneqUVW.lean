/-
  Bất đẳng thức:  a,b,c ≥ 0, a+b+c = 3  ⟹
      a/(a²+1) + b/(b²+1) + c/(c²+1) ≤ (2/5)(ab+bc+ca+3/4).

  LỜI GIẢI THEO HƯỚNG UVW / DỒN BIẾN (phiên bản "uvw-mixing").
  Xem `plans/uvw-exploration.md` cho phân tích đầy đủ.

  Sau khi quy đồng (p = 3, q = ab+bc+ca, r = abc):
      10·(VP·Π − N) = F(q,r) := (4q+3)r² + (12−34q)r + q(4q²−5q+4),  Π = ∏(a²+1) > 0.
  F là parabol LổN LÊN theo r, nên cấu trúc chứng minh theo uvw gồm 3 miền:

    * q ≤ 1/3       : F đơn điệu TĂNG theo r ≥ 0 ⟹ min tại biên r = 0 (1 biến = 0)
                      ⟹ F(q,0) = q(4q²−5q+4) ≥ 0.
    * 1/3 ≤ q ≤ 2/5 : MIỀN ĐỈNH. Hoàn thành bình phương:
                        (4q+3)·F = ((4q+3)r − 17q + 6)² + 4·Q4(q),
                      Q4 = 4q⁴−2q³−72q²+54q−9 > 0 trên miền (chứng minh bằng
                      nội suy dây + T lồi, hệ số hữu tỷ chính xác).
    * 2/5 ≤ q ≤ 3   : đỉnh KHÔNG khả thi (Δ(q,r*) < 0 — bậc 5, xem plans/);
                      về nguyên tắc min rơi vào biên Δ = 0 (2 biến bằng nhau,
                      nơi F triệt tiêu đúng tại (1,1,1), (½,½,2), (3,0,0)).
                      Trên trường có thứ tự TRỪU TƯỢNG α, điểm biên Δ=0 có thể
                      VÔ TỶ (ví dụ α = ℚ: r₂ = (−54+24√6)/54 ∉ ℚ) nên bước
                      "min ở biên" được đóng gói thành chứng chỉ đại số
                        2c₂sF = 2c₂μΔ + (…)² + (4/27)s³q²(4q−9)²,
                      chính là "bóng đại số" của lập luận uvw (xem plans).

  Kiểm chứng: Lean v4.35.0 stable (chỉ core, không Mathlib; dùng `grind`).
-/
set_option linter.unusedSectionVars false

section Uvw
variable {α : Type} [Lean.Grind.Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Lean.Grind.OrderedRing α] [Std.LawfulOrderLT α]

/-! ## Helpers kiểu ordered-field (core không có Mathlib) -/

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
theorem sq_eq_zero' (x : α) (h : x ^ 2 = 0) : x = 0 := by
  by_cases hp : 0 < x
  · have := mpos hp hp
    grind
  · by_cases hx : x = 0
    · exact hx
    · have hn : 0 < -x := by grind
      have := mpos hn hn
      grind

/-! ## Hai factorization biên (bản chất "tiếp tuyến / 1 biến" của hướng uvw)

  Chỉ là identity đa thức (không cần giả lập mệnh đề), dùng làm tài liệu:
    * 2 biến bằng nhau b = c = x, a = 3−2x  ⟹  tử số phân tích HẾT SẠCH:
        12·x·(x−1)²·(2x−1)²·(x−2)  — không còn dư P(x); dấu x(x−2) ≤ 0 trên [0,2].
    * 1 biến = 0 (c = 0, a+b = 3, q = a(3−a)):
        a(a−3)·(4q²−5q+4),  với 4q²−5q+4 = 4(q−5/8)²+39/16 > 0. -/

theorem two_equal_factorization (x : α) :
    10 * ((3 - 2*x) * (x^2+1) + 2*x*((3-2*x)^2+1)
      - 2/5*(x^2 + 2*x*(3-2*x) + 3/4)*(x^2+1)*((3-2*x)^2+1))
    = 12*x*(x-1)^2*(2*x-1)^2*(x-2) := by
  grind

theorem one_zero_factorization (a : α) :
    10 * (a*((3-a)^2+1) + (3-a)*(a^2+1)
      - 2/5*(a*(3-a) + 3/4)*(a^2+1)*((3-a)^2+1))
    = a*(a-3)*(4*(a*(3-a))^2 - 5*(a*(3-a)) + 4) := by
  grind

/-! ## Lõi uvw: giá trị nhỏ nhất của F theo r — ba miền q

  F(q,r) là parabol bậc 2 theo r với hệ số trưởng 4q+3 > 0:
    * biên r = 0       (ứng với "một biến = 0"),
    * đỉnh  r* = (17q−6)/(4q+3)  (ứng với giá trị F nhỏ nhất tuyệt đối),
    * biên Δ = 0       (ứng với "hai biến bằng nhau").
  Đỉnh khả thi ⟺ 6/17 ≤ q ≤ 2/5 (khi đó Q4(q) ≥ 0); ngoài miền đó chỉ cần biên. -/

/-- Miền biên r = 0: F(q,0) = q·(4q²−5q+4) ≥ 0, vì 4q²−5q+4 = 4(q−5/4)²+39/16 > 0. -/
theorem F_zero_nonneg (q : α) (hq : 0 ≤ q) :
    0 ≤ q * (4*q^2 - 5*q + 4) := by
  have hs : 0 ≤ (2*q - 5/4)^2 := sqnn (2*q - 5/4)
  exact mnn hq (by grind)

/-- `Q̃(s) = 4s⁴ + 50s³ − 16050s² + 20000s + 49375 > 0` trên `[0,1]`.

  Đây là `50625·Q4((s+5)/15)` với `Q4 = 4q⁴−2q³−72q²+54q−9`, `s = 15q − 5`
  (đoạn `[1/3, 2/5]` ↦ `[0,1]`). Chứng minh bằng nội suy dây tại 0 và 1 —
  toàn bộ hệ số NGUYÊN:
    Q̃ = [(1−s)·49375 + s·53379] + s(s−1)·T̃,   T̃(s) = 4s² + 54s − 15996,
  chord ≥ min(Q̃(0), Q̃(1)) = 49375 > 0 (tổ hợp lồi), còn `T̃ ≤ 0` trên [0,1] vì
    T̃ = (1−s)·(−15996) + s·(−15938) + 4s(s−1)
  là tổ hợp lồi của hai số âm cộng thêm 4s(s−1) ≤ 0. -/
theorem Qs_band_pos (s : α) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    0 < 4*s^4 + 50*s^3 - 16050*s^2 + 20000*s + 49375 := by
  have w1 : 0 ≤ 1 - s := by grind
  have w2 : 0 ≤ s := h0
  have w3 : 0 ≤ s * (1 - s) := mnn w2 w1
  -- T̃ ≤ 0 trên [0,1]
  have tle : 4*s^2 + 54*s - 15996 ≤ 0 := by
    have p1 : 0 ≤ (1 - s) * 15996 := mnn w1 (by grind)
    have p2 : 0 ≤ s * 15938 := mnn w2 (by grind)
    have p3 : 0 ≤ 4 * s * (1 - s) := by grind
    grind
  -- nội suy dây cho Q̃
  have cid : 4*s^4 + 50*s^3 - 16050*s^2 + 20000*s + 49375
      = (1-s)*49375 + s*53379 + s*(s-1)*(4*s^2 + 54*s - 15996) := by
    grind
  have cA : 0 < (1-s)*49375 + s*53379 := by
    have e : (1-s)*49375 + s*53379 = 49375 + 4004*s := by grind
    grind
  have cB : 0 ≤ s*(s-1)*(4*s^2 + 54*s - 15996) := by
    have m1 : 0 ≤ -(s - 1) := by grind
    have m2 : 0 ≤ -(4*s^2 + 54*s - 15996) := by grind
    have m3 : 0 ≤ s * ((-(s - 1)) * (-(4*s^2 + 54*s - 15996))) := mnn w2 (mnn m1 m2)
    grind
  grind

/-- MIỀN ĐỈNH `1/3 ≤ q ≤ 2/5`: hoàn thành bình phương
    (4q+3)·F = ((4q+3)r − 17q + 6)² + 4·Q4(q) ≥ 0,  vì Q4 > 0 ở đây
  (qua biến tỉ lệ s = 15q − 5 và bổ đề `Qs_band_pos`). -/
theorem F_vertex_band (q r : α) (h1 : 1/3 ≤ q) (h2 : q ≤ 2/5) :
    0 ≤ (4*q+3)*r^2 + (12-34*q)*r + q*(4*q^2-5*q+4) := by
  have hband := Qs_band_pos (15*q - 5) (by grind) (by grind)
  have hrel : 50625 * (4*q^4 - 2*q^3 - 72*q^2 + 54*q - 9)
      = 4*(15*q-5)^4 + 50*(15*q-5)^3 - 16050*(15*q-5)^2
        + 20000*(15*q-5) + 49375 := by
    grind
  have hQ : 0 < 4*q^4 - 2*q^3 - 72*q^2 + 54*q - 9 := by
    by_cases hQ' : 0 < 4*q^4 - 2*q^3 - 72*q^2 + 54*q - 9
    · exact hQ'
    · have hn : 4*q^4 - 2*q^3 - 72*q^2 + 54*q - 9 ≤ 0 := by grind
      have hp : 0 ≤ 50625 * -(4*q^4 - 2*q^3 - 72*q^2 + 54*q - 9) :=
        mnn (by grind) (by grind)
      grind
  have vid : (4*q+3)*((4*q+3)*r^2 + (12-34*q)*r + q*(4*q^2-5*q+4))
      = ((4*q+3)*r - 17*q + 6)^2 + 4*(4*q^4 - 2*q^3 - 72*q^2 + 54*q - 9) := by
    grind
  have hsq : 0 ≤ ((4*q+3)*r - 17*q + 6)^2 := Lean.Grind.OrderedRing.sq_nonneg
  have hpos : 0 < ((4*q+3)*r - 17*q + 6)^2 + 4*(4*q^4 - 2*q^3 - 72*q^2 + 54*q - 9) := by grind
  have hp : 0 < 4*q + 3 := by grind
  by_cases hF : 0 ≤ (4*q+3)*r^2 + (12-34*q)*r + q*(4*q^2-5*q+4)
  · exact hF
  · have hlt : (4*q+3)*r^2 + (12-34*q)*r + q*(4*q^2-5*q+4) < 0 := by grind
    have hcon : ((4*q+3)*r^2 + (12-34*q)*r + q*(4*q^2-5*q+4)) * (4*q+3)
        < 0 * (4*q+3) :=
      lt_mul_pos hlt hp
    grind

/-- Miền q ≤ 1/3: F đơn điệu tăng theo r ≥ 0, mọi số hạng ≥ 0. -/
theorem F_pos_small (q r : α) (hq : 0 ≤ q) (hr : 0 ≤ r) (h : q ≤ 1/3) :
    0 ≤ (4*q+3)*r^2 + (12-34*q)*r + q*(4*q^2-5*q+4) := by
  have e1 : 0 ≤ (4*q+3) * r^2 := mnn (by grind) (sqnn r)
  have e2 : 0 ≤ (12-34*q) * r := mnn (by grind) hr
  have e3 : 0 ≤ q * (4*q^2-5*q+4) := F_zero_nonneg q hq
  grind

/-- Miền q = 3: F(3,r) = 15(1−r)(5−r) ≥ 0 khi r ≤ 1 (từ 9r ≤ q² = 9). -/
theorem F_eq3 (r : α) (hr1 : r ≤ 1) :
    0 ≤ (4*3+3)*r^2 + (12-34*3)*r + 3*(4*3^2-5*3+4) := by
  have : 0 ≤ (1 - r) * (5 - r) := mnn (by grind) (by grind)
  grind

/-- MIỀN LỚN `2/5 < q < 3`: chứng chỉ SOS — "bóng đại số" của lập luận uvw
  (min phải ở biên Δ = 0, và chứng chỉ khẳng định F ≥ (hệ số)·Δ nên chỉ còn
  biên, đã kiểm qua hai factorization ở trên). Với s = 3−q, c₂ = q(87−4q)/2,
  μ = (4q²+69q−18)/54 ≥ 0:
      2c₂·s·F = 2c₂·μ·Δ + (q((87−4q)r − (4q²+27q−42)))² + (4/27)·s³·q²·(4q−9)². -/
theorem F_pos_cert (q r : α) (hq0 : 0 ≤ q) (h1 : 2/5 < q) (h3 : q < 3) (hr : 0 ≤ r)
    (hΔ : 0 ≤ 9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2) :
    0 ≤ (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4) := by
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
  have hprod : 0 ≤ (2 * (q * (87 - 4 * q)) * (3 - q)) * ((4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4)) := by
    grind
  by_cases hF : 0 ≤ (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4)
  · exact hF
  have hlt : (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4) < 0 := by grind
  have hpos : 0 < 2 * (q * (87 - 4 * q)) * (3 - q) := mpos (by grind) hs
  have := lt_mul_pos hlt hpos
  grind

/-- **Bổ đề uvw hợp nhất**: với mọi (q,r) khả thi (0 ≤ q ≤ 3, 0 ≤ r, 9r ≤ q², Δ ≥ 0)
  ta có F(q,r) ≥ 0 — case split theo miền đỉnh khả thi `[1/3, 2/5]`. -/
theorem F_nonneg_uvw (q r : α) (hq0 : 0 ≤ q) (hq3 : q ≤ 3) (hr : 0 ≤ r)
    (hr9 : 9 * r ≤ q ^ 2)
    (hΔ : 0 ≤ 9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2) :
    0 ≤ (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4) := by
  by_cases hA : q ≤ 1/3
  · exact F_pos_small q r hq0 hr hA
  by_cases hB : q ≤ 2/5
  · exact F_vertex_band q r (by grind) hB
  by_cases hC : q = 3
  · subst hC
    exact F_eq3 r (by grind)
  · exact F_pos_cert q r hq0 (by grind) (by grind) hr hΔ

/-! ## Từ (q,r) về (a,b,c) -/

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
  · subst hc'; grind
  · subst hc'; grind
  · have e : 9 * (a * b + b * c + c * a) ^ 2 - 4 * (a * b + b * c + c * a) ^ 3
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

/-- Assoc-shift helper: from `x * d = a` deduce `x * (d * P) = a * P`. -/
theorem div_mul_assoc {x a b c : α} (h : x * (a ^ 2 + 1) = a) :
    x * ((a ^ 2 + 1) * ((b ^ 2 + 1) * (c ^ 2 + 1))) = a * ((b ^ 2 + 1) * (c ^ 2 + 1)) := by
  grind

/-- The inequality. -/
theorem main_ineq (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pqr_facts a b c ha hb hc h
  have hF := F_nonneg_uvw _ _ h1 h2 h3 h4 h5
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
  have hN : (x + y + z) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1))
      ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) := by
    grind
  by_cases hle : x + y + z ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4)
  · exact hle
  · have hlt : 2 / 5 * (a * b + b * c + c * a + 3 / 4) < x + y + z := by grind
    have := lt_mul_pos hlt hPi
    grind

/-! ### Bridge cho https://comparator.live.lean-lang.org

Tên + signature khớp **chính xác** `ineq_challenge` trong `Challenge.lean`
(xem `problem.md`). -/

/-- Bất đẳng thức chính — khớp `ineq_challenge` trong challenge. -/
theorem ineq_challenge (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1)
      ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) :=
  main_ineq a b c ha hb hc habc

end Uvw

/-- Instantiation over ℚ (core `Rat`). -/
theorem main_ineq_rat (a b c : Rat) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) :=
  main_ineq a b c ha hb hc h
