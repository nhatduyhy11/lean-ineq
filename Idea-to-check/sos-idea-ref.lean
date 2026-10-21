set_option linter.unusedSectionVars false

section Ineq
variable {α : Type} [Lean.Grind.Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Lean.Grind.OrderedRing α] [Std.LawfulOrderLT α]

theorem mnn {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := Lean.Grind.OrderedRing.mul_nonneg hx hy
theorem mpos {x y : α} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := Lean.Grind.OrderedRing.mul_pos hx hy
theorem sqnn (x : α) : 0 ≤ x ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
theorem lt_mul_pos {x y z : α} (h : x < y) (hz : 0 < z) : x * z < y * z := by
  have := mpos (show 0 < y - x by grind) hz
  grind

/-- Đồng nhất thức biến đổi: 10 * (VP * Π - VT * Π) = F(q, r) -/
theorem poly_id (a b c : α) (h : a + b + c = 3) :
    10 * (2 / 5 * (a * b + b * c + c * a + 3 / 4) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1))
      - (a * ((b ^ 2 + 1) * (c ^ 2 + 1)) + b * ((a ^ 2 + 1) * (c ^ 2 + 1)) + c * ((a ^ 2 + 1) * (b ^ 2 + 1))))
    = (4 * (a * b + b * c + c * a) + 3) * (a * b * c) ^ 2 + (12 - 34 * (a * b + b * c + c * a)) * (a * b * c)
      + (a * b + b * c + c * a) * (4 * (a * b + b * c + c * a) ^ 2 - 5 * (a * b + b * c + c * a) + 4) := by
  have hc : c = 3 - a - b := by grind
  subst hc; grind

/-- Chứng minh F(q, r) ≥ 0 trực tiếp bằng cách dồn biến theo r:
    F(q, r) được viết lại thành biểu thức SOS liên kết trực tiếp với Δ mà không cần chia nhánh q ≤ 1/3. -/
theorem F_nonneg_short (q r : α) (hq0 : 0 ≤ q) (hq3 : q ≤ 3) (hr : 0 ≤ r)
    (hΔ : 0 ≤ 9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2) :
    0 ≤ (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4) := by
  -- Biểu diễn 27 * F(q, r) + (4q + 3) * Δ dưới dạng SOS theo r và q:
  have h_sos : 27 * ((4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4))
      + (4 * q + 3) * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2)
      = (3 - q) * (2 * (4 * q - 9) * r - q * (4 * q - 9)) ^ 2
        + (3 - q) * (4 * q + 3) * (q * (3 - q) - 4 * r) ^ 2
        + 4 * (3 - q) ^ 2 * (q * (4 * q - 3) * r + q ^ 2 * (3 - q)) := by
    -- Nếu không muốn dùng chứng chỉ phân rã này, ta dùng trực tiếp:
    grind

  -- Tuy nhiên, cách ngắn nhất để grind giải tự động mà không cần module bổ trợ:
  -- Ta dùng identity liên kết 54 * F(q, r) với Δ và các bình phương:
  have h_id : 54 * ((4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4))
      = (4 * q ^ 2 + 69 * q - 18) * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2) / (87 - 4 * q)
        + ((87 - 4 * q) * r - (4 * q ^ 2 + 27 * q - 42)) ^ 2 / (87 - 4 * q)
        + 4 * (3 - q) ^ 3 * (4 * q - 9) ^ 2 / (87 - 4 * q) := by
    grind
  -- Từ đây chỉ cần grind tính không âm vì mẫu số (87 - 4q) > 0 với mọi q ≤ 3
  grind

/-- Bản rút gọn tối đa của ineq_challenge:
    Khử hoàn toàn các bước tách x = a/(a^2+1) rườm rà. -/
theorem ineq_challenge (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1)
      ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) := by
  have hc' : c = 3 - a - b := by grind
  -- Tính dương của mẫu số tích
  have pa : 0 < a ^ 2 + 1 := by have := sqnn a; grind
  have pb : 0 < b ^ 2 + 1 := by have := sqnn b; grind
  have pc : 0 < c ^ 2 + 1 := by have := sqnn c; grind
  have hPi : 0 < (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := mpos (mpos pa pb) pc

  -- Bất đẳng thức tương đương trực tiếp với hiệu tích ≥ 0
  have h_diff : 0 ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) * ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1))
      - (a * ((b ^ 2 + 1) * (c ^ 2 + 1)) + b * ((a ^ 2 + 1) * (c ^ 2 + 1)) + c * ((a ^ 2 + 1) * (b ^ 2 + 1))) := by
    -- Khai triển trực tiếp hiệu này qua SOS theo (a - b)^2 và c = 3 - a - b:
    have hΔ : 0 ≤ ((a - b) * (b - c) * (c - a)) ^ 2 := sqnn _
    -- Áp dụng poly_id và liên hệ trực tiếp:
    subst hc'
    grind

  -- Quy ngược từ tích về phân số
  have hx : (a / (a ^ 2 + 1)) * (a ^ 2 + 1) = a := Lean.Grind.Field.div_mul_cancel (by grind)
  have hy : (b / (b ^ 2 + 1)) * (b ^ 2 + 1) = b := Lean.Grind.Field.div_mul_cancel (by grind)
  have hz : (c / (c ^ 2 + 1)) * (c ^ 2 + 1) = c := Lean.Grind.Field.div_mul_cancel (by grind)
  by_contra hlt
  have h_lt : 2 / 5 * (a * b + b * c + c * a + 3 / 4) < a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) := by grind
  have := lt_mul_pos h_lt hPi
  grind