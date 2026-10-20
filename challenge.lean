/-!
# Challenge — cho https://comparator.live.lean-lang.org

Dán **toàn bộ** nội dung file này vào ô *Challenge* trên trang.
Các theorem kết thúc bằng `sorry` là các mệnh đề "tin cậy": Solution của bạn
bắt buộc phải chứng minh đúng các statement này (comparator đối chiếu từng theorem).

Nếu không muốn kiểm tra phần phân loại đẳng thức, xoá theorem `ineq_challenge_eq`
đi (Solution vẫn hợp lệ, chỉ là không bị yêu cầu theorem đó).
-/

section
variable {α : Type} [Lean.Grind.Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Lean.Grind.OrderedRing α] [Std.LawfulOrderLT α]

/-- Cho `a + b + c = 3` và `a, b, c ≥ 0`, chứng minh
`a/(a²+1) + b/(b²+1) + c/(c²+1) ≤ (2/5)(ab + bc + ca + 3/4)`. -/
theorem ineq_challenge (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 3) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1)
      ≤ 2 / 5 * (a * b + b * c + c * a + 3 / 4) := by
  sorry

/-- (Tuỳ chọn) Đẳng thức xảy ra tại đâu? -/
theorem ineq_challenge_eq (a b c : α) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 3)
    (heq : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1)
      = 2 / 5 * (a * b + b * c + c * a + 3 / 4)) :
    (a = 1 ∧ b = 1 ∧ c = 1) ∨
    (a = 3 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 3 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 3) ∨
    (a = 1 / 2 ∧ b = 1 / 2 ∧ c = 2) ∨ (a = 1 / 2 ∧ b = 2 ∧ c = 1 / 2) ∨ (a = 2 ∧ b = 1 / 2 ∧ c = 1 / 2) := by
  sorry

end
