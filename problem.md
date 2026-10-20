$$
\begin{aligned}
Let :a+b+c = 3 \ and  \ a,b,c \ge 0 \\
Prove \ that \ \frac{a}{a^2+1} + \frac{b}{b^2+1} + \frac{c}{c^2+1} \le \frac{2}{5}\left(ab + bc + ca + \frac{3}{4}\right)\\
\end{aligned}
$$

---

## Lean Challenge — https://comparator.live.lean-lang.org

**Vì sao trang đó cần "Challenge"?** Comparator là công cụ kiểm chứng proof từ
nguồn *không tin cậy*: nó tách **mệnh đề** (statement) khỏi **lời giải** (proof).
Ô *Challenge* chứa statement "tin cậy" (các `theorem ... := by sorry`), còn ô
*Solution* chứa proof của bạn. Site biên dịch Solution rồi đối chiếu từng theorem
đã chứng minh xem có khớp **chính xác** statement trong Challenge hay không —
nhờ đó không thể gian lận bằng cách định nghĩa lại ký hiệu hay đổi đề bài.

### Ô 1 — Challenge (copy nguyên khối dưới đây)

```lean
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
```

> Chỉ muốn kiểm tra bất đẳng thức chính? Xoá theorem `ineq_challenge_eq` khỏi
> Challenge (Solution vẫn hợp lệ).

### Ô 2 — Solution (copy toàn bộ file `ineq_proof.lean`)

File này đã có sẵn 2 theorem bridge `ineq_challenge` và `ineq_challenge_eq`
(cuối file, trong section `Ineq`) khớp tên + statement với Challenge ở trên.
Đã kiểm chứng local (Lean v4.35.0): compile sạch, `#print axioms` chỉ ra
`[propext, Classical.choice, Quot.sound]` — proof thật, không `sorryAx`.
