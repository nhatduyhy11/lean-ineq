/-!
# Kiểm chứng ý tưởng "dồn biến / uvw" cho bất đẳng thức

Bài gốc:  a,b,c ≥ 0, a+b+c = 3  ⟹
    a/(a²+1) + b/(b²+1) + c/(c²+1) ≤ (2/5)(ab+bc+ca+3/4).

File này dựng lại các MẢNH ĐÚNG của ý tưởng "hàm g(t) + dồn biến 2-bằng",
mỗi mảnh một theorem Lean độc lập (core-only, `grind`):

1. `g_transform_id` — đồng nhất thức g-transform:
   (2/5)(q+3/4) = 21/10 − (a²+b²+c²)/5  khi a+b+c = 3,
   tức bài toán ⟺ Σ (a/(a²+1) + a²/5) ≤ 21/10.            [đúng ✓]

2. `two_equal_F` — TRÁI TIM của hướng dồn biến, dạng đúng đã sửa:
   F(6x−3x², x²(3−2x)) = 12x(2−x)(x−1)²(2x−1)²(x²+1) ≥ 0 trên [0, 3/2],
   với F là đa thức (q,r) của proof cũ.
   (Bản user đề xuất −(x−1)²(2x−1)²(3x−2)²·P(x) là SAI: không có nhân tử
   (3x−2)²; dạng đúng còn đẹp — không cần P(x).)

3. `two_equal_g` — cùng mảnh, đúng dạng g(t) của user:
   g(3−2x) + 2g(x) ≤ 21/10 với g(t) = t/(t²+1) + t²/5, x ∈ [0, 3/2].

4. `zero_case_g` — trường hợp biên còn lại của dồn biến (1 biến = 0):
   g(a) + g(3−a) ≤ 21/10 với a ∈ [0, 3], qua chứng chỉ SOS
   4a⁴−24a³+41a²−15a+4 = (2a²−6a+5/4)² + 39/16.

5. `F_vertex_decomp` — phép "triệt tiêu r²" giải thích vì sao hướng dồn biến
   KHÔNG tránh được chứng chỉ Δ:
   27F + (4q+3)Δ = L₂₇,  L₂₇ tuyến tính theo r, Δ = (a−b)²(b−c)²(c−a)².
   Trên miền khả thi Δ ≥ 0 nên F ≤ L (với κ = (4q+3)/27 > 0): F nằm DƯỚI dây
   cung nối hai giá trị 2-biến-bằng (tính lồi theo r) → biết F ≥ 0 tại biên
   CHƯA đủ; độ hụt −κΔ bắt buộc phải hấp thụ bằng bình phương — chính là
   chứng chỉ μΔ + SOS của `ineq_proof.lean`.

6. `F_at_zero` — F(q,0) = q(4q²−5q+4) ≥ 0 (mảnh "F tăng theo r khi q nhỏ").

Kết luận tổng thể (xem báo cáo): các mảnh trên đều đúng và đẹp, nhưng bước
"nên chỉ cần kiểm tra 2-biến-bằng ∪ 1-biến-không" KHÔNG biểu diễn được trên
trường có thứ tự trừu tượng α (cần IVT để dựng bộ (x, x, 3−2x) cùng mức q;
trên ℚ, x = 1−√(5/6) vô tỉ). Proof đầy đủ vẫn là `ineq_proof.lean`.

Kiểm chứng: Lean v4.35.0 stable, chỉ core, `lean idea_check.lean` exit 0.
-/

set_option linter.unusedSectionVars false

section IdeaCheck
variable {α : Type} [Lean.Grind.Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Lean.Grind.OrderedRing α] [Std.LawfulOrderLT α]

/-- 0 ≤ x·y từ hai thừa số không âm. -/
theorem mnn {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := Lean.Grind.OrderedRing.mul_nonneg hx hy
/-- 0 < x·y từ hai thừa số dương. -/
theorem mpos {x y : α} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := Lean.Grind.OrderedRing.mul_pos hx hy
/-- Nhân bất đẳng thức nghiêm ngặt với số dương. -/
theorem lt_mul_pos {x y z : α} (h : x < y) (hz : 0 < z) : x * z < y * z := by
  have := mpos (show 0 < y - x by grind) hz
  grind
/-- Nhân một hệ thức với một thừa số (context sạch — grind không tự thực hiện
bước này khi context lớn). -/
theorem shift_mul {u v w z : α} (h : u * v = w) : u * v * z = w * z := by grind

/-- Đa thức F(q,r) — chính là `10·(VP·Π − Tử)` trong `ineq_proof.lean`. -/
abbrev Fpoly (q r : α) : α := (4 * q + 3) * r ^ 2 + (12 - 34 * q) * r + q * (4 * q ^ 2 - 5 * q + 4)

/-- Tham số hoá bộ 2 biến bằng `(x, x, 3−2x)`: `q = 6x−3x²`, `r = x²(3−2x)`. -/
abbrev qOf (x : α) : α := 6 * x - 3 * x ^ 2
abbrev rOf (x : α) : α := x ^ 2 * (3 - 2 * x)

/-- `g(t) = t/(t²+1) + t²/5`. -/
abbrev gfun (t : α) : α := t / (t ^ 2 + 1) + t ^ 2 / 5

/-! ## 1. g-transform — đúng ✓ -/

/-- `(2/5)(ab+bc+ca+3/4) = 21/10 − (a²+b²+c²)/5` khi `a+b+c = 3`:
bài toán ⟺ `Σ (a/(a²+1) + a²/5) ≤ 21/10`. -/
theorem g_transform_id (a b c : α) (h : a + b + c = 3) :
    2 / 5 * (a * b + b * c + c * a + 3 / 4)
      = 21 / 10 - (a ^ 2 + b ^ 2 + c ^ 2) / 5 := by
  have hc : c = 3 - a - b := by grind
  subst hc
  grind

/-! ## 2. Identity 2-biến-bằng (dạng đúng đã sửa của ý tưởng) -/

/-- **Identity trung tâm:** `F` trên họ 2-biến-bằng là thuần đa thức
`12x(2−x)(x−1)²(2x−1)²(x²+1)` — không có nhân tử (3x−2)² như ý tưởng đề xuất. -/
theorem two_equal_F (x : α) :
    Fpoly (qOf x) (rOf x) = 12 * x * (2 - x) * (x - 1) ^ 2 * (2 * x - 1) ^ 2 * (x ^ 2 + 1) := by
  grind

/-- Hệ quả dấu: `F ≥ 0` trên toàn họ 2-biến-bằng, `x ∈ [0, 3/2]`. -/
theorem two_equal_F_nonneg {x : α} (hx : 0 ≤ x) (hx32 : x ≤ 3 / 2) :
    0 ≤ Fpoly (qOf x) (rOf x) := by
  rw [two_equal_F]
  have e1 : 0 ≤ (x - 1) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  have e2 : 0 ≤ (2 * x - 1) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
  have p1 : 0 ≤ 12 * x * (2 - x) := mnn (by grind) (by grind)
  have p2 : 0 ≤ x ^ 2 + 1 := by grind
  have := mnn (mnn (mnn p1 e1) e2) p2
  grind

/-! ## 3. Cùng mảnh này dưới dạng g(t) của ý tưởng -/

/-- Ring identity thuần phía sau identity `h(x)` (thế giới nhân 10):
`(x²+1)((3−2x)²+1)·(21 − 10Σg) = 12x(2−x)(x−1)²(2x−1)²`. -/
theorem two_equal_ring (x : α) :
    21 * (x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1)
        - 10 * (3 - 2 * x) * (x ^ 2 + 1)
        - 2 * (3 - 2 * x) ^ 2 * (x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1)
        - 20 * x * ((3 - 2 * x) ^ 2 + 1)
        - 4 * x ^ 2 * (x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1)
      = 12 * x * (2 - x) * (x - 1) ^ 2 * (2 * x - 1) ^ 2 := by
  grind

/-- Cầu nối không-phân-thức: triển khai và thay `u, v` (nhân 10 trước).
Chỉ cần e1, e2 — mọi thứ thuần đa thức. -/
theorem scale_bridge (x u v : α)
    (e1 : u * ((3 - 2 * x) ^ 2 + 1) * (x ^ 2 + 1) = (3 - 2 * x) * (x ^ 2 + 1))
    (e2 : v * (x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1) = x * ((3 - 2 * x) ^ 2 + 1)) :
    (x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1)
        * (21 - (10 * u + 2 * (3 - 2 * x) ^ 2 + 20 * v + 4 * x ^ 2))
      = 21 * (x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1)
        - 10 * (3 - 2 * x) * (x ^ 2 + 1)
        - 2 * (3 - 2 * x) ^ 2 * (x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1)
        - 20 * x * ((3 - 2 * x) ^ 2 + 1)
        - 4 * x ^ 2 * (x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1) := by
  grind

/-- Dạng đúng của `h(x)` trong ý tưởng: `g(3−2x) + 2g(x) ≤ 21/10` với
`x ∈ [0, 3/2]` — đúng bằng trường hợp `(3−2x, x, x)` sau g-transform. -/
theorem two_equal_g {x : α} (hx : 0 ≤ x) (hx32 : x ≤ 3 / 2) :
    gfun (3 - 2 * x) + 2 * gfun x ≤ 21 / 10 := by
  by_cases hle : gfun (3 - 2 * x) + 2 * gfun x ≤ 21 / 10
  · exact hle
  · exfalso
    have pa : 0 < (3 - 2 * x) ^ 2 + 1 := by
      have : 0 ≤ (3 - 2 * x) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      grind
    have pb : 0 < x ^ 2 + 1 := by
      have : 0 ≤ x ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      grind
    -- mở abbrev để phân thức lộ ra trong hle
    change ¬ ((3 - 2 * x) / ((3 - 2 * x) ^ 2 + 1) + (3 - 2 * x) ^ 2 / 5
        + 2 * (x / (x ^ 2 + 1) + x ^ 2 / 5) ≤ 21 / 10) at hle
    -- hai phân thức → biến mới u, v (kèm hệ thức chuyển để giữ thông tin)
    have hxa : (3 - 2 * x) / ((3 - 2 * x) ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1) = 3 - 2 * x :=
      Lean.Grind.Field.div_mul_cancel (by grind)
    have hxb : x / (x ^ 2 + 1) * (x ^ 2 + 1) = x :=
      Lean.Grind.Field.div_mul_cancel (by grind)
    generalize (3 - 2 * x) / ((3 - 2 * x) ^ 2 + 1) = u at hxa hle
    generalize x / (x ^ 2 + 1) = v at hxb hle
    -- phiên bản nhân 10: hết phân thức trong bất đẳng thức
    have h10 : 10 * (u + (3 - 2 * x) ^ 2 / 5 + 2 * (v + x ^ 2 / 5))
        = 10 * u + 2 * (3 - 2 * x) ^ 2 + 20 * v + 4 * x ^ 2 := by grind
    have hgt : 21 < 10 * u + 2 * (3 - 2 * x) ^ 2 + 20 * v + 4 * x ^ 2 := by grind
    have e1 : u * ((3 - 2 * x) ^ 2 + 1) * (x ^ 2 + 1) = (3 - 2 * x) * (x ^ 2 + 1) :=
      shift_mul hxa
    have e2 : v * (x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1) = x * ((3 - 2 * x) ^ 2 + 1) :=
      shift_mul hxb
    -- ghép: D·(21 − 10Σ) = đa thức có dấu sẵn
    have hD : 0 < (x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1) := by
      have := mpos pb pa
      grind
    have bridged := scale_bridge x u v e1 e2
    have hsign : 0 ≤ 12 * x * (2 - x) * (x - 1) ^ 2 * (2 * x - 1) ^ 2 := by
      have s1 : 0 ≤ (x - 1) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      have s2 : 0 ≤ (2 * x - 1) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      have p1 : 0 ≤ 12 * x * (2 - x) := mnn (by grind) (by grind)
      have := mnn (mnn p1 s1) s2
      grind
    -- nhưng D·(21 − 10Σ) < 0 vì 21 < 10Σ và D > 0
    have hlt : 21 * ((x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1))
        < (10 * u + 2 * (3 - 2 * x) ^ 2 + 20 * v + 4 * x ^ 2)
          * ((x ^ 2 + 1) * ((3 - 2 * x) ^ 2 + 1)) :=
      lt_mul_pos hgt hD
    grind

/-! ## 4. Trường hợp biên 1 biến = 0 (mảnh còn lại của dồn biến) -/

/-- Chứng chỉ SOS của tử số trường hợp `(a, 3−a, 0)`. -/
theorem quartic_sos (a : α) :
    4 * a ^ 4 - 24 * a ^ 3 + 41 * a ^ 2 - 15 * a + 4
      = (2 * a ^ 2 - 6 * a + 5 / 4) ^ 2 + 39 / 16 := by
  grind

/-- Ring identity thuần cho trường hợp `(a, 3−a, 0)` (thế giới nhân 10,
tử số ở dạng SOS sẵn). -/
theorem zero_case_ring (a : α) :
    21 * (a ^ 2 + 1) * ((3 - a) ^ 2 + 1)
        - 10 * a * ((3 - a) ^ 2 + 1)
        - 2 * a ^ 2 * (a ^ 2 + 1) * ((3 - a) ^ 2 + 1)
        - 10 * (3 - a) * (a ^ 2 + 1)
        - 2 * (3 - a) ^ 2 * (a ^ 2 + 1) * ((3 - a) ^ 2 + 1)
      = a * (3 - a) * ((2 * a ^ 2 - 6 * a + 5 / 4) ^ 2 + 39 / 16) := by
  grind

/-- Cầu nối không-phân-thức cho `(a, 3−a, 0)`: triển khai và thay `u, v`. -/
theorem scale_bridge0 (a u v : α)
    (e1 : u * (a ^ 2 + 1) * ((3 - a) ^ 2 + 1) = a * ((3 - a) ^ 2 + 1))
    (e2 : v * ((3 - a) ^ 2 + 1) * (a ^ 2 + 1) = (3 - a) * (a ^ 2 + 1)) :
    (a ^ 2 + 1) * ((3 - a) ^ 2 + 1)
        * (21 - (10 * u + 2 * a ^ 2 + 10 * v + 2 * (3 - a) ^ 2))
      = 21 * (a ^ 2 + 1) * ((3 - a) ^ 2 + 1)
        - 10 * a * ((3 - a) ^ 2 + 1)
        - 2 * a ^ 2 * (a ^ 2 + 1) * ((3 - a) ^ 2 + 1)
        - 10 * (3 - a) * (a ^ 2 + 1)
        - 2 * (3 - a) ^ 2 * (a ^ 2 + 1) * ((3 - a) ^ 2 + 1) := by
  grind

/-- Trường hợp `(a, 3−a, 0)`: `g(a) + g(3−a) ≤ 21/10` với `a ∈ [0, 3]`. -/
theorem zero_case_g {a : α} (ha : 0 ≤ a) (ha3 : a ≤ 3) :
    gfun a + gfun (3 - a) ≤ 21 / 10 := by
  by_cases hle : gfun a + gfun (3 - a) ≤ 21 / 10
  · exact hle
  · exfalso
    have pa : 0 < a ^ 2 + 1 := by
      have : 0 ≤ a ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      grind
    have pb : 0 < (3 - a) ^ 2 + 1 := by
      have : 0 ≤ (3 - a) ^ 2 := Lean.Grind.OrderedRing.sq_nonneg
      grind
    change ¬ (a / (a ^ 2 + 1) + a ^ 2 / 5
        + ((3 - a) / ((3 - a) ^ 2 + 1) + (3 - a) ^ 2 / 5) ≤ 21 / 10) at hle
    have h1 : a / (a ^ 2 + 1) * (a ^ 2 + 1) = a :=
      Lean.Grind.Field.div_mul_cancel (by grind)
    have h2 : (3 - a) / ((3 - a) ^ 2 + 1) * ((3 - a) ^ 2 + 1) = 3 - a :=
      Lean.Grind.Field.div_mul_cancel (by grind)
    generalize a / (a ^ 2 + 1) = u at h1 hle
    generalize (3 - a) / ((3 - a) ^ 2 + 1) = v at h2 hle
    -- phiên bản nhân 10: hết phân thức
    have h10 : 10 * (u + a ^ 2 / 5 + (v + (3 - a) ^ 2 / 5))
        = 10 * u + 2 * a ^ 2 + 10 * v + 2 * (3 - a) ^ 2 := by grind
    have hgt : 21 < 10 * u + 2 * a ^ 2 + 10 * v + 2 * (3 - a) ^ 2 := by grind
    have e1 : u * (a ^ 2 + 1) * ((3 - a) ^ 2 + 1) = a * ((3 - a) ^ 2 + 1) := shift_mul h1
    have e2 : v * ((3 - a) ^ 2 + 1) * (a ^ 2 + 1) = (3 - a) * (a ^ 2 + 1) := shift_mul h2
    have hD : 0 < (a ^ 2 + 1) * ((3 - a) ^ 2 + 1) := by
      have := mpos pa pb
      grind
    have bridged := scale_bridge0 a u v e1 e2
    -- SOS luôn dương
    have hsos : 0 < (2 * a ^ 2 - 6 * a + 5 / 4) ^ 2 + 39 / 16 := by
      have := Lean.Grind.OrderedRing.sq_nonneg (R := α) (a := 2 * a ^ 2 - 6 * a + 5 / 4)
      grind
    -- nhưng D·(21 − 10Σ) < 0
    have hlt : 21 * ((a ^ 2 + 1) * ((3 - a) ^ 2 + 1))
        < (10 * u + 2 * a ^ 2 + 10 * v + 2 * (3 - a) ^ 2)
          * ((a ^ 2 + 1) * ((3 - a) ^ 2 + 1)) :=
      lt_mul_pos hgt hD
    -- tổng hợp: D·(21−10Σ) = a(3−a)·SOS < 0, nhưng a(3−a) ≥ 0 và SOS > 0
    have hnn : 0 ≤ a * (3 - a) := mnn ha (by grind)
    have hps : 0 ≤ a * (3 - a) * ((2 * a ^ 2 - 6 * a + 5 / 4) ^ 2 + 39 / 16) :=
      mnn hnn (by grind)
    grind

/-! ## 5. Vì sao hướng dồn biến buộc phải quay lại chứng chỉ Δ -/

/-- **Phép triệt tiêu r²** (nhân 27 để thuần đa thức): `27·F + (4q+3)·Δ = L₂₇`
với `L₂₇` tuyến tính theo r, `Δ = (a−b)²(b−c)²(c−a)²`. Trên miền khả thi
`Δ ≥ 0` nên `F ≤ L` (chia 27, với κ = (4q+3)/27 > 0): F nằm dưới dây cung nối
hai giá trị 2-biến-bằng (tính lồi theo r). "Độ hụt" `−κΔ` này là lý do chứng
chỉ của `ineq_proof.lean` bắt buộc có số hạng `μΔ`. -/
theorem F_vertex_decomp (q r : α) :
    27 * Fpoly q r
        + (4 * q + 3) * (9 * q ^ 2 - 4 * q ^ 3 + (54 * q - 108) * r - 27 * r ^ 2)
      = 27 * (8 * q ^ 2 - 44 * q) * r - 4 * q * (4 * q ^ 3 - 33 * q ^ 2 + 27 * q - 27) := by
  grind

/-- `L₂₇` trùng với `27·F` trên đường Δ=0 (hai nhánh 2-biến-bằng). -/
theorem L_matches_on_curve (x : α) :
    27 * (8 * qOf x ^ 2 - 44 * qOf x) * rOf x
        - 4 * qOf x * (4 * qOf x ^ 3 - 33 * qOf x ^ 2 + 27 * qOf x - 27)
      = 27 * Fpoly (qOf x) (rOf x) := by
  have hΔ : 9 * qOf x ^ 2 - 4 * qOf x ^ 3 + (54 * qOf x - 108) * rOf x - 27 * rOf x ^ 2 = 0 := by
    grind
  have key := F_vertex_decomp (qOf x) (rOf x)
  grind

/-! ## 6. Mảnh "F tăng theo r khi q nhỏ" -/

/-- `F(q,0) = q(4q²−5q+4) ≥ 0` với `q ≥ 0` (vì `4q²−5q+4 = (2q−5/4)²+39/16`). -/
theorem F_at_zero {q : α} (hq : 0 ≤ q) : 0 ≤ Fpoly q 0 := by
  have e : Fpoly q 0 = q * (4 * q ^ 2 - 5 * q + 4) := by grind
  rw [e]
  have hq2 : 4 * q ^ 2 - 5 * q + 4 = (2 * q - 5 / 4) ^ 2 + 39 / 16 := by grind
  have hsos : 0 ≤ (2 * q - 5 / 4) ^ 2 + 39 / 16 := by
    have := Lean.Grind.OrderedRing.sq_nonneg (R := α) (a := 2 * q - 5 / 4)
    grind
  have hprod : 0 ≤ q * ((2 * q - 5 / 4) ^ 2 + 39 / 16) := mnn hq hsos
  grind

end IdeaCheck

/-! ## Smoke test: nghiệm `x = 1/2` của identity g (bộ (1/2, 1/2, 2)) -/

example : (1/2 : Rat) / ((1/2) ^ 2 + 1) + (1/2) ^ 2 / 5
    + ((1/2) / ((1/2) ^ 2 + 1) + (1/2) ^ 2 / 5)
    + (2 / (2 ^ 2 + 1) + 2 ^ 2 / 5) = 21 / 10 := by grind
