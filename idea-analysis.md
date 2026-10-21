# Phân tích ý tưởng "g(t) + dồn biến uvw" — 21/10/2026

Kiểm chứng bằng SymPy (symbolic, chính xác) + dựng lại Lean trong `idea_check.lean`.

## Verdict nhanh

| # | Claim trong ý tưởng | Kết quả |
|---|---|---|
| 1 | g-transform: đổi mất dạng `(2/5)(q+3/4) = 21/10 − Σa²/5` | ✅ ĐÚNG (xinh) |
| 2 | "F convex theo r (4q+3>0) ⟹ min tại biên ⟹ chỉ cần check 2-bằng" | ❌ SAI logic — parabol lõm lên có min tại ĐỈNH, không phải biên |
| 3 | `h(x) = −(x−1)²(2x−1)²(3x−2)²·P(x)/...` | ❌ SAI factorization — không có `(3x−2)²`; dạng đúng còn ĐẸP hơn |
| 4 | "Không cần SOS c₂, μ, s nữa" | ❌ Không tránh được — `μΔ` là bắt buộc (xem mục 3) |

## 1. g-transform ✅

`2(ab+bc+ca) = 9 − (a²+b²+c²)` khi `a+b+c = 3` nên bất đẳng thức
⟺ `Σ (a/(a²+1) + a²/5) ≤ 21/10`, đặt `g(t) = t/(t²+1) + t²/5`.
Điểm rơi: `g(0)=0, g(1/2)=9/20, g(1)=7/10, g(2)=6/5, g(3)=21/10`,
và `Σ(a/2 + 1/5) = 21/10` — con số 21/10 đến từ đây. Lean: `g_transform_id`.

## 2. Factorization đúng của h(x)

Ý tưởng ghi `h(x) = −(x−1)²(2x−1)²(3x−2)²·P(x)/(10(...))`. SymPy:

```
h(x) = 3x(x−2)(x−1)²(2x−1)² / (10(x²+1)((3−2x)²+1)/4)
```

- KHÔNG có nhân tử `(3x−2)²` (check: `h(2/3) ≈ −0.0024 ≠ 0`).
- Không cần P(x) gì cả — tử số là `3x(x−2)·(bình phương)` → `h ≤ 0` trên
  `[0, 3/2]` vì `x ≥ 0, x−2 ≤ 0`.
- Dạng (q,r) còn đẹp hơn (SymPy verified, Lean `two_equal_F`):

```
F(6x−3x², x²(3−2x)) = 12·x·(2−x)·(x−1)²·(2x−1)²·(x²+1)  ≥ 0
```

trong đó `F` là đa thức (q,r) của proof cũ. Nghiệm `x=2` của `h` ứng với bộ
`(−1,2,2)` ngoài miền — không liên quan `(3x−2)`.

## 3. Vì sao dồn biến KHÔNG thay được chứng chỉ SOS

Ba blocker độc lập, all verified:

**(a) Logic "convex ⟹ min tại biên" sai.** F lõm lên theo r nên min tại đỉnh
`r* = (34q−12)/(8q+6)`. Với `6/17 < q < ~0.354` đỉnh nằm TRONG miền khả thi
(Δ(q,r*) ≥ 0), phải check F tại đỉnh riêng. Nói cách khác, chuyện "chỉ cần
kiểm tra biên" chính là định lý uvw — một kết quả không-sơ-cấp.

**(b) Trên trường có thứ tự trừu tượng α (đề bài của comparator), không dựng
được bộ 2-biến-bằng cùng mức q.** Bước "min của F xảy ra tại r = r_max ⟹
trả giá trị tại bộ (x,x,3−2x)" đòi hỏi nghiệm `x` của `3x²−6x+q = 0` trong
trường — với q = 1/2, x = 1−√(5/6) vô tỉ, KHÔNG tồn tại trong ℚ. IVT không
có trên trường tổng quát. Mọi chứng thức "giá trị tại biên ≥ 0" kiểu này
đều chết ở bước cuối.

**(c) F lồi ⟹ F nằm DƯỚI dây cung nối 2 đầu 2-biến-bằng.** Phép triệt tiêu r²
(SymPy + Lean `F_vertex_decomp`):

```
F = L − ((4q+3)/27)·Δ,   L tuyến tính theo r,
L = ((8q²−44q)r)·... (L trùng F trên Δ=0, `L_matches_on_curve`)
```

Trên miền khả thi Δ ≥ 0 nên `F ≤ L`. Biết F ≥ 0 tại hai đầu (2-biến-bằng) —
chưa kết luận gì giữa: độ hụt `−κΔ` bắt buộc phải hấp thụ bằng bình phương.
Đó chính xác là vai trò của số hạng `2c₂·μ·Δ` trong chứng chỉ cũ
`2c₂·s·F = 2c₂·μ·Δ + (□)² + (4/27)s³q²(4q−9)²`. Không có lối tắt.

## 4. Các mảnh đúng đã Lean-hóa (`idea_check.lean`, exit 0, 3 axioms chuẩn)

- `g_transform_id`, `two_equal_F` (identity sửa-lại), `two_equal_F_nonneg`,
  `two_equal_g` (h(x) đúng: g(3−2x)+2g(x) ≤ 21/10, x ∈ [0,3/2]),
  `zero_case_g` (g(a)+g(3−a) ≤ 21/10, a ∈ [0,3], SOS
  `4a⁴−24a³+41a²−15a+4 = (2a²−6a+5/4)² + 39/16`),
  `F_vertex_decomp`, `L_matches_on_curve`, `F_at_zero`.

## 5. Kết luận cho câu hỏi "có cách làm gọn hơn không"

- Ý tưởng **đúng ở 2 trường hợp con** (2-bằng, 1-không) và factorization thật
  của chúng rất đẹp — đáng giữ như "bản chất giải tích".
- Nhưng **không thể ghép thành proof gọn hơn** trên α trừu tượng: (b) chặn
  cách dựng bộ 2-bằng; (c) chặn cách "chỉ check biên"; muốn đủ đầy vẫn quay
  về chứng chỉ μΔ+SOS. `ineq_proof.lean` giữ nguyên là proof chính thức.
- Nếu được phép làm việc trên ℝ (có sqrt/IVT), hướng dồn biến cho proof
  trên giấy ~ 15 dòng; nhưng challenge của comparator đang viết trên α.

## Phụ lục: kỷ thuật Lean (chi tiết trong plans/lean-setup.md)

Trên đường đi fix được một vấn đề grind hay gặp: goal dạng `D·(21/10 − (tổng
có phân thức)) = poly` **không bao giờ** được grind triển khai; phải nhân mẫu
chung (10) để mọi thứ thuần đa thức (`scale_bridge`, `scale_bridge0`).
