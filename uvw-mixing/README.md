# uvw-mixing — chứng minh theo hướng uvw / dồn biến

`IneqUVW.lean` — chứng minh cùng một bất đẳng thức với `../ineq_proof.lean`
nhưng cấu trúc theo **uvw**: tách rời ba miền của `q = ab+bc+ca`, mỗi miền
ứng với một "chỗ rơi cực tiểu" của

```
F(q,r) = (4q+3)r² + (12−34q)r + q(4q²−5q+4)     (parabol LỔM LÊN theo r)
```

## Trạng thái

- **Compile sạch**: `lean uvw-mixing/IneqUVW.lean` → exit 0 (Lean v4.35.0, chỉ core, không Mathlib).
- **Không `sorry`**: `#print axioms ineq_challenge` → `[propext, Classical.choice, Quot.sound]`.
- Bridge `ineq_challenge` khớp tên + statement với `Challenge.lean` (xem `../problem.md`).
- 317 dòng (file gốc pqr+SOS: 395 dòng).

## Cấu trúc chứng minh (case split theo miền đỉnh `[1/3, 2/5]`)

| Miền | Định lý | Bản chất uvw |
|---|---|---|
| `q ≤ 1/3` | `F_pos_small` | F tăng theo `r ≥ 0` ⟹ min tại biên **r = 0** (một biến = 0): `F(q,0) = q(4q²−5q+4) ≥ 0` |
| `1/3 ≤ q ≤ 2/5` | `F_vertex_band` | **MIỀN ĐỈNH**: `(4q+3)F = ((4q+3)r−17q+6)² + 4·Q4(q) ≥ 0` — đỉnh khả thi và vẫn không âm |
| `2/5 < q < 3` | `F_pos_cert` | Đỉnh không khả thi ⟹ min ở biên **Δ = 0** (hai biến bằng nhau); đóng gói bằng chứng chỉ SOS `2c₂sF = 2c₂μΔ + □ + □` |
| `q = 3` | `F_eq3` | `F = 15(1−r)(5−r) ≥ 0` vì `9r ≤ q²` |

Sau đó `pqr_facts` + `poly_id` (giữ nguyên từ file gốc) kéo kết quả về `(a,b,c)`.

## Hai mảnh mới so với file gốc

1. **`Qs_band_pos`** — `Q4 > 0` trên `[1/3, 2/5]` bằng *nội suy dây* với hệ số
   **nguyên thuần** qua biến tỉ lệ `s = 15q − 5`:
   `Q̃(s) = 4s⁴ + 50s³ − 16050s² + 20000s + 49375`,
   `Q̃ = [(1−s)·49375 + s·53379] + s(s−1)·T̃`,  `T̃(s) = 4s² + 54s − 15996`,
   `T̃ = (1−s)(−15996) + s(−15938) + 4s(s−1) ≤ 0` (tổ hợp lồi + phần lồi).
   Mọi bước là first-order; các `have` riêng lẻ nên `grind` chạy nhanh.
   *(Bản thử đầu với đoạn `[6/17, 2/5]` cho hệ số `/17⁴ = 83521` — grind
   field-normalization vượt 200k heartbeats; scale nguyên là fixes.)*
2. **`F_vertex_band`** — đồng nhất thức hoàn thành bình phương tại đỉnh
   `r* = (17q−6)/(4q+3)` — bước thay thế first-order cho lập luận
   "đỉnh nằm ngoài miền khả thi" (cái đó tương đương bất đẳng thức bậc 5,
   không chứng minh được bằng `grind` core).

Hai **factorization biên** (`two_equal_factorization`, `one_zero_factorization`)
là identity đa thức tài liệu hóa phần "kiểm biên" của uvw:
- hai biến bằng nhau: `12x(x−1)²(2x−1)²(x−2)` — phân tích hết sạch,
  sửa lại claim cũ (không có `(3x−2)²`);
- một biến = 0: `a(a−3)(4q²−5q+4)`, `4q²−5q+4 = 4(q−5/4)²+39/16 > 0`.

## Ghi chú trung thực về hướng uvw

Trên trường có thứ tự trừu tượng `α` (ví dụ `α = ℚ`), điểm biên `Δ = 0` có thể
**vô tỷ** nên không thể "tính F tại biên" trực tiếp. Miền lớn dùng chứng chỉ
SOS — chính là bóng đại số của lập luận uvw. Xem `../plans/uvw-exploration.md`
cho phân tích đầy đủ (vì sao đỉnh/quintic không formalize được trong core).

## Compile

```bash
lean uvw-mixing/IneqUVW.lean   # exit 0 = QED
```
