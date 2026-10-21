# Phân tích ý tưởng "SOS reduce" (idea-sos-reduce.md + sos-idea-ref.lean) — 21/10/2026

Kiểm chứng bằng SymPy (symbolic, chính xác) + compile Lean thật (`~/.elan/bin/lean`).

## Verdict nhanh

| # | Phần của ý tưởng | Kết quả |
|---|---|---|
| 1 | File `.md` (3 trường hợp q≤1/3, q=3, 1/3<q<3 + chứng chỉ SOS) | ✅ đúng — nhưng đây CHÍNH LÀ `ineq_proof.lean` hiện có, không phải cách gọn hơn |
| 2 | Dòng chứng chỉ trong `.md`: `2c₂·s·F = 2c₂·μ·Δ + …` với `c₂ = q(87−4q)/2` | ❌ typo hệ số 2 — bản đúng là `c₂ = q(87−4q)` (code Lean gốc ĐÚNG, chỉ comment/.md sai) |
| 3 | ref `h_sos`: `27F + (4q+3)Δ = 3 bình phương` (bỏ chia case) | ❌ SAI tuyệt đối — VP bậc 2 theo r, VT bậc 1, không thể sửa hệ số mà đúng |
| 4 | ref `h_id`: `54F = [(4q²+69q−18)Δ + □ + …]/(87−4q)` | ❌ SAI tuyệt đối — counterexample (q,r)=(3,0): 4050 ≠ −6 |
| 5 | Mục tiêu "không cần chia nhánh q ≤ 1/3" | ❌ bất khả trong mọi family chứng chỉ tự nhiên (mục 3 dưới) |

Compile thực tế của `sos-idea-ref.lean`: **6 lỗi** (dòng 35, 43, 45, 67 grind failed; 73 unknown tactic — cascade; 52 unsolved goals).

## 1. File `.md` = proof hiện có, không phải ý tưởng mới

Cấu trúc `.md` khớp 1-1 với `ineq_proof.lean`: poly_id → 3 trường hợp (q≤1/3
xét từng số hạng; q=3 thì F = 15(1−r)(5−r); 1/3<q<3 dùng chứng chỉ SOS với
c₂, μ, s) → phân loại dấu bằng (1,1,1), (3,0,0), (2,1/2,1/2). Toán đúng hết,
chỉ dòng chứng chỉ viết lệch hệ số 2 (c₂ thiếu… thừa /2). Đã sửa comment trong
`ineq_proof.lean` cho khớp code (code không đổi).

## 2. Hai identity trong `F_nonneg_short` ĐỀU sai (SymPy expand chính xác)

**h_sos**: `27F + (4q+3)Δ` là **đa thức bậc 1 theo r** (chính là L trong
`F_vertex_decomp` của `idea_check.lean`), còn vế phải có thành phần
`(3−q)((4q−9)(2r−q))² + 16(3−q)(4q+3)r²` — hệ số r² là
`4(3−q)(16q²−56q+93)`, với discriminant `56²−4·16·93 = −2816 < 0` nên **dương
với mọi q**, không bao giờ triệt tiêu. Counterexample q=1:
VT = −4(243r−29), VP = 2(212r²−204r+69). Đây không phải lỗi "sai hệ số" mà là
sai cấu trúc — không sửa được trong family này.

**h_id**: nhân `(87−4q)` cả hai vế vẫn sai. (q,r) = (3,0): VT = 54·F(3,0) =
4050, VP = −450. Nguyên nhân: chứng chỉ thật có thêm nhân tử `q(3−q)` ở cả hai
vế và `q²` trong bình phương — ref đã "rút gọn" bừa chúng đi.

Ngoài ra term thứ 3 của h_sos `4(3−q)²(q(4q−3)r + q²(3−q))` không phải bình
phương và không hiển nhiên ≥ 0 — ngay cả nếu identity đúng, grind vẫn không
kết luận được. Ref cũng quên giả định `9r ≤ q²` (cần cho case q=3: r ≤ 1).

## 3. "Bỏ chia case" là bất khả — 3 chứng minh độc lập

**(a) Family `F = A(q)·Δ + Σ(uᵢ(q)r+vᵢ(q))² + w(q)` với A ≥ 0: vô nghiệm.**
Tại q=0: `F(0,r) = 3r(r+4)` và `Δ(0,r) = −27r(r+4)` — tức `F = −Δ/9` trên cả
đường thẳng q=0. Đồng nhất thức buộc `Σ(uᵢ(0)r+vᵢ(0))² + w(0) ≡ 0` nên
`uᵢ(0)=vᵢ(0)=w(0)=0`; so sánh hệ số của r: `12 = −108·A(0)` ⟹ `A(0) = −1/9 < 0`.
Miền khả thi có điểm trong cho mọi q ∈ (0, 9/4) nên tính liên tục buộc A ≥ 0
gần 0 — mâu thuẫn. (A(0)<0 chỉ "vô hại" tại đúng điểm (0,0) nơi Δ=0, nhưng
A(q) là đa thức theo q nên âm lan cả một lân cận có Δ>0.)

**(b) Family chứng chỉ μΔ (kiểu proof cũ): μ bắt buộc đổi dấu.** Hệ số của Δ
là `μ(q) = (4q²+69q−18)/54`, nghiệm dương `(−69+3√561)/8 ≈ 0.257` — âm với
q < 0.257. Đó chính là lý do proof cũ phải tách `q ≤ 1/3` xét từng số hạng.

**(c) Đi đường monotone theo r với bound `9r ≤ q²` cũng phải chia.** F giảm
theo r trên `0 ≤ r ≤ q²/9` cần `φ(q) = 2q²(4q+3)/9 + 12 − 34q ≤ 0`, tức
q ≥ 0.3566… — lại một ngưỡng, không uniform.

Cùng một gốc với blocker (c) trong `idea-analysis.md`: `F = L/27 − ((4q+3)/27)Δ`
với κ > 0 ⟹ F nằm DƯỚI dây cung; ở vùng q nhỏ, số hạng theo từng bậc của F
tự dương và Δ gần như không còn "chỗ" để hấp thụ — mọi chứng chỉ đều buộc
hệ số của Δ âm gần q=0 ⟹ bắt buộc xử lý vùng đó bằng lập luận khác ⟹ chia case.

## Kết luận

- `.md` = mô tả trung thực của proof hiện có (kèm 1 typo hệ số 2) — **không
  phải cách gọn hơn**.
- ref.lean = nỗ lực bỏ chia case bằng một chứng chỉ duy nhất — **fail hoàn toàn**:
  2 identity sai cấu trúc (không sửa được), 6 lỗi compile, và mục tiêu no-split
  bất khả trong mọi family tự nhiên.
- `ineq_proof.lean` (3 case + chứng chỉ μΔ) vẫn là proof ngắn nhất đã biết và
  là proof chính thức cho challenge.

## Phụ lục: lệnh kiểm chứng

```
~/.elan/bin/lean Idea-to-check/sos-idea-ref.lean        # 6 lỗi
/tmp/leancheck-venv/bin/python /tmp/check_sos_reduce.py # expand các identity
/tmp/leancheck-venv/bin/python /tmp/check_fix.py        # chứng chỉ Lean nguyên văn: difference = 0
```
