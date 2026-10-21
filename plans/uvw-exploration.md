# Khai phá hướng uvw / mixing-variables (21/10/2026)

Câu hỏi: hướng "đại số hóa" hiện tại trong `ineq_proof.lean` (p,q,r + SOS) cồng kềnh —
hướng phân tích tiếp tuyến / dồn biến (uvw) có cho proof Lean gọn đẹp hơn không?

**Kết luận: KHÔNG cho Lean. Hướng này đẹp cho NGƯỜI ĐỌC, nhưng formalize dài hơn file hiện tại.**
File hiện tại giữ nguyên là artifact tốt nhất. Chi tiết bên dưới (đã verify bằng số học exact).

---

## 1. Toàn suy cho biến đổi tiếp tuyến (đã check đúng)

Với `a+b+c = 3`: `2q = 9 − Σa²` nên `(2/5)(q + 3/4) = 21/10 − Σa²/5`, tức BĐT ⟺

```
Σ ( a/(a²+1) + a²/5 ) ≤ 21/10          g(t) := t/(t²+1) + t²/5
```

Điểm rơi: `g(1) = 7/10`, `g(2) = 6/5`, `g(1/2) = 9/20`, `g(3) = 21/10`, `g(0) = 0` —
khớp cả 7 điểm đẳng thức. Chú ý: **không tồn tại** majorant đơn biến `g(t) ≤ αt + β`
(3 cấu hình rơi riêng biệt), nên buộc phải tương tác 3 biến → uvw.

## 2. Hai factorization biên (verify exact bằng Python, số hữu tỷ)

**Một biến = 0** (`c=0, b=3−a`), với `q = a(3−a)`:
```
10(a²+1)((3−a)²+1)·h(a) = a(a−3)·(4q² − 5q + 4) ≤ 0
```
vì `a(a−3) ≤ 0` trên `[0,3]` và `4q²−5q+4 = 4(q−5/8)² + 39/16 > 0`.

**Hai biến bằng nhau** (`b=c=x, a=3−2x`, `x ∈ [0,3/2]`) — ĐẸP HƠN claim ban đầu:
```
10(x²+1)((3−2x)²+1)·h(x) = 12·x·(x−1)²·(2x−1)²·(x−2)
```
Phân tích **hết sạch**, không còn dư `P(x)` nào. Sửa lại claim cũ:
- factor `(3x−2)²` **không tồn tại** (`x = 2/3` không là nghiệm; `(5/3,2/3,2/3)` không phải
  điểm đẳng thức). Root thực: `x ∈ {0, 1, 1, 1/2, 1/2, 2}` (x=2 ứng với a=−1, ngoài miền).
- Dấu: `x(x−2) ≤ 0` trên `[0,2] ⊇ [0,3/2]` ⟹ `h ≤ 0` tự động.
- Kiểm số: `h(1/4) = −0.00958…` khớp công thức.

## 3. Lỗ hổng của bước dồn biến — và vì sao không vá được trong core Lean

`F(q,r) = (4q+3)r² + (12−34q)r + q(4q²−5q+4)` có hệ số `r²` là `4q+3 > 0` ⟹ parabol
**lõm lên** theo r ⟹ **cực TIỂU ở đỉnh, cực đại ở biên**. Claim "lõm lên ⟹ min ở biên"
là NGƯỢC chiều. Cần F lõm XUỐNG mới được giảm về biên.

Miền r khả thi (q cố định) là đoạn `[r₁, r₂]` (từ `Δ ≥ 0`, `Δ` lõm xuống theo r) cắt `[0,∞)`.
Min của F trên đoạn nằm ở **một trong 3 chỗ**: 2 đầu mút (biên: `r=0` / `Δ=0`) hoặc đỉnh

```
r* = (17q − 6)/(4q + 3)
```

Verify bằng quét exact (grid 1/100 trên q ∈ (0,3]): **r* không bao giờ nằm trong đoạn**
— nhưng chứng minh điều đó tương đương bất đẳng thức **bậc 5**:

```
N(q) := (4q+3)²·Δ(q, r*) = −64q⁵ + 48q⁴ + 3852q³ − 13668q² + 1620q + 972 ≤ 0
        trên [6/17, 3]     (N > 0 chỉ khi q < 6/17 ≈ 0.3529, lúc đó r* < 0 tự infeasible)
```

N không có nghiệm hữu tỷ, đổi dấu trong (0.35, 0.40). Quan trọng: đây không phải
"technicality" — `F(r*) = 4·Q4(q)/(4q+3)` với `Q4 = 4q⁴−2q³−72q²+54q−9` **âm** từ q ≈ 0.45
(Q4(1) = −25): nếu đỉnh khả thi thì BĐT SAI. Nên nhánh đỉnh là phần cốt lõi, không bỏ được.

**Các hướng vá đều thất bại (đã test):**
- Dùng bound rẻ `9r ≤ q²` thay `Δ`: cần `(W ≤ 0 ⟹ Q4 ≥ 0)` với `W = 4q³+3q²−153q+54`
  (W đơn điệu giảm trên [0,3], ✓ đẹp) — nhưng counterexample ở q = 0.51…1.0 (249 điểm grid):
  W(1) = −92 ≤ 0 mà Q4(1) = −25 < 0. **Không đủ.**
- Chứng chỉ không nhân (`F = κΔ + □ + C`): match hệ số r² buộc κ = −(4q+3)/27 < 0. Loại.
- Chứng chỉ nhân s=3−q: tại q=3 mọi chứng chỉ dạng này suy biến (buộc m(3)=n(3)=0 —
  giải slice q=3 cho ra hệ duy nhất trái nhau), tại q=0 cũng vậy ⟹ **case split ở hai đầu
  là bắt buộc của mọi chứng chỉ trong họ này**.
- Slice-scan `min_κ̂≥0 disc(F − κ̂Δ) ≤ 0`: khả thi chính xác trên `(0.2568…, 3)` — trùng
  ngưỡng `μ = (4q²+69q−18)/54 ≥ 0`. Case `q ≤ 1/3` của file hiện tại dùng `r ≥ 0` thay Δ,
  và đó là duy nhất có thể. **Cấu trúc file hiện tại là canonical, không gọt thêm được.**

## 4. Vì sao hướng uvw formalize tệ hơn (đếm chi phí core Lean, không Mathlib)

Muốn chứng minh "min trên đoạn ở đầu mút hoặc đỉnh" cần: (a) miền khả thi là ĐOẠN
(concave-quadratic-above-chord: làm được bằng identity `(r−r₁)(r₂−r)·27 ≥ 0`),
(b) xét vị trí r* so với đoạn — so sánh với nghiệm của Δ (vô tỷ!), (c) nhánh đỉnh:
quintic N ≤ 0 với ngưỡng 6/17. Ước tính ≥ 100–150 dòng grin khó + một BĐT bậc 5 mà
grind core không tự chứng minh được (không có Sturm/CAD). So với 48 dòng `F_nonneg` hiện tại.

Nhận xét cấu trúc: chứng chỉ hiện tại `2c₂sF = 2c₂μΔ + □ + □` CHÍNH LÀ bóng đại số của
lập luận uvw — "F ≥ (bội của) Δ ⟹ chỉ cần biên Δ=0" — gói trong một identity để né
reasoning trên khoảng. Đó là lý do nó ngắn bất thường.

## 5. Giá trị còn lại: writeup người đọc (đã verify đủ để viết)

Proof olympiad gọn (2 trang):
1. Quy đồng ⟹ F(q,r) ≥ 0 (như `poly_id`).
2. Cite uvw (bậc ≤ 2 theo r): chỉ cần kiểm `c=0` và `b=c`. *(fine-print nhánh đỉnh nằm
   trong chứng minh của bổ đề uvw; người viết cần biết nó tồn tại — xem mục 3.)*
3. Hai factorization ở mục 2 (mỗi cái 2 dòng).
4. Đẳng thức: (1,1,1), perms (3,0,0), perms (½,½,2) — đọc ra từ nghiệm x ∈ {0,1,½}.

Script verify (Python thuần, fractions, không sympy): `%TEMP%/lean-sos-scratch/`
(`poly.py`, `verify_boundary.py`, `vertex.py`, `escape.py`, `slice2.py`).

---

## 6. CẬP NHẬT (21/10/2026): đã Lean hóa thành công — `uvw-mixing/IneqUVW.lean`

Mặc định mục 3–4 nói "không gọt thêm được" vẫn đúng cho chứng chỉ large-q (canonical),
nhưng hướng uvw **đã formalize được** đẹp hơn dự kiến, nhờ 3 phát hiện:

1. **Miền đỉnh thật là `[1/3, 2/5]`, không phải `[6/17, 2/5]`.** Nhánh đỉnh chỉ cần
   phủ phần mà hai nhánh kia không phủ: nhánh nhỏ chạy tới `1/3` (hệ số `12−34q ≥ 2/3 ≥ 0`),
   chứng chỉ chạy từ `2/5` (nhưng chỉ cần `q > 1/3`). Đoạn `[1/3, 2/5]` cho `Q4(1/3) = 79/81`
   — hết mẫu `17⁴` vô duyên.
2. **Scale biến `s = 15q − 5` đưa nội suy dây về hệ số NGUYÊN**: `Q̃(s) = 50625·Q4((s+5)/15)
   = 4s⁴+50s³−16050s²+20000s+49375`; chia cho `s(s−1)` ra đúng `T̃(s) = 4s²+54s−15996`
   với `T̃(0) = −15996`, `T̃(1) = −15938` — mọi identity đều integer nên `grind` chạy nhanh.
   (Bản thử đầu giữ q với mẫu `83521 = 17⁴` — grind timeout 200k heartbeats ở chính
   những identity này.)
3. **Đồng nhất thức đỉnh** `(4q+3)F = ((4q+3)r−17q+6)² + 4Q4(q)` (verify exact bằng tay:
   khớp cả 3 hệ số của quadvật theo r) là thay thế first-order hoàn hảo cho việc
   "đỉnh có/không khả thi" — trong miền đỉnh chỉ cần `Q4 ≥ 0`.

**Kết quả**: `uvw-mixing/IneqUVW.lean` — 317 dòng (gốc 395), compile sạch exit 0,
`#print axioms ineq_challenge` = `[propext, Classical.choice, Quot.sound]` (không sorryAx).
Cấu trúc 4 miền: `q ≤ 1/3` (biên r=0) / `[1/3,2/5]` (đỉnh, `Qs_band_pos` + `F_vertex_band`)
/ `(2/5,3)` (chứng chỉ SOS, giữ nguyên) / `q = 3` (`F = 15(1−r)(5−r)`).
Hai factorization biên được giữ làm identity tài liệu (`two_equal_factorization`,
`one_zero_factorization`). Chi tiết: `uvw-mixing/README.md`.

Nhánh đỉnh vẫn KHÔNG xử lý quintic `N(q) ≤ 0` — tránh được bằng cách không cần nó:
trong `[1/3,2/5]` đỉnh khả thi nhưng `F(đỉnh) = 4Q4/(4q+3) ≥ 0` nên không cần biết
đỉnh nằm đâu; ngoài `[1/3,2/5]` chứng chỉ SOS gói mọi trường hợp.
