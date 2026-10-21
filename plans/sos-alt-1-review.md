# Review: sos-alt-1 — hướng pqr-SOS dạng "đẳng thức có tên"

## Kết luận (21/10/2026)
**Khả thi ✓ — đã verify đầy đủ.** File `sos-alt-1/sos-alt-1.lean` compile sạch
(Lean v4.35.0, ~16s), 2 bridge `ineq_challenge` + `ineq_challenge_eq` khớp Challenge
(binder names `ha/hb/hc/habc/heq` đúng), `#print axioms` của cả 8 định lý chính chỉ
ra `[propext, Classical.choice, Quot.sound]` — không `sorryAx`.

## Bản chất hướng này
- **Cùng chứng chỉ toán** với `ineq_proof.lean` (cùng F(q,r), cùng certificate
  `2·q(87−4q)·(3−q)·F = 2·q(87−4q)·μ·Δ + □² + (4/27)(3−q)³q²(4q−9)²`).
- **Khác cấu trúc proof**: mọi bước đại số được tách thành định lý ring identity
  CÓ TÊN (section 2: `id_q_le_3`, `id_q2_ge_9r`, `id_discriminant`, `id_quad_pos`,
  `id_F_at_q3`, `id_mu_pos`, `id_sos_certificate`) — người đọc kiểm chứng được bằng
  khai triển 2 vế; phần sign-reasoning lắp từ các atom `mnn/mpos/add3_nn` tường minh.
  File gốc giao nhiều bước trung gian cho `grind` opaque.
- Kích thước: alt ~470 dòng (đủ cả eq-cases) vs gốc 395 dòng. Compile alt ~16s.
- Đã kiểm chứng toán tay tại các điểm: (1,1,1), (2,1,0), (0,3/2,3/2), (2,1/2,1/2),
  (q,r)=(1,0), (9/4,0) — cả reduction identity lẫn certificate đều khớp.

## Đã bổ sung trong đợt review này
- Port **equality cases** từ file gốc sang theo phong cách alt: `cubic_roots`,
  `F_zero_cases` (dùng `id_quad_pos`/`id_mu_pos`/`id_sos_certificate`/`id_F_at_q3`
  thay grind opaque), `equality_cases`, 7 theorem `eq_*`, bridge `ineq_challenge_eq`.
- Thêm helpers section 1: `mul_eq_zero'`, `sum_zero`, `sq_eq_zero'`, dời
  `div_mul_assoc` lên trước (trước đây nằm sau eq-section gây unknown identifier).

## Grind limitations đã đụng khi port (dạy được cho các lần sau)
1. **Dot-notation `.le`/`.lt` FAIL trên instance biến**: `h : 0 < x` với `LT α`
   là instance lớp → `h.le` lỗi "Field projection…C is a constant".
   Dùng `mnn h (by grind)` thay thế.
2. **Grind không tự nhân tích các số dương tự suy ra**: có `0 < q`, `0 < 87−4q`
   trong context nhưng `0 ≤ 2*(q*(87−4q))` vẫn fail → phải lập fact tường minh
   `have hc2 : 0 < q * (87 - 4*q) := mpos …`.
3. **Tương tự cho scaling**: từ `0 < (3−q)³` và `0 < q²` phải lập
   `have h27 : 0 < 4/27*(3−q)³*q²` qua `mpos` rồi mới để grind scale 4/27.
4. Grind ĐỦ sức chứng minh strict `0 < (2q−5/4)² + 39/16` từ fact `0 ≤ □` (linear).
5. `rw [← id_at_q3 r]` + `exact hF` khớp syntactic sau `subst` — pattern đáng tin
   để thay `have cert : … := by grind` (khối certificate ~4 dòng) bằng identity có tên.

## Bridge/Comparator
- File giờ là **drop-in replacement** cho `ineq_proof.lean` trên comparator
  (đủ cả 2 theorem của Challenge đầy đủ `cde1cb43…352543`).
- Chưa chạy trên comparator.live.lean-lang.org (chỉ verify local). Flow dán đã
  ghi ở `plans/lean-setup.md` nếu cần.

## Bonus
- `main_ineq_rat` (instantiation ℚ) compile OK → core 4.35.0 CÓ sẵn instance
  `Lean.Grind.Field/OrderedRing` cho `Rat` (không cần Mathlib bridge).

## Bản giải thích cho người không biết Lean (21/10/2026)
- `docs/bdt-explainer.pdf` (6 trang A4) + nguồn `docs/bdt-explainer.html`.
- Trình bày lại chứng minh bằng ký hiệu toán thường: chiến lược q,r → (Đ0)–(Đ7)
  khớp 1-1 với các identity có tên trong `sos-alt-1.lean`; có hình SVG miền (q,r)
  với 3 điểm dấu bằng trên biên Δ=0 (biên cong vẽ từ tham số hóa nghiệm kép
  b=c=t: q=6t−3t², r=3t²−2t³).
- **Render pipeline** (máy không có LaTeX/pandoc/typst): HTML + MathJax 3 (CDN
  tex-svg) → headless Chrome in PDF:
  `chrome --headless=new --no-pdf-header-footer --virtual-time-budget=25000
  --print-to-pdf=… file:///…/bdt-explainer.html`
- **Gotchas HTML+MathJax đã gặp**: (1) `<` trong công thức theo sau bởi CHỮ cái
  bị browser ăn vào làm tag (vd `$\dfrac13<q<3$`) → dùng `\lt`; `<3` (số) thì
  vô hại; (2) display math dài tràn lề A4 → tách `\begin{aligned}` nhiều dòng;
  (3) xem trước bằng `--screenshot --window-size=850,7800` (không có poppler
  để đọc PDF trực tiếp).
