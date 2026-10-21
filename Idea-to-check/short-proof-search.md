# Tìm kiếm chứng minh gọn hơn (SDP/P-satz) — 21/10/2026

Câu hỏi: có cách giải gọn hơn pqr + 3-case + chứng chỉ SOS không?
Phương pháp: tìm chứng chỉ Positivstellensatz một-vài bằng SDP (cvxpy/CLARABEL/SCS),
cùng các phân tích cấu trúc bằng tay. Pipeline SDP đã được sanity-check trên một
bài toán biết-chắc-feasible (trả "optimal" đúng).

## Kết quả từng hướng

| # | Hướng | Kết quả |
|---|---|---|
| 1 | Bound tuyến tiếp từng số hạng: `t/(t²+1) ≤ −t²/5 + μt + ν` với μ+ν=1/2 | ❌ Fail tại t=1 (1/2 > 3/10) — chứng minh bằng tay |
| 2 | Chứng chỉ cấp-1: `F = σ₀ + a·τ₁ + b·τ₂ + c·τ₃ + (p−3)K` (σ SOS, đối xứng) | ❌ INFEASIBLE — 2 tham số hóa độc lập (clean-form pqr; Gram tổng quát 35×35 và 56×56), bậc tới 10 |
| 3 | `d·F = σ₀ + p·σ₁ + (p−3)K` với d = 1, 4 | ❌ INFEASIBLE (d=1, bậc 8 và 10) |
| 4 | Preordering mở rộng: `d·F = σ₀ + pσ₁ + qσ₂ + rσ₃ + Δσ₄ + qΔσ₅ + (p−3)K`, d=4 | ✅ FEASIBLE — nhưng nghiệm là quái vật: rank ~70 bình phương, K ~165 đơn thức → dài hơn nhiều so proof hiện tại |
| 5 | Chứng chỉ 2-biến (q,r): `dF = σ₀ + qσ₁ + (3−q)σ₂ + rσ₃ + Δσ₄ + (q²−9r)σ₇` | ✅ FEASIBLE (solver-tolerance) nhưng margin biên PSD ≡ 0⁻ (razor-thin, −6.5e−5 sau khi thêm Schur level) → không thể rationalize chính xác |
| 6 | Hand-cert `F = A(q)·Δ + SOS` | ❌ Bất khả — mâu thuẫn A(0) = −1/9 (chứng minh bằng tay, xem sos-reduce-analysis.md) |
| 7 | Monotone-in-r qua 9r≤q², vertex uvw | ❌ Đều sinh ngưỡng chia case (q ≥ 0.3566; cửa sổ vertex q ∈ (6/17, ~0.354)) |

## Phát hiện toán học chính

1. **Không tồn tại chứng chỉ one-shot "tự nhiên".** Cấp-1 P-satz (bội chỉ a,b,c)
   infeasible ở mọi cấu hình bậc đã thử. Nguyên nhân cấu trúc: F phải khít dấu bằng
   tại 3 orbit (1,1,1), (3,0,0), (2,½,½) — trong đó (3,0,0) nằm trên MẶT of miền
   (a=0): chứng chỉ cấp-1 buộc σ₀, τᵢ triệt tiêu đồng thời tại đỉnh → quá chặt.

2. **Chứng chỉ one-shot tồn tại nhưng vô dụng.** Với preordering đầy đủ (thêm p,q,r,Δ)
   chứng chỉ tồn tại — ở dạng ~70 bình phương + K 165 đơn thức: dài hơn, xấu hơn và
   khó hơn proof pqr-3-case hiện tại (thân proof ~115 dòng). Chứng chỉ 2-biến (q,r)
   hẹp hơn nhiều (~45 bình phương) nhưng margin PSD = 0 (khít tại dấu bằng) nên
   không extract được nghiệm hữu tỉ chính xác từ solver số.

3. **Case split q ≤ 1/3 là load-bearing** — không phải artifact. Cùng một ngưỡng
   q ≈ 6/17–1/3 xuất hiện độc lập trong: (a) dấu của μ(q) = (4q²+69q−18)/54 tại
   q ≈ 0.257; (b) điều kiện monotone 2q²(4q+3)/9+12−34q ≤ 0 tại q ≈ 0.3566;
   (c) tính khả thi của vertex uvw (cửa sổ q ∈ (6/17, ~0.354)); (d) phân tích
   từng-hệ-số. Đây là chỗ cấu trúc toán thực sự đổi.

## Kết luận

**Không có cách giải gọn hơn đáng kể.** Proof hiện tại (`ineq_proof.lean`,
p=a+b+c=3, quy về F(q,r), 3 case + chứng chỉ 2c₂sF = 2c₂μΔ + □ + (4/27)s³q²(4q−9)²)
về bản chất là chứng chỉ P-satz nhỏ nhất của bài toán này. Tối ưu tí hon có thể làm
nếu muốn: gộp case q=3 vào case Δ (tại q=3, Δ≥0 ⟹ r=1 trực tiếp, cho phép bỏ giả
thiết 9r≤q² khỏi F_nonneg) — tiết kiệm ~10 dòng, không đáng đổi lại rủi ro.

## Script kiểm chứng (venv /tmp/leancheck-venv, cvxpy)

```
/tmp/sdp_sanity.py   # pipeline sanity: optimal
/tmp/sdp3.py 1 4 3   # cấp-1 Gram tổng quát: infeasible
/tmp/sdp3.py 1 5 4   # cấp-1 bậc 10: infeasible
/tmp/sdp6.py 4       # clean-form d=4: infeasible
/tmp/sdp8.py 4 5 4 3 2   # preordering đầy đủ: optimal, quái vật ~70 squares
/tmp/sdp10.py 1 4 3 3 3  # 2-biến (q,r): optimal (tolerance)
/tmp/repair2.py      # margin trong không gian affine chính xác: t* = −6.5e−5 (razor-thin)
```
