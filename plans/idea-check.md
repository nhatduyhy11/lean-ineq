# Idea check: hướng "tiếp tuyến / g-transform" (21/10/2026)

Câu hỏi: ý tưởng đưa bài về `Σg(x) ≤ 21/10` với đường chốt `L(x) = x/2 + 1/5`
có thay được chứng chỉ SOS-pqr trong `ineq_proof.lean` không?

## Verdict: FAIL theo tiêu chí "không được gom về SOS cũ"

- **Không trùng tư duy** với SOS (đây là hướng giải tích/tiếp tuyến, minh bạch hơn).
- Nhưng **không ghép được thành proof đầy đủ trên trường α trừu tượng** — muốn đủ
  vẫn phải quay về chứng chỉ `μΔ + (□)²` cũ. Chi tiết đầy đủ: `idea-analysis.md` (root).

## Hai lỗi toán trong ý tưởng gốc

1. Tiếp tuyến tại 1: dạng đúng là `g(x) − (2x/5 + 3/10) = (x−1)²(2x²−3)/(10(x²+1))`
   — ĐỔI DẤU tại `√(3/2)`; không phải `−(x−1)²(2x²−x+3)` như ý tưởng viết.
   "Trường hợp 1" (a ≤ 2 dùng tiếp tuyến tại 1) sập tại x=2: g(2)=1.2 > 1.1.
2. h(x) không có nhân tử `(3x−2)²`; dạng đúng: tử `12x(2−x)(x−1)²(2x−1)²` ≤ 0 trên [0,3/2].

## 3 blocker khi ghép (verified SymPy + Lean)

1. F(q,r) lõm lên theo r (4q+3>0) ⟹ min tại ĐỈNH trong miền khả thi (q ∈ (6/17, ~0.354)), không phải biên.
2. Trên α trừu tượng không dựng được bộ 2-biến-bằng cùng mức q (nghiệm vô tỉ; không có IVT/sqrt).
3. `F = L − κΔ` (κ>0, Δ≥0): biết F ≥ 0 hai đầu dây cung chưa đủ; độ hụt −κΔ bắt buộc hấp thụ bằng μΔ + (□)² — chính là chứng chỉ cũ.

## Đã Lean hóa đúng (idea_check.lean — exit 0, axioms [propext, Classical.choice, Quot.sound])

`g_transform_id`, `two_equal_F(_nonneg)`, `two_equal_g`, `zero_case_g`,
`F_vertex_decomp`, `L_matches_on_curve`, `F_at_zero`.
Kỹ thuật: goal có phân thức phải nhân mẫu chung 10 trước khi grind (`scale_bridge`).
