# Lean Setup — lean-sos project

## Trạng thái (21/10/2026)
- Toolchain: **Lean v4.35.0 stable** (chỉ core, KHÔNG Mathlib) — đã cài trên **Mac này** qua elan (`~/.elan/bin`, `elan toolchain install leanprover/lean4:v4.35.0`; không cần workaround Windows).
- `ineq_proof.lean` — proof đầy đủ (p,q,r + SOS), compile sạch, 3 axiom chuẩn.
- `idea_check.lean` — các mảnh đúng của ý tưởng dồn-biến (g-transform, two-equal, zero-case, vertex-decomp), compile sạch, 3 axiom chuẩn. Xem `idea-analysis.md`.
- Build: `~/.elan/bin/lean <file>.lean` (single file, chưa cần lake project).

## Grind lessons (bắt buộc đọc khi debug grind) — 21/10/2026
- Grind **không triển khai tích qua tổng chứa nghịch đảo**: goal dạng `D·(21/10 − (u + a²/5 + ...)) = poly` không bao giờ close dù e1/e2 đã merge các monomial. Fix: **nhân 10 (hay mẫu chung) trước**, làm việc hoàn toàn không phân thức: `D·(21 − 10Σ)` với `10Σ = 10u + 2a² + ...` — ăn ngay.
- `generalize (expr) = u at h hle` KHÔNG rewrite hypothesis nếu phân thức bị giấu dưới `abbrev` chưa unfold → dùng `change <dạng-mở> at hle` trước khi generalize.
- `def` không cho grind nhìn xuyên; dùng `abbrev`.
- Nhân một hệ thức với thừa số: làm lemma riêng context sạch (`shift_mul {u v w z} (h : u*v = w) : u*v*z = w*z := by grind`) rồi apply — đừng trông chờ grind tự nhân trong context lớn.
- `0 < S` không tự coerce thành `0 ≤ S` khi truyền vào lemma khác → `mnn h (by grind)`.
- `div_mul_cancel (by grind)` cần proven `den ≠ 0` trong context; helper có nhánh if-then-else của grind cần giả định mẫu dương/≠0 để tránh case-split vô lý.
- Right-hand-side chứa `(tổng)^2 + 39*16⁻¹` (nghịch đảo vô tỷ trong ngoặc) khiến ring-normalizer bỏ cuộc trên goal — đưa về dạng đã-NHÂN-RỘNG (SOS inline, không `/`) trong phát biểu theorem.

## Cách cài trên máy này (network có endpoint OCSP/CRL bị chặn)
TLS của Windows (schannel) fail revocation check → `curl` thường và **downloader của elan đều lỗi**
(`CRYPT_E_NO_REVOCATION_CHECK`). Vì vậy KHÔNG dùng `elan toolchain install` trực tiếp:

1. `curl --ssl-no-revoke` cho mọi download thủ công.
2. Toolchain được cài bằng tay: zip `lean-4.35.0-windows.zip` giải nén vào
   `~/.elan/toolchains/leanprover-lean4-v4.35.0`, rồi đăng ký:
   `elan toolchain link "leanprover/lean4:v4.35.0" <thư_mục>` → file `lean-toolchain` trong repo resolve OK, không cần download.
3. elan-init.exe đã tự thêm `~/.elan/bin` vào Windows user PATH (registry); Git Bash PATH thêm tay trong `~/.bashrc`.

## Port draft 4.28.0-pre → 4.35.0 (khác biệt grind API đã gặp)
- `simp only at h` (no-op) trong khối `congrArg` cũ → bỏ; thay bằng helper `div_mul_assoc`
  (theorem nhỏ, context sạch) — grind trong context khổng lồ (h1..h5, hid…) hay bị `grind failed`.
- Core 4.35.0 **không có** `mul_assoc` generic (chỉ `Nat.mul_assoc`).
- Grind không tự nhân hypothesis với biến (bước `x²·(a+b+c−3)=0` từ `a+b+c=3`) → phải cấp
  fact tường minh (xem `cubic_roots`).
- `grind [tên_local_hyp]` → lỗi "redundant parameter" (local hyps tự động được dùng).

## Comparator Live (comparator.live.lean-lang.org) — 20/10/2026
- Model: Challenge (statement tin cậy, `theorem ... := by sorry`) vs Solution (proof).
  Site biên dịch Solution rồi đối chiếu theorem đã chứng minh với statement trong Challenge
  (ngăn gian lận: đổi đề, định nghĩa lại ký hiệu). Repo mẫu: leanprover/comparator-live,
  challenge mẫu nằm ở `Projects/mathlib-stable/TrustedChallenges/*.lean`.
- File project: `challenge.lean` (2 theorem: `ineq_challenge`, `ineq_challenge_eq`, đều `sorry`).
- `ineq_proof.lean` có 2 bridge cùng tên + signature y hệt (`ineq_challenge`, `ineq_challenge_eq`)
  trong section `Ineq`, gọi `main_ineq` / `equality_cases`. **Tên hypothesis phải trùng khớp**
  (`habc`, `heq`) giữa challenge và solution — tránh rủi ro so khớp binder names.
- Đã verify local: challenge chỉ warning `sorry`; solution exit 0; axioms bridge = 3 axiom chuẩn.
- Challenge viết trên `α` trừu tượng (grind classes) chứ không phải `ℝ`: Mathlib master
  (checked 20/10/2026) mới chỉ có bridge `CommRing → Lean.Grind.CommRing`
  (`Mathlib/Algebra/Ring/GrindInstances.lean`), KHÔNG xác nhận được
  `Lean.Grind.Field/OrderedRing/Std.IsLinearOrder/LawfulOrderLT` cho `ℝ` → bridge qua `ℝ` rủi ro.
  Statement trừu tượng mạnh hơn ℝ (suy ra trường hợp ℝ) nên hợp lệ về mặt toán.
- Copy-paste: Challenge = khối trong `problem.md` mục "Lean Challenge"; Solution = nguyên file `ineq_proof.lean`.
- **Đã verify thành công trên site (20/10/2026)**: status *"Successfully validated against
  locally-trusted challenge"*. Challenge hash SHA256 `cde1cb43…352543`. Flow UI: dán Challenge →
  trang báo "Not a known challenge" → bấm "I trust this challenge" (confirm dialog hiện hash) →
  "Run Verification" → Success. Screenshot: `comparator-success.png`.
  Lưu ý UI: nút Chakra bị animation chặn click Playwright thường → click bằng JS (`b.click()`).
- **Test "giấu điều kiện dấu bằng" (20/10/2026)**: Challenge rút gọn CHỈ còn `ineq_challenge`
  (xoá `ineq_challenge_eq`), Solution giữ nguyên cả 2 bridge → vẫn **Success**. Hash challenge
  rút gọn: `a399b2d2…97fd`. Screenshot: `comparator-hidden-eq-success.png`. Kết luận: comparator
  chỉ yêu cầu ĐỦ các theorem có trong challenge; solution chứa theorem thừa không sao. Giấu
  theorem làm challenge YẾU hơn (được kiểm chứng ít hơn), không ảnh hưởng soundness. Ngược lại
  giấu HYPOTHESIS (vd `0 ≤ a`) thì challenge sai → không ai pass được.
- **Intent của user khi giấu dấu bằng (KHÔNG phải để làm đề dễ)**: challenge công khai chỉ
  yêu cầu BDT (tầng 1 — máy chấm); phần phân loại dấu bằng là **tiêu chí chất lượng ẩn** —
  user biết solution thật có 7 điểm dấu bằng, đọc solution của model mà thiếu/sai phần đó
  → biết model miss cấu trúc. Workflow 2 tầng: tầng 1 = minimal challenge (`a399b2d2…97fd`);
  tầng 2 = chấm sâu bằng challenge ĐẦY ĐỦ (`cde1cb43…352543`, đã trust) — solution thiếu
  bridge `ineq_challenge_eq` sẽ FAIL cơ chế ở tầng 2, không cần đọc tay.

## VS Code
Extension: `leanprover.lean4`. Mở folder repo → extension đọc `lean-toolchain` qua elan, goal panel hoạt động ngay.
