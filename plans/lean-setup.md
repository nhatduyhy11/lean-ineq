# Lean Setup — lean-sos project

## Trạng thái (20/10/2026)
- Toolchain: **Lean v4.35.0 stable** (chỉ core, KHÔNG Mathlib).
- File chính: `ineq_proof.lean` — compile sạch, exit 0, không `sorry` (chỉ dùng 3 axiom chuẩn: propext, Classical.choice, Quot.sound).
- Build: `lean ineq_proof.lean` (single file, chưa cần lake project).
- Chưa có lake project. Nếu cần Mathlib sau này: `lake +v4.35.0 new <name> math` → `lake update` → `lake exe cache get` → `lake build`.

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

## VS Code
Extension: `leanprover.lean4`. Mở folder repo → extension đọc `lean-toolchain` qua elan, goal panel hoạt động ngay.
