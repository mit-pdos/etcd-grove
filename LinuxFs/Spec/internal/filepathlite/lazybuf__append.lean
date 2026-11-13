/-
`filepathlite.lazybuf.append` (`internal/filepathlite`, Go 1.27 `path.go`, the part's translation; WAL leaf specs, 2026-11-13).
Lean-first; proved in `LinuxFs/Proof/internal/filepathlite/lazybuf__append.lean`.
-/
module

public import LinuxFs.Proof.internal.filepathlite.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.internal.filepathlite.Assumptions]

/-- `b.append(c)` below the path's length: `c` written at `w`, the bytes before kept. -/
abbrev filepathlite.lazybuf.append.spec : Prop :=
  ∀ (b : Loc) (p : GoString) (P : List w8) (w : Nat) (c : w8),
  w < p.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.filepathlite ∗ filepathlite.lbOwn b p P w }}
    (App (Val (b @!! go.GoType.PointerType _root_.Perennial.internal.filepathlite.lazybuf.ty @!! go!"append"))
      (Val #c))
  {{ RET #(); ∃ P' : List w8, filepathlite.lbOwn b p P' (w + 1) ∗
      ⌜P'.take (w + 1) = P.take w ++ [c] ∧ P'.length = p.length⌝ }}

end spec

end EtcdGrove
end Perennial
