/-
`filepathlite.lazybuf.string` (`internal/filepathlite`, Go 1.27 `path.go`, the part's translation; WAL leaf specs, 2026-11-13).
Lean-first; proved in `LinuxFs/Proof/internal/filepathlite/lazybuf__string.lean`.
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

/-- `b.string()`: the buffer's first `w` bytes (the volume name is empty). -/
abbrev filepathlite.lazybuf.string.spec : Prop :=
  ∀ (b : Loc) (p : GoString) (P : List w8) (w : Nat),
  P.length = p.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.filepathlite ∗ filepathlite.lbOwn b p P w }}
    (App (Val (b @!! go.GoType.PointerType _root_.Perennial.internal.filepathlite.lazybuf.ty @!! go!"string"))
      (Val #()))
  {{ RET #(P.take w); True }}

end spec

end EtcdGrove
end Perennial
