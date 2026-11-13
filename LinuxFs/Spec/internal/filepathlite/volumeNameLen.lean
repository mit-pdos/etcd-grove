/-
`filepathlite.volumeNameLen` (`internal/filepathlite`, Go 1.27 `path_unix.go`, the part's translation; WAL leaf specs, 2026-11-13).
Lean-first; proved in `LinuxFs/Proof/internal/filepathlite/volumeNameLen.lean`.
-/
module

public import Proof.path.Model
public import LinuxFs.Proof.internal.filepathlite.PkgInit

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

/-- `volumeNameLen(p)`: `0` on Unix. -/
abbrev filepathlite.volumeNameLen.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.filepathlite }}
    (App (Val (@! _root_.Perennial.internal.filepathlite.volumeNameLen)) (Val #p))
  {{ RET #(W64 0); True }}

end spec

end EtcdGrove
end Perennial
