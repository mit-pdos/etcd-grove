/-
`filepathlite.Dir` (`internal/filepathlite`, Go 1.27 `path.go`, the part's translation; WAL leaf specs, 2026-11-13).
Lean-first; proved in `LinuxFs/Proof/internal/filepathlite/Dir.lean`.
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

/-- `Dir(p)`: all but the last element, cleaned, as `path.Dir` (`path.dirModel`). -/
abbrev filepathlite.Dir.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.filepathlite }}
    (App (Val (@! _root_.Perennial.internal.filepathlite.Dir)) (Val #p))
  {{ (r : GoString), RET #r; ⌜r = path.dirModel p⌝ }}

end spec

end EtcdGrove
end Perennial
