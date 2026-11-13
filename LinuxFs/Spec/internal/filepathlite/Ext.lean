/-
`filepathlite.Ext` (`internal/filepathlite`, Go 1.27 `path.go`, the part's translation; WAL leaf specs, 2026-11-13).
Lean-first; proved in `LinuxFs/Proof/internal/filepathlite/Ext.lean`.
-/
module

public import LinuxFs.Proof.path.filepath.Model
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

/-- `Ext(p)`: the extension of the last element (`filepath.extModel`). -/
abbrev filepathlite.Ext.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.filepathlite }}
    (App (Val (@! _root_.Perennial.internal.filepathlite.Ext)) (Val #p))
  {{ (r : GoString), RET #r; ⌜r = filepath.extModel p⌝ }}

end spec

end EtcdGrove
end Perennial
