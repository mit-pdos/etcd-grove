/-
`filepath.Ext` (`path/filepath`, Go 1.27 `path.go`, the part's translation; WAL leaf specs, 2026-11-13).
Lean-first; proved in `LinuxFs/Proof/path/filepath/Ext.lean`.
-/
module

public import LinuxFs.Proof.path.filepath.Model
public import LinuxFs.Proof.path.filepath.PkgInit

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
variable [package_sem : _root_.Perennial.path.filepath.Assumptions]

/-- `Ext(p)`: the extension of the last element (`filepath.extModel`). -/
abbrev filepath.Ext.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.path.filepath }}
    (App (Val (@! _root_.Perennial.path.filepath.Ext)) (Val #p))
  {{ (r : GoString), RET #r; ⌜r = filepath.extModel p⌝ }}

end spec

end EtcdGrove
end Perennial
