/-
`filepath.Dir` (`path/filepath`, Go 1.27 `path.go`, the part's translation; WAL leaf specs, 2026-11-13).
Lean-first; proved in `LinuxFs/Proof/path/filepath/Dir.lean`.
-/
module

public import Proof.path.Model
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

/-- `Dir(p)`: all but the last element, cleaned (`path.dirModel`). -/
abbrev filepath.Dir.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.path.filepath }}
    (App (Val (@! _root_.Perennial.path.filepath.Dir)) (Val #p))
  {{ (r : GoString), RET #r; ⌜r = path.dirModel p⌝ }}

end spec

end EtcdGrove
end Perennial
