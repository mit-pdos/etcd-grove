/-
`filepath.Abs` (`path/filepath`, Go 1.27 `path.go`, the part's translation; WAL leaf specs, 2026-11-13).
Lean-first; proved in `LinuxFs/Proof/path/filepath/Abs.lean`.
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

/-- `Abs(p)` of an absolute `p`: `Clean(p)` and no error (a relative `p` calls `os.Getwd`,
names-only here, so the spec excludes it). -/
abbrev filepath.Abs.spec : Prop :=
  ∀ (p : GoString),
  p.head? = some (W8 47) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.path.filepath }}
    (App (Val (@! _root_.Perennial.path.filepath.Abs)) (Val #p))
  {{ RET (PairV #(path.cleanModel p) #GoInterface.nil); True }}

end spec

end EtcdGrove
end Perennial
