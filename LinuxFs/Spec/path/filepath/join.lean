/-
`filepath.join` (`path/filepath`, Go 1.27 `path_unix.go`, the part's translation): `Clean` of the
elements from the first non-empty one, joined by the separator. Lean-first; proved in
`LinuxFs/Proof/path/filepath/join.lean`.
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

/-- `join(elem)`: the elements from the first non-empty one, joined with `/`, cleaned; `""` if
all are empty (`path.joinModel`). -/
abbrev filepath.join.spec : Prop :=
  ∀ (sl : GoSlice) (es : List GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.path.filepath ∗ sl ↦*{dq} es }}
    (App (Val (@! _root_.Perennial.path.filepath.join)) (Val #sl))
  {{ (r : GoString), RET #r; ⌜r = path.joinModel es⌝ ∗ sl ↦*{dq} es }}

end spec

end EtcdGrove
end Perennial
