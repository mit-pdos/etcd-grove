/-
`filepath.Join` (`path/filepath`, Go 1.27 `path.go`, the part's translation; WAL leaf specs, 2026-11-13).
Lean-first; proved in `LinuxFs/Proof/path/filepath/Join.lean`.
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

/-- `Join(elem...)` of elements whose lengths sum below `2^62`: the elements from the
first non-empty one, joined with `/`, cleaned; `""` if all are empty (`path.joinModel`; on Unix
`filepath.Join` is `path.Join`). -/
abbrev filepath.Join.spec : Prop :=
  ∀ (sl : GoSlice) (es : List GoString) (dq : DFrac),
  (es.map List.length).sum + es.length < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.path.filepath ∗ sl ↦*{dq} es }}
    (App (Val (@! _root_.Perennial.path.filepath.Join)) (Val #sl))
  {{ (r : GoString), RET #r; ⌜r = path.joinModel es⌝ ∗ sl ↦*{dq} es }}

end spec

end EtcdGrove
end Perennial
