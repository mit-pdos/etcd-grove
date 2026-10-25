/-
`path.Join` (`path.go`; rafthttp stage 5d). Lean-first; the model: `Proof/path/Model.lean`.
-/
module

public import Proof.path.Model
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `Join(elem...)` of elements whose lengths sum below `2^62`: the elements from the first
non-empty one, joined with `/`, cleaned; `""` if all are empty (`path.joinModel`). -/
abbrev path.Join.spec : Prop :=
  ∀ (sl : GoSlice) (es : List GoString) (dq : DFrac),
  (es.map List.length).sum + es.length < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.path ∗ sl ↦*{dq} es }}
    (App (Val (@! _root_.Perennial.path.Join)) (Val #sl))
  {{ (r : GoString), RET #r; ⌜r = path.joinModel es⌝ ∗ sl ↦*{dq} es }}

end spec

end EtcdGrove
end Perennial
