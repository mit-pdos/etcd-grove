/- Lean-first (no Rocq counterpart). -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `isMsgInArray(msgt, arr)`: `arr[msgt]`, `false` past its end. Only that it returns is
specified: no caller depends on the answer (`RawNode.Step` guards with it). `MessageType`
is an `int32`: a negative one panics (index out of range). -/
abbrev isMsgInArray.spec : Prop :=
  ∀ (t : w32) (arr : GoSlice) (l : List Bool),
  0 ≤ sint.Z t →
  {{ (arr ↦*□ l : IProp GF) }}
    (App (App (Val #(functions isMsgInArray [])) (Val #t)) (Val #arr))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
