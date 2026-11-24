-- The copy for the part `KvNet/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/isMsgInArray.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). -/
module

public import KvNet.Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `isMsgInArray(msgt, arr)`: `arr[msgt]`, `false` past its end. (Until 2026-11-24 only that it
returns: `RawNode.Step`'s strengthened spec needs `IsLocalMsg`'s answer, #33 S4.) `MessageType`
is an `int32`: a negative one panics (index out of range). -/
abbrev isMsgInArray.spec : Prop :=
  ∀ (t : w32) (arr : GoSlice) (l : List Bool),
  0 ≤ sint.Z t →
  {{ (arr ↦*□ l : IProp GF) }}
    (App (App (Val #(functions isMsgInArray [])) (Val #t)) (Val #arr))
  {{ (b : Bool), RET #b; ⌜b = (l[(sint.Z t).toNat]?.getD false)⌝ }}

end spec

end EtcdGrove
end Perennial
