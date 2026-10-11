/-
`gatherResponseOps(resp, ops)` (`client/v3/leasing/util.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`gatherResponseOps(resp, ops)`** for the operation trees `ts` (standing for `ops`) and their
responses (read-only, with results `rs`): the plain operations that ran, in order
(`OpT.chosenL`), in a fresh slice. -/
abbrev gatherResponseOps.spec : Prop :=
  ∀ (rsl : GoSlice) (ps : List Loc) (sl : GoSlice) (vs : List go_etcd_io.etcd.client.v3.Op)
    (ts : List OpT) (ops : List TxnOp) (rs : List TxnOpResult),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ rsl ↦*□ ps ∗ txnOpsRespN ps ops rs ∗ sl ↦*□ vs ∗ opListAtC false vs ts ∗
      ⌜OpT.txnOps ts = some ops⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.gatherResponseOps)) (Val #rsl)) (Val #sl))
  {{ (ret : GoSlice), RET #ret; opsOwn ret (OpT.chosenL ts rs) }}

end spec

end leasing
end EtcdGrove
end Perennial
