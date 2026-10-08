/-
Port of election_proof/spec_raft__bcastHeartbeat.v (feb5c73d4).

Lean notes:
* The reference `raft__bcastHeartbeatⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:3285` is to the
  Lean generated code `raft.bcastHeartbeat.impl`.
* Rocq's `send_msgs s ms <| nstate.prvals := pvs |>` is
  `{ sendMsgs s ms with prvals := pvs }`, and the type of the untyped binder `pvs` is
  written out.
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `r.bcastHeartbeat()` (`raft.bcastHeartbeat.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3.lean`;
`raft.go:722`):

      r.bcastHeartbeatWithCtx(r.readOnly.heartbeatCtx())

`heartbeatCtx` returns `nil` under the scope (no read requests;
`spec_readOnly__heartbeatCtx.v`), and reading it leaves the `readOnly` object as it
was; the rest is `bcastHeartbeatWithCtx`'s spec. This is what `stepLeader` does on a
`MsgBeat`, and the postcondition is the model's `Step.beat`. -/
abbrev raft.bcastHeartbeat.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"bcastHeartbeat")) (Val #()))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhys cfg r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜∀ m ∈ ms, HeartbeatOk id (toPState s) m⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

end spec

end EtcdGrove
end Perennial
