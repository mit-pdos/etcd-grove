/- Port of election_proof/spec_raft__bcastAppend.v. -/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The broadcast a new leader sends. `bcastAppend` visits every peer's `Progress` and
calls `sendAppend`, which reaches `maybeSendAppend` -- and that sends a `MsgApp` only
when the log and the peer's `Progress` permit it, otherwise a `MsgSnap` or nothing at
all (the peer is paused, or there is nothing to send and `sendIfEmpty` is false).

So this says **not** one `MsgApp` per peer, only that the outbox grew by some list of
`App`s from `id` at the current term. That is exactly what the weakened `step_win`
asks for, and all the election model ever uses: a receiver reads an `App` through
`step_higher_term`, which cares about its term and that a leader sent it. An earlier
version of the model demanded one per peer, which would have made this claim false --
the same trap `raft.appendEntry.spec` fell into before 2026-09-15 (it was called
`wp_raft__appendEmptyEntry` then, after a Go method that does not exist). -/
abbrev raft.bcastAppend.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"bcastAppend")) (Val #()))
  {{ (ms : List Msg) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)), RET #();
      ownRaftPhys cfg r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜AppSends id s.term ms⌝ }}

end spec

end EtcdGrove
end Perennial
