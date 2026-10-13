/- Port of election_proof/spec_raft__bcastAppend.v (feb5c73d4).

Lean notes: Rocq's untyped binders `id s` and `pvs` get their types written
out; `send_msgs s ms <| nstate.prvals := pvs |>` is `{ sendMsgs s ms with prvals := pvs }`.
-/
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

/-- The broadcast a new leader sends. `bcastAppend` visits every peer's `Progress` and
calls `sendAppend`, which reaches `maybeSendAppend` -- and that sends a `MsgApp` only
when the log and the peer's `Progress` permit it, otherwise a `MsgSnap` or nothing at
all (the peer is paused, or there is nothing to send and `sendIfEmpty` is false).

So this says **not** one `MsgApp` per peer, only that the outbox grew by some list of
messages `ReplOk` allows (`ReplSends`, `Defs.lean`) -- which is exactly what `step_win`
and `step_send_apps` ask for -- and that no `Match` moved. An earlier version of the
model demanded one per peer, which would have made this claim false -- the same trap
`raft.appendEntry.spec` fell into before 2026-09-15 (it was called
`wp_raft__appendEmptyEntry` then, after a Go method that does not exist). -/
abbrev raft.bcastAppend.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysC c r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"bcastAppend")) (Val #()))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysC c r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜ReplSends id s ms⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.bcastAppend.spec` by `raft.bcastAppend.spec_simple`. -/
abbrev raft.bcastAppend.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"bcastAppend")) (Val #()))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhys cfg r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜ReplSends id s ms⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

open Iris.ProofMode in
theorem raft.bcastAppend.spec_simple
    (H : raft.bcastAppend.spec (GF := GF) (hG := hG)) :
    raft.bcastAppend.specS (GF := GF) (hG := hG) := by
  intro cfg r id s
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s $$ [$Hpkg $Hphys]
  inext
  iintro %ms %pvs ⟨Hphys, %H1, %H2⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ
  iframe Hphys
  ipureintro; exact ⟨H1, H2⟩

end spec

end EtcdGrove
end Perennial
