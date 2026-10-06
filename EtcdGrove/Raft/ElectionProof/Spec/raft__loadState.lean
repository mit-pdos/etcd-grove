/-
Port of `election_proof/spec_raft__loadState.v`.

Lean notes: Rocq's three chained updates `s <| term := … |> <| vote := … |> <| logst :=
… |>` are one `{ s with term := …, vote := …, logst := { s.logst with committed := … } }`
(the same value). The premise `a ≤ b ≤ c` is written `a ≤ b ∧ b ≤ c`.
-/
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

/-- `r.loadState(hs)` restores a persisted `HardState`: `raftLog.committed`, `Term` and
`Vote`. It `Panicf`s unless `hs.Commit` lies in `[committed, lastIndex()]`, hence the
premise -- stated on the log's state `s.logst`, which `NState` records.

`loadState` does not touch the tracker. (Until 2026-09-25 the *log* had to be on loan,
because `ownRaftPhys` did not record its state.) -/
abbrev raft.loadState.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (hs : raftpb.HardState),
  uint.Z s.logst.committed ≤ uint.Z hs.Commit' ∧ uint.Z hs.Commit' ≤ uint.Z (logLast s.logst) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"loadState")) (Val #hs))
  {{ RET #();
      ownRaftPhys cfg r id
        { s with term := hs.Term', vote := hs.Vote',
                 logst := { s.logst with committed := hs.Commit' } } }}

end spec

end EtcdGrove
end Perennial
