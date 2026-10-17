/-
`RawNode.ReadyWithOpts` (`rawnode.go:137`), new in etcd-io/raft#60 (`notes/pr-verify/raft-60.md`,
2026-10-16): `Ready` with options, `readyWithoutAccept(opts)` then `acceptReady`. `Ready()` is now
`ReadyWithOpts(ReadyOpts{})`.

Lean notes: as `RawNode.Ready.spec` (`hlc := HasLC.hasLC`, `[AllG GF]`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnodeReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `rn.ReadyWithOpts(opts)` is `RawNode.Ready.spec` with one more conjunct, `Hce_off`: with
`opts.DisableCommittedEntries` the `Ready`'s `CommittedEntries` are empty (`ce = []`), so the
node's `delivered` is unchanged and the entries not handed out now are the next ones handed out
later (the next `Ready`'s `ce` extends `delivered`, `isCommitted`): pausing the flow skips no
committed entry and hands none out twice. Everything else (entries to append, messages, read
states, hard state) is handed out as by `Ready`: the option only holds back the committed
entries. Without the option it is `RawNode.Ready.spec` (`RawNode.Ready.wp_proof` is proved from
this spec at `ReadyOpts{}`). -/
abbrev RawNode.ReadyWithOpts.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (opts : ReadyOpts),
  rs.steps = [] →
  rs.unpersisted = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ReadyWithOpts")) (Val #opts))
  {{ (rd : Ready) (ce es : List EntryM) (ms : List QMsg)
      (sts : List ReadStateM) (h : HardStateM) (steps : List Pending), RET #rd;
      "Hrn" ∷ ownRawNode γ rn id
        { rs with delivered := rs.delivered ++ ce, unpersisted := es, steps := steps,
                  outlb := 0, unst := false } ∗
      "#Hce" ∷ entsRO rd.CommittedEntries' ce ∗
      -- the option: no committed entries handed out
      "%Hce_off" ∷ ⌜opts.DisableCommittedEntries' = true → ce = []⌝ ∗
      "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
      "#Hents" ∷ entsRO rd.Entries' es ∗
      "Hmsgs" ∷ rd.Messages' ↦* ms.map QMsg.loc ∗
      "Hmsgs_cap" ∷ ownSliceCap Loc rd.Messages' (DFrac.own 1) ∗
      -- (2026-10-16, stage R5, D8) the messages, a response at half
      "Hmsgs_own" ∷ ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) ∗
      "#Hmsgs_ok" ∷ ([∗list] q ∈ ms, isRaftMsg γ q.st) ∗
      -- each message's read credit (2026-10-13)
      "Hmsgs_cred" ∷ ([∗list] q ∈ ms,
        rdCred γ (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) ∗
      -- every message is of a term at most the node's at the call (2026-10-10)
      "%Hmsgs_term" ∷ ⌜∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z rs.term⌝ ∗
      "%Hsnapz" ∷ ⌜rd.Snapshot' = null⌝ ∗
      -- the read states (2026-10-13)
      "#Hrs" ∷ readStatesPts rd.ReadStates' sts ∗
      "#Hrs_ok" ∷ ([∗list] st ∈ sts, readStateOk γ st) ∗
      -- (2026-10-16, stage R5) the hard state, `nil` or fresh and read-only
      "#Hhard" ∷ hsOpt rd.HardState' h ∗
      -- the right to append `es` to the node's storage (2026-10-10)
      "Happ" ∷ appendRight rs.storage es }}

end spec

end EtcdGrove
end Perennial
