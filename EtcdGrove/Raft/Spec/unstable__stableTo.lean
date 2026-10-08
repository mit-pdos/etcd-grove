/-
Port of `election_proof/spec_unstable__stableTo.v` (857d09190).

Lean notes: `unstable_hit` is `UnstableHit`.
-/
import EtcdGrove.Raft.InvReadylog

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- When `u.stableTo(id)` moves entries: `id.index` is an index of the suffix and the
entry there has term `id.term`. (On the state record since 2026-10-08; before, on the
Goose value and the entries.) -/
def UnstableHit [FfiSyntax] (us : UnstableSt) (id : entryID) : Prop :=
  (uint.Z us.offset ≤ uint.Z id.index' ∧
   uint.Z id.index' < uint.Z us.offset + (us.ents.length : Int)) ∧
  ∃ e, us.ents[(uint.Z id.index' - uint.Z us.offset).toNat]? = some e ∧
       e.Term' = id.term'

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `u.stableTo(id)` (`log_unstable.go:134`):

    gt, ok := u.maybeTerm(id.index)
    if !ok { Infof; return }
    if id.index < u.offset { Infof; return }      // the snapshot's index
    if gt != id.term { Infof; return }
    num := int(id.index + 1 - u.offset)
    u.entries = u.entries[num:]
    u.offset = id.index + 1
    u.offsetInProgress = max(u.offsetInProgress, u.offset)
    u.shrinkEntriesArray()

On a hit (`UnstableHit`) the suffix loses its first `id.index + 1 - offset` entries and
`offset` moves past `id`; otherwise nothing changes. The premises are `maybeTerm`'s;
the `Logger` for the `Infof`s is `ownUnstable`'s. Which entries may be moved -- the persisted ones -- is
the caller's business (`raftLog.stableTo`'s `StableOk`). -/
abbrev unstable.stableTo.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt) (id : entryID),
  (∀ sid, us.snap = some sid → uint.Z us.offset = uint.Z sid.index' + 1) →
  uint.Z us.offset + (us.ents.length : Int) < 2^64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"stableTo")) (Val #id))
  {{ (us' : UnstableSt), RET #();
      ownUnstable u us' ∗
      ⌜(UnstableHit us id →
         us' = { us with
                 ents := us.ents.drop (uint.Z id.index' + 1 - uint.Z us.offset).toNat,
                 offset := id.index' + W64 1,
                 inprogress := w64Max us.inprogress (id.index' + W64 1) }) ∧
        (¬ UnstableHit us id → us' = us)⌝ }}

end spec

end EtcdGrove
end Perennial
