/-
Port of `election_proof/spec_unstable__stableTo.v` (857d09190).

Lean notes: `unstable_hit` is `UnstableHit`.
-/
import EtcdGrove.Raft.ElectionProof.InvReadylog

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- When `u.stableTo(id)` moves entries: `id.index` is an index of the suffix and the
entry there has term `id.term`. -/
def UnstableHit [FfiSyntax] (uv : unstable) (uents : List raftpb.Entry) (id : entryID) :
    Prop :=
  (uint.Z uv.offset' ≤ uint.Z id.index' ∧
   uint.Z id.index' < uint.Z uv.offset' + (uents.length : Int)) ∧
  ∃ e, uents[(uint.Z id.index' - uint.Z uv.offset').toNat]? = some e ∧
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
`offset` moves past `id`; otherwise nothing changes. The premises are `maybeTerm`'s,
and a `Logger` for the `Infof`s. Which entries may be moved -- the persisted ones -- is
the caller's business (`raftLog.stableTo`'s `StableOk`). -/
abbrev unstable.stableTo.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents : List raftpb.Entry)
    (snap : Option entryID) (id : entryID) (ulg : GoInterfaceOk),
  (∀ sid, snap = some sid → uint.Z uv.offset' = uint.Z sid.index' + 1) →
  uint.Z uv.offset' + (uents.length : Int) < 2^64 →
  uv.logger' = interface.ok ulg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u uv uents ∗
      "#Hsnap" ∷ ownSnap uv.snapshot' snap ∗ "#Hlg" ∷ isLogger ulg }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"stableTo")) (Val #id))
  {{ (uv' : unstable) (uents' : List raftpb.Entry), RET #();
      ownUnstable u uv' uents' ∗
      ⌜uv'.snapshot' = uv.snapshot' ∧
        uv'.logger' = uv.logger' ∧
        (UnstableHit uv uents id →
         uents' = uents.drop (uint.Z id.index' + 1 - uint.Z uv.offset').toNat ∧
         uv'.offset' = id.index' + W64 1 ∧
         uv'.offsetInProgress' = w64Max uv.offsetInProgress' (id.index' + W64 1)) ∧
        (¬ UnstableHit uv uents id → uv' = uv ∧ uents' = uents)⌝ }}

end spec

end EtcdGrove
end Perennial
