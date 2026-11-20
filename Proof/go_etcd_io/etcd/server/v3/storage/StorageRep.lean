/- Lean-first (no Rocq counterpart).

# The server's WAL storage (`server/storage/storage.go`; wal-link L2, 2026-11-17, `notes/wal-link-scope.md` §2)

`NewStorage(lg, w, s)` returns a fresh `*storage{lg, s, mux, w}`; its methods take `st.mux` (the read lock
for `Save`, `SaveSnap`, `Sync`, `Release`, the write lock for `Close`) and call the WAL's (and, for
`Release`, the snapshotter's) method. The representation:

* `storagePw p w q`: the fraction `q` of the field `p.w ↦ w`, which `st.mux` guards (`MinimalEtcdVersion`, not
  verified and never reached by the server's runs, `notes/wal-link-handoff.md` "R6", reassigns it under the
  write lock);
* `storageOver p w ss` (persistent): the snapshotter field `p.s ↦□ ss` and the persistent guard of `st.mux`
  over `storagePw p w` (what the write lock, `Close`'s, needs);
* `storageRd p w`: a reader token of `st.mux` (`ownRWMutex`). `NewStorage` hands out exactly two, one for each
  thread that uses the storage under the read lock: etcd's raft loop (`Save`, `SaveSnap` of a received
  snapshot, `Sync`, S/etcdserver/raft.go:257-280) and its apply thread (`SaveSnap`, `Release`,
  S/etcdserver/server.go:1122, 2158-2163). A method takes its caller's token and gives it back, so no thread
  bound is needed (CLAUDE.md, "Bounds").

The WAL handle itself (`walOpenWS`) is not the storage's: its callers hold shares of it and pass them through,
as the WAL's methods serialize on `w.mu`.

`SaveSnap` shares raft's metadata objects (the `Index`/`Term` cells and the conf state) in the
`walpb.Snapshot` it builds (S/storage/storage.go:63-68): `metaWalC m` is that record's content for a frozen
metadata of content `m` (`metaRoC`, raft's `PbContent`), and `walSnapAt_storageLit` the record frozen.
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.storage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Perennial.Proof.sync.RWMutexGuard
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PbSnapshot
public import Proof.go_etcd_io.raft.v3.PbContent

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace storage

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 WalEnc

/-! ## The record `SaveSnap` builds -/

/-- **A raft conf state's content as the WAL's.** -/
def csWalC (c : CSC) : WalCsC := ⟨c.voters, c.learners, c.votersOutgoing, c.learnersNext, c.autoLeave, c.uf⟩

/-- **The content of `walpb.Snapshot{Index, Term, ConfState}` built from a metadata of content `m`**
(the pointers shared, no unknown fields: a fresh struct). -/
def metaWalC [GooseExts] (m : SnapMetaC) : WalSnapC := ⟨m.index, m.term, m.confState.map csWalC, []⟩

theorem csWalC_model (c : CSC) : (csWalC c).model = c.model := rfl

theorem metaWalC_model [GooseExts] (m : SnapMetaC) : (metaWalC m).model = m.model := by
  obtain ⟨oc, oi, ot, uf⟩ := m
  cases oc <;> rfl

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The fraction `q` of the storage's WAL field** (see the file header). -/
def storagePw (p w : Loc) (q : Qp) : IProp GF :=
  typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.storage.storage go!"w" p) w (DFrac.own q)

instance storagePw_fractional (p w : Loc) : Fractional (storagePw (GF := GF) p w) :=
  fractional_of_dfractional
    (fun dq => typedPointsto (GF := GF) (structFieldRef go_etcd_io.etcd.server.v3.storage.storage go!"w" p) w dq)

instance storagePw_timeless (p w : Loc) (q : Qp) : Timeless (storagePw (GF := GF) p w q) := by
  unfold storagePw; infer_instance

/-- **The storage `p` over the WAL `w` and the snapshotter `ss`** (persistent; see the file header). -/
def storageOver (p w ss : Loc) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.server.v3.storage.storage go!"s" p ↦□ ss ∗
    sync.isRWMutexGuard (structFieldRef go_etcd_io.etcd.server.v3.storage.storage go!"mux" p) (storagePw p w))

instance storageOver_persistent (p w ss : Loc) : Persistent (storageOver (GF := GF) p w ss) := by
  unfold storageOver; infer_instance

/-- **A reader token of the storage's lock** (see the file header). -/
def storageRd (p w : Loc) : IProp GF :=
  sync.ownRWMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.storage go!"mux" p) (storagePw p w)

/-- Two of a lock's reader slots (it has at least two). -/
theorem slots_two (R : IProp GF) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), R) ⊢ R ∗ R := by
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 2 :=
    ⟨_, (Nat.sub_add_cancel sync.actualMaxReaders_ge_2).symm⟩
  rw [hm, List.replicate_succ, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, -⟩
  iframe H1 H2

theorem optCell_recCell {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (o : Option V) :
    optCell (GF := GF) p o = recCell p o := by
  cases o <;> rfl

theorem pbMsg_walCsHidden (p : Loc) (uf : List w8) :
    pbMsg (GF := GF) raftpb.ConfState p uf ⊢ walCsHidden p uf := by
  unfold pbMsg walCsHidden
  simp only [pbN, PbGoType.goTy, pbSchemaOf_confState]
  exact .rfl

/-- **A frozen raft conf state is the WAL's** (the same fields; raft's `pbMsg` at the conf state's schema is
the WAL's `walCsHidden`). -/
theorem csRoC_walCsRoC (p : Loc) (c : CSC) : csRoC (GF := GF) p c ⊢ walCsRoC p (csWalC c) := by
  unfold csRoC walCsRoC
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hn, #HV, #Hv, #HL, #Hl, #HO, #Ho, #HN, #Hn', #HA, #Hc, #Hpb⟩
  iexists sv, sl, so, sn, pa
  simp only [csWalC]
  isplitr
  · ipureintro; exact Hn
  iframe HV Hv HL Hl HO Ho HN Hn' HA
  rw [← optCell_recCell]
  iframe Hc
  iapply pbMsg_walCsHidden $$ Hpb

theorem csOptC_walCsOptRoC (p : Loc) (o : Option CSC) :
    csOptC (GF := GF) p o ⊢ walCsOptRoC p (o.map csWalC) := by
  cases o with
  | none => simp only [csOptC, walCsOptRoC, Option.map_none]; exact .rfl
  | some c => simp only [csOptC, walCsOptRoC, Option.map_some]; exact csRoC_walCsRoC p c

end defs

section lit
open go_etcd_io.etcd.server.v3.storage.wal
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [walpb_sem : go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- **`SaveSnap`'s record frozen** (as `walSnapAt_lit`, `Create`'s): the literal over the cells and the conf
state of a frozen metadata of content `m` with `Index` and `Term` set, whose bytes are the client's
marshaller's of its model (the premise on the conf state's content, `notes/wal-link-scope.md` F2), is
`walSnapAt Mr l m.model`, the conf state present iff `m`'s is. -/
theorem walSnapAt_storageLit (Mr : WalMarshal) (m : SnapMetaC) (l pi pt pc : Loc) (i t : w64)
    (st : google_golang_org.protobuf.internal.impl.MessageState) (sc : w32)
    (hi : m.index = some i) (ht : m.term = some t) (al : Bool) (henc : snapEnc (metaWalC m) = Mr.encSnap m.model al) :
    ⊢ l ↦ (walpb.Snapshot.mk st pi pt pc slice.nil sc) -∗ pi ↦□ i -∗ pt ↦□ t -∗
      csOptC (GF := GF) pc m.confState ={⊤}=∗ walSnapAt (GF := GF) Mr l m.model al m.confState.isSome := by
  iintro Hl #Hi #Ht #Hc
  ihave #Hc' := csOptC_walCsOptRoC pc m.confState $$ Hc
  ihave ⟨Hl, %Hln⟩ := typedPointsto_not_null_dup _ _ _ $$ Hl
  iStructNamed Hl
  ipersist Index
  ipersist Term
  ipersist ConfState
  imod inv_alloc (nroot.@"protobuf") ⊤ (iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
      (sc : w32) (us : GoSlice),
    l.[walpb.Snapshot, go!"state"] ↦ st ∗ l.[walpb.Snapshot, go!"sizeCache"] ↦ sc ∗
      l.[walpb.Snapshot, go!"unknownFields"] ↦ us ∗ us ↦* ([] : List w8))) $$ [state sizeCache unknownFields]
    with #Hinv
  · inext
    iexists st, sc, slice.nil
    iframe
    iapply ownSlice_nil
  imodintro
  iunfold walSnapAt
  iexists metaWalC m
  isplitl
  · iunfold walSnapRoC
    iexists pi, pt, pc
    simp only [metaWalC, hi, ht, recCell, snapHidden]
    isplitr
    · ipureintro; exact Hln
    iframe #
    ipureintro; exact ufWire_nil _
  ipureintro
  refine ⟨metaWalC_model m, ?_, ?_, ?_, henc⟩
  · simp only [metaWalC, hi, SnapMetaC.model, Option.getD_some]
  · simp only [metaWalC, ht, SnapMetaC.model, Option.getD_some]
  · simp only [metaWalC, Option.isSome_map]

end lit

section getter
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [raftpb_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- **`GetConfState()` of a set metadata reads its field** (raftpb's getter, `raftpb/raft.pb.go`: `nil` only
for a nil receiver; as raft's `wp_SnapshotMetadata_GetConfState_field`, here without raft's package
assumptions, which the storage package does not have). -/
theorem wp_SnapshotMetadata_GetConfState_fieldS (pm pc : Loc) (dq : DFrac) (Hnn : pm ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        pm.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc }}
      (App (Val (pm @!! go.GoType.PointerType raftpb.SnapshotMetadata.ty @!! go!"GetConfState"))
        (Val #()))
    {{ RET #pc; pm.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc }} := by
  wp_start as HC
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · iapply HΦ
    iframe HC

end getter

end storage
end EtcdGrove
end Perennial
