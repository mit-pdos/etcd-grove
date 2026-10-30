/-
**M2, the storage side: "no compaction at revision 0", M2's scope restriction (Draft)**
(`notes/m2-storage-plan.md`, "After review round 4", Q7 (a); `issues/etcd-restore-scheduled-compact-zero.md`).
Imported by nothing; no `axiom`, no `sorry`; nothing switched.

**Where the premise sits** (review round 4's placement, checked against the code): where a compaction
enters the log, not in mvcc (`store.Compact.spec` handles `Compact(0)` correctly, so a premise there
would be unneeded; `Restore.specM` keeps `c ≤ r.crev` as its only premise on the revision).
- **The request contract** (`EtcdServer.Compact.specD`): today's `EtcdServer.Compact.spec` with
  `⌜1 ≤ r⌝`, marked as the scope restriction. M2's compactor discharges it: both of its permits
  (`v3compactor.revPermit`, `perPermit`) carry `0 < r` (`revision.go:82` skips `rev <= 0`; the
  periodic one compacts `revs[0]` only once it is a revision the store reached, `> 0`), so
  `compactableOk_serverD` (proved) is `compactableOk_server` over the drafted spec, unchanged in its
  statement. A client's `Compact(0)` RPC (`key.go:139`, any revision) is out of M2's scope.
- **The committed log** (how `kvRaftOf` models proposals: a fold of the committed entries `A`,
  each decoded to an `IRRModel` and dispatched, `KVModelDefs.lean:372`; a compaction entry changes
  no revision of the mvcc log): the apply side's invariant of the committed entries in compaction mode
  is `plainLogC` (`CompactMode.lean`: every plain entry a plain request or `compactPropOk`), the
  vehicle. `compactPropOkD` adds `1 ≤ r` to `compactPropOk`; `Compact`'s proposal establishes it
  (`compactPropOkD_irrCompaction` from the spec's premise); `plainLogCD_compaction_pos` (proved) is the
  invariant's content: every committed compaction is at a revision `≥ 1`. So the KV model's
  compaction revision `crevOf A` (S1, the apply side's: not defined here) is `-1` or `≥ 1`, the
  images' records are past `0` (`mvcc.recsPos` in `keyImageM`), and `restore()`'s revision is `-1`
  or `≥ 1` (`mvcc.recsPos_crev`): `c ≤ r.crev` at SNAPSHOT-SORRY #8 is `crevOf_mono`, with no corner.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CompactEnv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section pure
variable [GooseExts]

/-- **A compaction request in M2's scope** (draft of `compactPropOk`): of the kind `compaction`, at a
revision `≥ 1` (M2's scope restriction, Q7 (a): no compaction at revision `0`,
`issues/etcd-restore-scheduled-compact-zero.md`). -/
def compactPropOkD (rq : apply.IRRModel) : Prop :=
  apply.dispatchKind rq = .compaction ∧ ∃ r : w64, rq.compaction = some r ∧ 1 ≤ sint.Z r

theorem compactPropOk_of_D (rq : apply.IRRModel) (h : compactPropOkD rq) : compactPropOk rq :=
  ⟨h.1, h.2.choose, h.2.choose_spec.1⟩

/-- `Compact`'s request at a revision `≥ 1` is one. -/
theorem compactPropOkD_irrCompaction (rev : w64) (h : 1 ≤ sint.Z rev) :
    compactPropOkD (irrCompaction rev) :=
  ⟨(compactPropOk_irrCompaction rev).1, rev, rfl, h⟩

/-- **A plain entry in compaction mode, M2's scope** (draft of `plainEntryC`). -/
def plainEntryCD (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    plainReq rq ∨ compactPropOkD rq

/-- Every entry, in M2's scope (draft of `plainLogC`: the committed log's invariant). -/
def plainLogCD (L : List EntryModel) : Prop := ∀ m ∈ L, plainEntryCD m

theorem plainEntryC_of_D (m : EntryModel) (h : plainEntryCD m) : plainEntryC m :=
  fun h1 h2 rq h3 => (h h1 h2 rq h3).imp id (compactPropOk_of_D rq)

/-- **Every committed compaction is past revision `0`** (the log invariant's content): a committed
entry decoding to a compaction request at `r` has `1 ≤ r` (a plain request is not a compaction:
`putgetKind`). -/
theorem plainLogCD_compaction_pos (L : List EntryModel) (hL : plainLogCD L) (m : EntryModel)
    (hm : m ∈ L) (ht : m.typ = W32 0) (hd : m.data ≠ []) (rq : apply.IRRModel)
    (hrq : apply.irrDecode m.data = some rq) (hk : apply.dispatchKind rq = .compaction) (r : w64)
    (hr : rq.compaction = some r) : 1 ≤ sint.Z r := by
  rcases hL m hm ht hd rq hrq with hp | ⟨-, r', hr', h1⟩
  · exfalso
    have := hp.2
    rw [hk] at this
    simp [putgetKind] at this
  · rw [hr] at hr'; cases hr'; exact h1

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Draft of `EtcdServer.Compact.spec` in M2's scope**: today's, for a request at a revision
`≥ 1` (**M2's scope restriction**, Q7 (a): no compaction at revision `0`; a client's `Compact(0)` RPC
is out of scope, `issues/etcd-restore-scheduled-compact-zero.md`). Its proof proposes
`irrCompaction rev`, `compactPropOkD` by `compactPropOkD_irrCompaction`, the log invariant's step. -/
abbrev EtcdServer.Compact.specD : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (r : Int),
  1 ≤ r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqC s E ρ ∗ isServerRead s E γr ∗ srvLeadTimeReader s ∗ srvLgReader s ∗ E.RD ∗
      mvcc.storeReaderC E.s E.γ ∗ idCred ρ.ids 1 ∗
      context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx none ∗ srvRevLb E.γ r ∗
      compactReqIs p r }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Compact"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗
      srvLgReader s ∗ E.RD ∗ mvcc.storeReaderC E.s E.γ ∗ compactOutIs E resp err }}

/-- Today's spec gives the drafted one (it is weaker: one premise more). -/
theorem EtcdServer.Compact.specD_of (h : EtcdServer.Compact.spec (GF := GF) (hG := hG)) :
    EtcdServer.Compact.specD (GF := GF) (hG := hG) :=
  fun s E ρ γr ctx cd p r _ => h s E ρ γr ctx cd p r

/-- **M2's compactor discharges the scope premise** (proved): the server is the compactor's
`Compactable` over the drafted spec, for the revision permit (whose `0 < r` is the premise),
statement unchanged from `compactableOk_server`. -/
theorem compactableOk_serverD (hC : EtcdServer.Compact.specD (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ret : Int) (hret : 0 ≤ ret) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqC s E ρ ∗ isServerRead s E γr ∗ idCred ρ.ids 1 ⊢
      v3compactor.compactableOk
        (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s)
        (v3compactor.revPermit (srvRevLb E.γ) ret) (srvCompactR s E) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd, #Hcred⟩
  iunfold v3compactor.compactableOk
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %r %ctx %cd %p %Φ !> ⟨Hpm, HR, #Hctx, #Htr, Hreq⟩ HΦ
  iunfold v3compactor.revPermit at Hpm
  icases Hpm with ⟨%Hr, #Hlb⟩
  iunfold srvCompactR at HR
  icases HR with ⟨Hlt, Hlr, Hrd, Hst⟩
  ihave #Hlb' : srvRevLb E.γ r $$ []
  · iapply srvRevLb_mono E.γ r (r + ret) (by omega); iexact Hlb
  iapply (hC s E ρ γr ctx cd p r (by omega)) $$ [Hlt Hlr Hrd Hst Hreq]
  · iframe Hlt Hlr Hrd Hst Hreq; iframe #
  inext
  iintro %resp %err ⟨Hlt, Hlr, Hrd, Hst, Hout⟩
  iapply HΦ
  iunfold srvCompactR
  iframe Hlt Hlr Hrd Hst
  iapply errTreeOk_of_compactOutIs; iexact Hout

end spec

end EtcdGrove
end Perennial
