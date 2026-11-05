/-
`s.applySnapshot(ep, ap)` (`server.go`), under raft's contract that a `toApply` carries no
snapshot (`rnApP`: `ap.snapshot = nil`). Lean-first (no Rocq counterpart); the request path's
unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreImageOpen
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageLeases

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.applySnapshot(ep, ap)` with no snapshot (`ap.snapshot = nil`, raft's contract): it returns
at once (`raft.IsEmptySnap(nil)`). -/
abbrev EtcdServer.applySnapshot.specEmpty : Prop :=
  ∀ (s ep ap : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      taSnapshotAddr ap ↦□ (null : Loc) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applySnapshot")) (Val #ep))
      (Val #ap))
  {{ RET #(); True }}

/-- **`s.applySnapshot(ep, ap)` with a non-empty snapshot, in the server's auth mode** (D22 receiver epochs, S8d, 2026-10-26;
`notes/snapshot-s8-plan.md`): the snapshot `sv` newer than the applied index `ai` (Go panics
otherwise), its backend file `snapDBPath ss i` holding the image `D` (its metadata, `metaIs`, at the
snapshot's index and the image's stored term `tI`, D22 J7b: until then the snapshot's
`Metadata.Term`, which the image's certificate does not give and the proof does not need, the term
only naming the consistent index's protocol at the new backend; the restored log `[[], []] ++ R` extending the KV's, by the store's mode at the image's compaction records `r`, `keyImageM`), the apply thread's resources before.
(M2's item 15, 2026-11-02) In either mode: on, the store restores over the compacted image (its
compaction right the apply thread's, at `x.crev ≤ r.crev`, back at `r.crev`), with the restored
log's receipt and the compaction permits at the records as premises; off, as before.
`OpenSnapshotBackend` opens the new backend, `ci.SetBackend` swaps the consistent index's (the
protocol's names move to `futPhys π0 γB`), the KV, the lessor, the alarm and auth stores and the
cluster recover from it, `s.be` is swapped under `bemu`, the old backend is closed in a goroutine
(with its stop channels and the constructors' half of its open token, W7, and the readers' and the
monitor's shares the swap gathers), the transport's peers are removed and the members re-added
(W8), and `NewUberApplier` rebuilds the applier: `srvSnapApplied`. Named premises (S-j1's to
discharge): the image's facts (`hmeta`, `hkI`, `hRok`, `hpre`, `hlease`, `hlp`, `halarm`,
`hmemb`, `himg`, `hA'`, `hAA'`, `hlnil`, `hauthI`), the server's auth mode (`hany`), the auth store's `Recover` facts
(`snapAuthResM`), the members' directory (`srvMembersDir`) (until J8a-6, 2026-11-01, also `8·|ps|` reader
slots of the transport's `lgMu`), the KV's closer, `NewUberApplier`'s fields and feature gate, the stores' contracts on
whichever backend (`alarmApplyOk`, `authApplyOkM`, `lessorApplyOk`, `clusterApplyOk`).

(F9, the user's decision of 2026-11-03: one spec over `E.authMode`; until 2026-11-03 also the
mode-off twin `specSnap`, this statement's `off` case) The mode-dependent parts are indexed by
`E.authMode`: the server's and the applier's rows (`isServerM E.authOn`,
`srvApplyKVM` at the applied log's auth state), the rest model's buckets (`snapRestImgM`: on, all
but the auth ones), the image's auth facts (`snapAuthImgM`: off, `hauthb`; on, the auth buckets at
the state after the image's log `A'`, `A <+: A'`), `Recover`'s facts (`snapAuthResM`: off,
`authRecoverOk`; on, the store's invariant at the server's `E.RD` with the snapshot clause
`authSchemaSnap` and the committed `A'`), the apply contract in the mode, the open share
(`srvOpenQ`). After: `srvSnapAppliedM` (on, the applier at the image's auth state).

With auth on, `srvApplyKVOn`'s auth part `authApplyResB (.on γa)` holds the fuel at a base, the
token's lifecycle and the hook clause (`authInstallPre`), which `Recover`'s glue needs and gives
back (P6.2; the plan note's findings 1 and 2). -/
abbrev EtcdServer.applySnapshot.specSnapM : Prop :=
  ∀
    (s ep ap sn : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai at0 dsi : w64) (nc : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss hk : Loc)
    (hi : uint.Z ai < uint.Z sv.Metadata'.Index')
    (d : mvcc.KBReal) (D : backend.Data) (lgh : Loc)
    (hkb : E.γ.kb = some d)
    (hdbo : storage.dbOpensOk) (hsop : storage.snapOpensOk)
    (hP : d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧ ciKeys d.P ∧ storage.hooksParams d.P)
    (hcfgl : cfg.Logger' ≠ null) (hmmap : storage.openMmapOk cfg)
    (tI : w64) (hmeta : metaIs D (sv.Metadata'.Index', tI))
    (st : ApplyState) (b : GoInterface)
    (hle : uint.Z (ciEff γ st.k) ≤ uint.Z sv.Metadata'.Index')
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (hRO : E.RO = srvRestOwnH E.authMode d.γB cl (srvObjsOn al ast lp cl d.be))
    (hwq : E.γ.watchQ = true)
    (R : mvcc.Log) (hpre : x.log <+: [[], []] ++ R) (hRok : mvcc.restoreLogOk R)
    -- (since M2's item 15) the image by the store's mode at its compaction records
    -- `r`, on past the store's compaction revision
    (r : mvcc.CmpRecs) (hcc : d.cm = true → x.crev ≤ r.crev)
    (hkI : mvcc.keyImageM d.cm ([[], []] ++ R) r D) (hbr : mvcc.bridgeParams d.P)
    -- (the lease-revoke plan, 2026-10-31) the `Lease` bucket in the table, tracked, no hook keys
    -- (the boot backend's, `bootOk`; the new backend's parameters are the old one's)
    (hlp : mvcc.leaseParams d.P)
    (γp : WTNames) (hrbw : receiptBound GF ≤ backend.wbInit - 6)
    (stp : Loc) (γd γt : GName) (img : w64 → backend.Data → IProp GF) (nt : Nat)
    (hstp : storage.storageSnap stp ss) (hnt : nt ≤ uint.nat sv.Metadata'.Index')
    (halarm : ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅)
    -- (the backend-auth-split stage) the alarm bucket in the table
    (halbi : d.P.has mvcc.alarmBI ∧
      d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI)
    (hmemb : ((backend.rbData d.P D).lookup go!"members").isSome ∧
      ((backend.rbData d.P D).lookup go!"members_removed").isSome ∧
      ((backend.rbData d.P D).lookup go!"cluster").isSome)
    (memI : GMap w64 apply.MemberM)
    (himg : membership.clusterImageOk cl (backend.rbData d.P D) memI)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (dir : w64 → List GoString)
    (ps : List w64) (idm : w64)
    (hdir : γn.dir = dir) (hdok : netDirOk dir) (hps : ∀ f, dir f ≠ [] ↔ f ∈ ps)
    (hlid : c.lid = idm)
    (msi : w64) (cs0 : Loc) (fg : GoInterface) (quota : w64) (wad : time.Duration)
    (hbuq : apply.backendUnderQuota)
    -- (S8d's named premise, S-j1's) the snapshot's entries `A'`: the rest model after them is the
    -- image's rest buckets, with the `lease` and `alarm` buckets set to empty (the rest model holds
    -- neither: their contents are the lessor's and the alarm store's), and the decoded members
    (A' : List EntryModel)
    -- (the lease-expiry plan's S2–S4, review r1 F1, 2026-11-05) in either auth mode, the image's log
    -- extends the applied one (until then the `on` arm's alone, `snapAuthImgM`)
    (hAA' : A <+: A')
    (hA' : snapRestImgM E.authOn γr d.P D A' ∧
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI)
    -- (the lease-expiry plan's S2–S4, 2026-11-05: until then the bucket empty, at a cluster that
    -- grants none) the image's lease bucket the records of its log's live leases
    (hlease : imageLeasesAt γr d.P D A')
    -- (review r1 F2) in a cluster that grants none, the image's log grants none (its table empty;
    -- the receive side's `snapRecv_image(On)`, from the committed log's plain mode)
    (hlnil : E.lg = false → (appliedTable γr A').ids = [])
    -- (F9) a mode the server runs in (the convention: `EtcdServer__apply.lean:44`), and the image's
    -- auth facts by it (`off`: lean's `hauthb`; `on`: `snapRecv_imageOn`'s), in place of `hoff`
    (hany : E.authMode ≠ .any) (hauthI : snapAuthImgM E.authMode γr d.P D A A')
    -- (2026-11-01, J8a-1, item 8) the payload's two-receive `notifyc` (`rnApSnap`'s), before its
    -- first receive (until then a unit bag)
    (γnc : NotifyNames),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       isServerM E.authOn s γ ci TM E ρ γr ∗
       taSnapshotAddr ap ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
       taNotifycAddr ap ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
       epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epDiskSnapAddr ep ↦ dsi ∗
       srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
       -- the apply thread's token, given back
       threadTok ∗
       srvCfgAddr s ↦□ cfg ∗ structFieldRef EtcdServer go!"snapshotter" s ↦□ ss ∗
       structFieldRef EtcdServer go!"beHooks" s ↦□ hk ∗
       snap.isSnapshotter ss ∗ backend.fileHolds (snap.snapDBPath ss sv.Metadata'.Index') D ∗
       backend.pathOwn (config.backendPathOf cfg.DataDir') ∗
       (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
       storage.isBackendHooks hk
         ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #ci⟩ lgh ∗
       applyThread γ st ∗ applyBackend γ ci b ∗
       srvApplyKVM E.authOn s E ρ.wait x (srvAuthAtLog γr.kv srvAuthSt0 A) ∗ srvRest E γr A ∗
       -- (S2–S4, review r1 F1) in either auth mode, the image's log committed (until then the `on`
       -- arm's alone, `snapAuthResM`)
       srvRLogLb γr.raft A' ∗
       lease.lessorInv lp E.γ.leases ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
       -- (the lease-grant plan's D2, 2026-11-02) the lessor's mode, `Recover`'s premise (the
       -- lease-expiry plan's S2–S4, Q-S5, 2026-11-05: the environment's, `srvSnapRO`'s; until then
       -- revocable, which only a cluster that grants none had)
       lease.lessorModeIs E.γ.leases (decide (E.lm = .mono)) ∗
       -- (M2's item 15) the server's closer by the mode (on, the watchable store's own parts: the
       -- store's right is the apply thread's, `srvApplyKV`'s compaction resources)
       srvKVCloserW s E ∗
       (∃ (wsl : Loc) (γw0 : mvcc.WsNames), srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
        mvcc.isWatchableStore wsl E.s γw0) ∗
       mvcc.certOk E.γ ([[], []] ++ R) ∗
       -- on, the restored log's receipt and the compaction permits at the records
       mvcc.restoreRcptM d ([[], []] ++ R) ∗ mvcc.crevPermAt E.γ r.finRev ∗ mvcc.crevPermAt E.γ r.crev ∗
       □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b) ∗ srvWTPool E γp ∗
       rnStorageAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.storage.storage.ty) #stp : GoInterface) ∗
       -- (2026-11-01, J8a-1, item 8) the directory's removal fact `srvSnapRm`, as the server's
       -- bundle (`srvSnapRO`) has it (until then `snapTakenLb γt`, its first disjunct)
       inv snapDirN (snapDirInv ss γd img (srvSnapRm γt γr)) ∗ monoNatAuthOwn γt 1 nt ∗
       srvAlarmStoreAddr s ↦□ al ∗ isAlarmStore al ∗
       srvAuthStoreAddr s ↦□ auth.authIface ast ∗ srvClusterAddr s ↦□ cl ∗
       membership.isRaftCluster cl ∗
       rnTransportAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t : GoInterface) ∗
       trLive γn t c rs ∗ srvMemberIDAddr s ↦□ idm ∗
       srvMembersDir cl ps dir ∗
       epMemSnapAddr ep ↦ msi ∗ epConfState ep cs0 ∗
       srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗ isFeatureGate fg ∗
       srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ quota ∗
       srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ wad ∗
       -- (review R1's F1, decision 5) the apply thread's quarter
       srvStopChans γ d ∗ backend.bOpen d.γB (srvOpenQ E.authMode) ∗
       -- (F9) the auth store's `Recover` facts by the mode (`off`: `authRecoverOk`; `on`, Q2's
       -- candidate (ii): the store's invariant at the server's `E.RD` with the snapshot clause,
       -- and the image's committed log)
       snapAuthResM E.authMode s ast E.RD γr A' ∗
       -- (S8d's named premises, S-j1's: `NewServer`'s contracts of the stores on whichever backend)
       alarmApplyOk al ∗ authApplyOkM E.authMode ast E.RD ∗ lessorApplyOk lp ∗ clusterApplyOk cl ∗
       lease.lessorCfg lp ∗ lessorLookupOk lp ∗ (∃ n : Loc, membership.rcVersionChangedAddr cl ↦□ n) ∗
       -- (J8a-4, 2026-11-01, the user's decision: `notes/decisions.md`, "J8a-4") the meta reads of
       -- a backend the apply thread opens at the protocol's names `π` over an image whose meta keys
       -- are `π.m0`, from its fresh keys and payment rights (until then of any backend at any names
       -- with `π.m0` the snapshot's, false)
       □ (∀ (π : ApplyPhys) (γB : backend.BNames) (P : backend.BParams) (D : backend.Data),
         ⌜ciKeys P ∧ metaIs D π.m0 ∧ π.bwb = γB.wb ∧ π.bopn = γB.opn⌝ -∗
         backend.hkOwn γB (backend.hkData P D) -∗ backend.bFresh γB -∗
         backend.hkOwn γB (backend.hkData P D) ∗ backend.bFresh γB ∗
         □ ∀ (W : IProp GF) (b : Loc),
           backend.isBackend γB P W (batchLockInv (γ.withPh π) (metaTM γB P)) b -∗
           isMetaBackend (interface.mkOk (go.GoType.PointerType
             go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) (⊤ \ ↑applyN)
             (readView (γ.withPh π))) }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applySnapshot")) (Val #ep))
        (Val #ap))
    {{ RET #(); srvSnapAppliedM E.authOn s ep sv γ ci E ρ γr d R r A' ss (config.backendPathOf cfg.DataDir') γt γn t c rs idm lp al ast cl ∗
      notifyRcvN γnc 1 ∗ threadTok }}

/-- **`applySnapshot`'s spec** (J8b, 2026-11-01): both cases, the empty snapshot (`specEmpty`) and a
non-empty one in the server's auth mode (`specSnapM`; until 2026-11-03 the mode-off `specSnap`), for
the link. -/
abbrev EtcdServer.applySnapshot.spec : Prop :=
  EtcdServer.applySnapshot.specEmpty (GF := GF) (hG := hG) ∧
    EtcdServer.applySnapshot.specSnapM (GF := GF) (hG := hG)

end spec

end EtcdGrove
end Perennial
