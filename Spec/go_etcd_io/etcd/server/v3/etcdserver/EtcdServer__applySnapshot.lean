/-
`s.applySnapshot(ep, ap)` (`server.go`), under raft's contract that a `toApply` carries no
snapshot (`rnApP`: `ap.snapshot = nil`). Lean-first (no Rocq counterpart); the request path's
unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageLeases
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver
open mvcc.api (isMvcc mvccImage mvccLeases)

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
only naming the consistent index's protocol at the new backend), the apply thread's resources
before. (Strict M1, 2026-11-06: over mvcc's API, the draft's §3c-§3d) The image is the
certificate's (`dbImage`, unpacked: the committed log `A'` extending the applied `A`, mvcc's
`mvccImage` of its model's history and compaction revision, recording an unfinished compaction iff
`u`, the state reachable and short, `imageStOk`, and that compaction revision's permit `E.Cp`): the
proof opens the new backend over it (`dbImageA_open.law`, over `etcdStorage_open.law`) and restores
the store by `KV.Restore.contract` at the update `kvAus`' restore builder makes
(`restoreArgs.law`), its open token the apply thread's (`apply.cmpOwn`), the old backend's share
the apply thread's (`apply.kvBk`). Until then the store's internals: the restored log `[[], []] ++
R`, its key image at the records `r` (`keyImageM`), `restoreLogOk`, the receipt `restoreRcptM`, the
permits `crevPermAt`, the store's certificate `certOk`, the KV's closer `srvKVCloserW` and the
watchable store `isWatchableStore`, the store's backend `E.γ.kb = some d` and watch flag. (The
mvcc merge, 2026-11-06: the KV's model by the auth mode, `kvModelM E.authOn`.)
`OpenSnapshotBackend` opens the new backend, `ci.SetBackend` swaps the consistent index's (the
protocol's names move to `futPhys π0 γB`), the KV, the lessor, the alarm and auth stores and the
cluster recover from it, `s.be` is swapped under `bemu`, the old backend is closed in a goroutine
(with its stop channels and the constructors' half of its open token, W7, and the readers' and the
monitor's shares the swap gathers), the transport's peers are removed and the members re-added
(W8), and `NewUberApplier` rebuilds the applier: `srvSnapApplied`. Named premises (S-j1's to
discharge): the image's facts (`hmeta`, `hxA`, `hst`, `hnl`, `hlease`, `hlp`, `halarm`,
`hmemb`, `himg`, `hA'`, `hAA'`, `hauthI`), the applied log's prefix and lease mode (`hpre0`, `hlmk`),
the server's auth mode (`hany`), the auth store's `Recover` facts
(`snapAuthResM`), the members' directory (`srvMembersDir`) (until J8a-6, 2026-11-01, also `8·|ps|` reader
slots of the transport's `lgMu`), `NewUberApplier`'s fields and feature gate, the stores' contracts on
whichever backend (`alarmApplyOk`, `authApplyOkM`, `lessorApplyOk`, `clusterApplyOk`).

(F9, the user's decision of 2026-11-03: one spec over `E.authMode`; until 2026-11-03 also the
mode-off twin `specSnap`, this statement's `off` case) The mode-dependent parts are indexed by
`E.authMode`: the server's and the applier's rows (`isServerM E.authOn`,
`srvApplyKVM` at the applied log's auth state), the rest model's buckets (`snapRestImgM`: on, all
but the auth ones), the image's auth facts (`snapAuthImgM`: off, `hauthb`; on, the auth buckets at
the state after the image's log `A'`), `Recover`'s facts (`snapAuthResM`: off,
`authRecoverOk`; on, the store's invariant at the server's `E.RD` with the snapshot clause
`authSchemaSnap`), the apply contract in the mode, the open share
(`srvOpenQ`). After: `srvSnapAppliedM` (on, the applier at the image's auth state).

With auth on, `srvApplyKVOn`'s auth part `authApplyResB (.on γa)` holds the fuel at a base, the
token's lifecycle and the hook clause (`authInstallPre`), which `Recover`'s glue needs and gives
back (P6.2; the plan note's findings 1 and 2).

(R2d'a swap batch 2, 2026-11-06, the restart form; review F1, the swap the user approved) The rest
buckets are at any image `r0` of `A`'s table (`srvRestRp E γr A r0`): inside a restart window the
apply thread's rest buckets are at the replay's image (`srvRestR`'s arm, `restReplay`), not the
model of the ghost log. `applySnapshot` reads the old image only through `E.RO` and drops it. At
`r0` the model of `A` this is the statement before the swap (`srvRestRp_model`, a first start's). -/
abbrev EtcdServer.applySnapshot.specSnapM : Prop :=
  ∀
    (s ep ap sn : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai at0 dsi : w64) (nc : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss hk : Loc)
    (hi : uint.Z ai < uint.Z sv.Metadata'.Index')
    (d : mvcc.KBReal) (D : backend.Data) (lgh : Loc)
    (hkb : E.BkTie = srvBkTie d)
    (hdbo : storage.dbOpensOk) (hsop : storage.snapOpensOk)
    (hP : d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧ ciKeys d.P ∧ storage.hooksParams d.P)
    (hmmap : storage.openMmapOk cfg)
    (tI : w64) (hmeta : metaIs D (sv.Metadata'.Index', tI))
    (st : ApplyState) (b : GoInterface)
    (hle : uint.Z (ciEff γ st.k) ≤ uint.Z sv.Metadata'.Index')
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    -- (R2d'a swap batch 2, 2026-11-06) the rest buckets' image `r0`: any, at `A`'s table
    -- (`srvRestRp`; until then the model of `A`, `srvRest E γr A`, its instance `srvRestRp_model`)
    (r0 : apply.RestM)
    (hRO : E.RO = srvRestOwnH E.authMode d.γB cl (srvObjsOn al ast lp cl d.be))
    -- (strict M1, 2026-11-06) the image's committed log `A'` (bound below, `hAA'`), the KV at the
    -- applied `A`'s model (`kvApplied`'s; the mvcc merge: by the mode), the image's state reachable
    -- and short (`dbImage`'s `imageStOk`), recording an unfinished compaction iff `u`
    (A' : List EntryModel) (u : Bool)
    (hxA : x.log = kvModelM E.authOn γr.kv A ∧ x.crev = crevOf γr.kv A)
    (hst : imageStOk (kvModelM E.authOn γr.kv A') (crevOf γr.kv A'))
    -- (strict M1's, kept by R4, 2026-11-07) the image's history attaches no lease to a key (the
    -- server's KV model's, `kvRaftOf_restorable`: leases are granted and revoked, `hlease` and
    -- `lessor.Recover` restore their records, but no put carries one), so `KV.Restore.contract` has
    -- no pending item, and its `leaseOwn (mvccLeases E.γ) L ∅` is met at `Recover`'s live set
    (hnl : mvcc.LogNoLease (kvModelM E.authOn γr.kv A'))
    (hbr : mvcc.bridgeParams d.P)
    -- (the lease-revoke plan, 2026-10-31) the `Lease` bucket in the table, tracked, no hook keys
    -- (the boot backend's, `bootOk`; the new backend's parameters are the old one's)
    (hlp : mvcc.leaseParams d.P)
    (γp : WTNames) (hrbw : receiptBound GF ≤ backend.wbInit - 6)
    (stp : Loc) (γd γt : GName) (img : w64 → backend.Data → IProp GF) (nt : Nat)
    (hstp : storage.storageSnap stp ss) (hnt : nt ≤ uint.nat sv.Metadata'.Index' + 1)
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
    -- (S8d's named premise, S-j1's) at the snapshot's entries `A'`: the rest model after them is
    -- the image's rest buckets, with the `lease` and `alarm` buckets set to empty (the rest model
    -- holds neither: their contents are the lessor's and the alarm store's), and the decoded members
    -- (the lease-expiry plan's S2–S4, review r1 F1, 2026-11-05) in either auth mode, the image's log
    -- extends the applied one (until then the `on` arm's alone, `snapAuthImgM`)
    (hAA' : A <+: A')
    (hA' : snapRestImgM E.authOn γr d.P D A' ∧
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI)
    -- (the lease-expiry plan's S2–S4, 2026-11-05: until then the bucket empty, at a cluster that
    -- grants none) the image's lease bucket the records of its log's live leases
    (hlease : imageLeasesAt γr d.P D A')
    -- (the lease-expiry plan's S2–S4, Probe 4, DRAFT 2026-11-05) the applied log after an empty
    -- prefix (`applyAll`'s raft names) and the KV names' lease mode the environment's
    -- (`srvSnapRO`'s): what the granting walk's table lemmas take (`ImageLeases.lean`)
    (hpre0 : γr.raft.pre = []) (hlmk : E.lm = γr.kv.lm)
    -- (F9) a mode the server runs in (the convention: `EtcdServer__apply.lean:44`), and the image's
    -- auth facts by it (`off`: lean's `hauthb`; `on`: `snapRecv_imageOn`'s), in place of `hoff`
    (hany : E.authMode ≠ .any) (hauthI : snapAuthImgM E.authMode γr d.P D A A')
    -- (2026-11-01, J8a-1, item 8) the payload's two-receive `notifyc` (`rnApSnap`'s), before its
    -- first receive (until then a unit bag)
    (γnc : NotifyNames),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       isServerM E.authOn s γ ci TM E ρ γr ∗
       taSnapshotAddr ap ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
       -- (sweep repairs 1, W2) the first receive's payload: the storage's WAL records at or
       -- above the snapshot's index (what `Release` takes)
       taNotifycAddr ap ↦□ nc ∗ isNotify2 γnc nc
         (walBaseLb (storage.walOf (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.storage.storage.ty) #stp)) (uint.nat sv.Metadata'.Index')) iprop(True) ∗
       notifyRcvN γnc 0 ∗
       epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epDiskSnapAddr ep ↦ dsi ∗
       srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
       -- the apply thread's token, given back
       threadTok ∗
       -- (premise-fixes-6, until then the pure premise `cfg.Logger' ≠ null`) the configuration's
       -- logger a zap logger (`OpenSnapshotBackend`'s `openPre`)
       srvCfgAddr s ↦□ cfg ∗ zapLoggerOk cfg.Logger' ∗ structFieldRef EtcdServer go!"snapshotter" s ↦□ ss ∗
       structFieldRef EtcdServer go!"beHooks" s ↦□ hk ∗
       snap.isSnapshotter ss ∗ backend.fileHolds (snap.snapDBPath ss sv.Metadata'.Index') D ∗
       backend.pathOwn (config.backendPathOf cfg.DataDir') ∗
       (⌜cfg.ServerFeatureGate' = GoInterface.nil⌝ ∨ isFeatureGate cfg.ServerFeatureGate') ∗
       -- (sweep repairs 1, B4) `ETCD_VERIFY` off (`OpenSnapshotBackend`'s `openPre`)
       envVerifyOff ∗
       storage.isBackendHooks hk
         ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #ci⟩ lgh ∗
       applyThread γ st ∗ applyBackend γ ci b ∗
       srvApplyKVM E.authOn s E ρ.wait x (srvAuthAtLog γr.kv srvAuthSt0 A) ∗ srvRestRp E γr A r0 ∗
       -- (S2–S4, review r1 F1) in either auth mode, the image's log committed (until then the `on`
       -- arm's alone, `snapAuthResM`)
       srvRLogLb γr.raft A' ∗
       lease.lessorInv lp (mvccLeases E.γ) ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
       -- (the lease-grant plan's D2, 2026-11-02) the lessor's mode, `Recover`'s premise (the
       -- lease-expiry plan's S2–S4, Q-S5, 2026-11-05: the environment's, `srvSnapRO`'s; until then
       -- revocable, which only a cluster that grants none had)
       lease.lessorModeIs (mvccLeases E.γ) (decide (E.lm = .mono)) ∗
       -- (strict M1, 2026-11-06) the KV the store's handle (`srvSnapRO`'s); mvcc's image of the
       -- image's committed log's model, its compaction revision's permit (`dbImage`'s, with `hAA'`,
       -- `hst`; `snapRecv_image`). Until then the KV's closer `srvKVCloserW` (
       -- over the API, the apply thread's `mvccOpen E.γ`), the watchable store, `certOk`, the
       -- restored log's receipt and the compaction permits at the records.
       srvKVAddr s ↦□ E.kv ∗
       mvccImage D (kvModelM E.authOn γr.kv A') (crevOf γr.kv A') u ∗ E.Cp (crevOf γr.kv A') ∗
       □ (∀ (γB : backend.BNames) (b : Loc), mvcc.keySized γB d.P b) ∗ srvWTPool E γp ∗
       rnStorageAddr (srvRAddr s) ↦□ (interface.mkOk (go.GoType.PointerType
         go_etcd_io.etcd.server.v3.storage.storage.ty) #stp : GoInterface) ∗
       -- (2026-11-01, J8a-1, item 8) the directory's removal fact `srvSnapRm`, as the server's
       -- bundle (`srvSnapRO`) has it (until then `snapTakenLb γt`, its first disjunct); (restart
       -- S6a) the member's removal counter `γt` (`snapRmM`), its authority at most the index plus one
       inv snapDirN (snapDirInv ss γd img (snapRmM γt)) ∗ monoNatAuthOwn γt 1 nt ∗
       srvAlarmStoreAddr s ↦□ al ∗ isAlarmStore al ∗
       srvAuthStoreAddr s ↦□ auth.authIface ast ∗ srvClusterAddr s ↦□ cl ∗
       membership.isRaftCluster cl ∗
       -- (premise-fixes-6) the cluster's logger, a zap logger (`RaftCluster.Recover`'s)
       (∃ lgc : Loc, membership.rcLgAddr cl ↦□ lgc ∗ zapLoggerOk lgc) ∗
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
    {{ RET #(); srvSnapAppliedM E.authOn s ep sv γ ci E ρ γr d A' ss (config.backendPathOf cfg.DataDir') γt γn t c rs idm lp al ast cl ∗
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
