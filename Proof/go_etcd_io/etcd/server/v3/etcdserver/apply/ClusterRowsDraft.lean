/-
**The cluster contract's rows, restated (Draft)** (the cluster-rows stage, 2026-11-02;
`notes/cluster-rows-plan.md`). Imported by nothing; no `axiom`, no `sorry`; nothing switched. Each
`…D` drafts the unsuffixed statement it names, to replace it in place at the switch; a new name
(`semverAtMostServer`, `restReqOk`) is the name it will have.

The rows of `apply.isCluster` (`Contracts.lean`) that the server's `bootOk` asserts of the real
`*membership.RaftCluster` (`clusterApplyOk`), restated where they are false of Go at the fork pin
(`notes/decisions.md`, "Defects of the applied cluster contract"; the Go tests
`clr_rows_test.go` of the stage):

* **`SetVersion`** takes the caller's `onSet` as any value and any version: Go calls `onSet`
  (`cluster.go:623`) and `MustDetectDowngrade` panics for a version above the server's
  major.minor (`downgrade.go:48-53`). Restated: `onSet` is `api.UpdateCapability`, the function
  the one caller passes (`apply/backend.go:273`); the version not above the server's
  (`semverAtMostServer`, opaque, as `semverValid`: the monitor's axiom is the only source).
* **`UpdateAttributes`** of an id that is neither a member nor removed panics
  (`cluster.go:479-486`). Restated: the id a member of the rest state's `mem` (the server's
  membership is static after boot, `ccApplyOk`: no member is ever removed, so the removed case,
  a warning in Go, is not claimed).

The bucket presence (the rows' `UnsafePut` is fatal on a missing bucket) and the client URLs'
aliasing are in the rest resource and the members' vocabulary (the server's draft,
`etcdserver/ClusterRowsDraft.lean`). Here: the rows (`isClusterD`), the two callers' specs and
proofs (`ClusterVersionSet.specD`, `ClusterMemberAttrSet.specD`: the glue), the request premise
(`rqOkD`) and the rest state's premise of the dispatch (`restReqOk`), with the laws `dispatch`'s
proof needs at its two call sites.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__ClusterVersionSet
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__ClusterMemberAttrSet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__DowngradeInfoSet

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3
  go_etcd_io.etcd.server.v3

namespace apply

/-! ## The premises -/

/-- **Trust boundary (semver and the server's version).** The version `semver.MustParse(s)` is
not above this server's: not greater (`semver.Version.LessThan`, SemVer's order, prerelease below
release) than the major and minor version of `version.Version` with patch `0` (`3.8.0` at the fork
pin: `MustDetectDowngrade(lg, MustParse(version.Version), cv)` compares
`semver.New(sv.Major(), sv.Minor(), 0, "", "")` with `cv` and panics when it is less,
`server/etcdserver/version/downgrade.go:42-54`). Opaque, as `semverValid`: the premise of a
`ClusterVersionSet` request, which only the leader's monitor proposes, of the minimum of the
members' server versions with patch `0` (`version.Monitor.UpdateClusterVersionIfNeeded`), or
`MinClusterVersion` (`3.0.0`) while the cluster has no version and a member does not answer: the
leader's own `version.Version` is among the versions (`getMembersVersions` records the local
member's, the local member being in `c.members`), which bounds the proposal by the proposer's
major.minor. The applying member's bound is the proposer's because every member runs this binary
(the model's deployment: one program, the verified one); a member restarted on an older binary
between the proposal and its apply panics, by design (`MustDetectDowngrade`). The monitor's
downgrade branch (`monitor.go:79-98`, which could propose above the bound: `allowedDowngradeVersion`
wraps `Minor()-1` at minor `0`) is not reached: no `DowngradeInfoSet` is admitted (`rqOk`), and the
boot and snapshot images carry no enabled downgrade record.
Its axiom is `EtcdServer.monitorClusterVersions`'s, through `monitorReq`. -/
opaque semverAtMostServer : GoString → Prop

/-- **The rest state's premise of `dispatch(rq)`** (the cluster-rows stage): a member attributes
request's member is a member of the in-memory members (`UpdateAttributes` panics on an id that is
neither a member nor removed, and the server removes no member). Of the request's model and the
rest state the entry meets: the apply thread's `restModel`, which the server's proof relates to the
committed log's workload facts (`attrLogOk`). -/
def restReqOk (rq : IRRModel) (rs : RestM) : Prop :=
  dispatchKind rq = .clusterMemberAttrSet →
    ∀ a, rq.clusterMemberAttrSet = some a → (rs.mem.lookup a.memberID).isSome = true

/-- Another request kind asks nothing of the rest state. -/
theorem restReqOk_other (rq : IRRModel) (rs : RestM) (h : dispatchKind rq ≠ .clusterMemberAttrSet) :
    restReqOk rq rs := fun hk => absurd hk h

/-- **The per-request premise, restated** (`rqOk`'s text but for its `clusterVersionSet` row: the
version not above the server's, `semverAtMostServer`). -/
def rqOkD (log : mvcc.Log) (rq : IRRModel) : Prop :=
  match dispatchKind rq with
  | .put => putOk log
  | .deleteRange => ∀ o, rq.deleteRange = some o → delOk log o
  | .range => ∀ o, rq.range = some o → rangeOk log o
  | .txn => ∀ t, rq.txn = some t → txn.TxnPre log t
  | .leaseGrant => False
  | .leaseRevoke => False
  | .leaseCheckpoint => False
  | .clusterVersionSet => ∀ v, rq.clusterVersionSet = some v → semverValid v ∧ semverAtMostServer v
  | .downgradeInfoSet => False
  | .alarm => False
  | .authenticate => False
  | .authEnable => False
  | .authDisable => False
  | .authUserAdd => False
  | .authUserDelete => False
  | .authUserChangePassword => False
  | .authUserGrantRole => False
  | .authUserGet => False
  | .authUserRevokeRole => False
  | .authRoleAdd => False
  | .authRoleGrantPermission => False
  | .authRoleGet => False
  | .authRoleRevokePermission => False
  | .authRoleDelete => False
  | .authUserList => False
  | .authRoleList => False
  | _ => True

/-- The restated premise is at least today's (`dispatch`'s other rows unchanged). -/
theorem rqOk_of_rqOkD (log : mvcc.Log) (rq : IRRModel) (h : rqOkD log rq) : rqOk log rq := by
  unfold rqOkD at h; unfold rqOk
  split <;> rename_i hk <;> simp only [hk] at h <;> first | exact h | (intro v hv; exact (h v hv).1)

/-- Today's premise is the restated one off `ClusterVersionSet` (the other producers of
`rqShape`: `InvProposer`, `ReqOn`, `EtcdServer__Compact`, `KVAuthModel`, `ProposeOn`). -/
theorem rqOkD_of_rqOk (log : mvcc.Log) (rq : IRRModel) (h : rqOk log rq)
    (hk : dispatchKind rq ≠ .clusterVersionSet) : rqOkD log rq := by
  unfold rqOk at h; unfold rqOkD
  split <;> rename_i hk' <;> simp only [hk'] at h <;> first | exact h | exact absurd hk' hk

/-- **`dispatch`'s `ClusterVersionSet` call site** (the glue: `uberApplier__dispatch.lean:259`'s
`hsv`, now with the version's bound). -/
theorem rqOkD_ver (log : mvcc.Log) (rq : IRRModel) (x : GoString) (h : rqOkD log rq)
    (hk : dispatchKind rq = .clusterVersionSet) (hx : rq.clusterVersionSet = some x) :
    semverValid x ∧ semverAtMostServer x := by
  unfold rqOkD at h; rw [hk] at h; exact h x hx

/-- **`dispatch`'s `ClusterMemberAttrSet` call site** (the glue). -/
theorem restReqOk_attr (rq : IRRModel) (rs : RestM) (a : MemberAttrModel) (h : restReqOk rq rs)
    (hk : dispatchKind rq = .clusterMemberAttrSet) (ha : rq.clusterMemberAttrSet = some a) :
    (rs.mem.lookup a.memberID).isSome = true := h hk a ha

end apply

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The rows -/

/-- **The `*membership.RaftCluster` `c`, restated** (the cluster-rows stage, 2026-11-02;
`isCluster`'s text but for two rows): `SetVersion`'s `onSet` is `api.UpdateCapability` (until then
any value: Go calls it), with `membership`'s and `api`'s package initialization (it writes
`ClusterVersionMetrics` and `api`'s capability globals; as `RaftCluster.Recover`'s axiom, round 2) and its version not above the server's (`semverAtMostServer`: above it,
`MustDetectDowngrade` panics); `UpdateAttributes`' member a member of `r.mem` (an id neither a
member nor removed panics). The rest state's buckets present and the members' client URLs
read-only are in `RO`'s meaning (`srvRestOwnD`, `memberAtD`, the server's draft), `SetDowngradeInfo`'s
in `RW`'s (`srvRestRWD`). Claimed, and false, as before this stage: a saved value above bbolt's
`MaxValueSize` (a member's attributes, or a version string with a huge prerelease tag, which sorts
below the bound) is fatal in `unsafePut` (`batch_tx.go:183-188`); no caller makes one (the monitor
proposes `Major.Minor.0`, the attributes come from the configuration),
`issues/etcd-backend-put-value-too-large-fatal.md`; a size premise is the user's question. -/
def apply.isClusterD (c : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RO : apply.RestM → IProp GF) (RW : IProp GF) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗
    □ ({{ True }}
        (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty @!!
          go!"Version")) (Val #()))
      {{ (v : Loc), RET #v; True }}) ∗
    □ ({{ True }}
        (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty @!!
          go!"ID")) (Val #()))
      {{ (id : w64), RET #id; True }}) ∗
    □ (∀ (v : Loc) (s : GoString) (b : Bool) (Pre Q Post : IProp GF) (r : apply.RestM),
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
          isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api ∗
          cPre b P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ ⌜v ≠ null⌝ ∗ semverIs v s ∗
          ⌜apply.semverAtMostServer s⌝ ∗ RO r }}
        (App (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty
          @!! go!"SetVersion")) (Val #v))
          (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.UpdateCapability))) (Val #b))
      {{ RET #(); cPost b Pre Post ∗ mvcc.storeRT γ ∗ RO (apply.restSetVersion b s r) }}) ∗
    □ (∀ (id : w64) (attr : etcdserver.api.membership.Attributes) (cus : List GoString) (b : Bool)
        (Pre Q Post : IProp GF) (r : apply.RestM),
      {{ cPre b P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗
          attr.ClientURLs' ↦*□ cus ∗ ⌜(r.mem.lookup id).isSome = true⌝ ∗ RO r }}
        (App (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty
          @!! go!"UpdateAttributes")) (Val #id)) (Val #attr)) (Val #b))
      {{ RET #(); cPost b Pre Post ∗ mvcc.storeRT γ ∗
          RO (apply.restUpdateAttrs b ⟨id, attr.Name', cus⟩ r) }}) ∗
    □ (∀ (d : Loc) (di : etcdserver.version.DowngradeInfo) (b : Bool) (Pre Q Post : IProp GF),
      {{ cPre b P f Pre Q Post ∗ mvcc.storeWT γ ∗ mvcc.storeRT γ ∗ d ↦ di ∗ RW }}
        (App (App (Val (c @!! go.GoType.PointerType etcdserver.api.membership.RaftCluster.ty @!!
          go!"SetDowngradeInfo")) (Val #d)) (Val #b))
      {{ RET #(); cPost b Pre Post ∗ mvcc.storeRT γ ∗ RW }}))

instance apply.isClusterD_persistent (c : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RO : apply.RestM → IProp GF) (RW : IProp GF) : Persistent (apply.isClusterD c γ P f RO RW) := by
  unfold apply.isClusterD; infer_instance

/-- `backendOptsOk` over the restated rows (the switch changes `isCluster` in place; the Draft
copies the two definitions that carry it). -/
def apply.backendOptsOkD (E : apply.AEnv GF) (opts : ApplierOptions) : IProp GF :=
  iprop(⌜opts.Logger' ≠ null⌝ ∗ apply.isApplyKV opts.KV' E.s E.γ ∗ mvcc.hookOk E.γ E.P E.f ∗
    apply.isApplyLessor opts.Lessor' E.s E.γ E.P E.f E.RO E.RW ∗
    apply.isAuthStore opts.AuthStore' E.γ E.P E.f E.RD E.authMode E.RW ∗
    apply.isAlarmStore opts.AlarmStore' E.γ E.P E.f E.RW ∗
    apply.isClusterD opts.Cluster' E.γ E.P E.f E.RO E.RW ∗
    apply.isRaftStatus opts.RaftStatus' ∗ apply.isSnapshotServer opts.SnapshotServer' E.FS ∗
    apply.isConsistentIndexer opts.ConsistentIndex' E.ciC)

instance apply.backendOptsOkD_persistent (E : apply.AEnv GF) (opts : ApplierOptions) :
    Persistent (apply.backendOptsOkD E opts) := by
  unfold apply.backendOptsOkD; infer_instance

def apply.backendIsD (E : apply.AEnv GF) (p : Loc) : IProp GF :=
  iprop(∃ opts : ApplierOptions, structFieldRef applierV3backend go!"options" p ↦□ opts ∗
    apply.backendOptsOkD E opts)

instance apply.backendIsD_persistent (E : apply.AEnv GF) (p : Loc) :
    Persistent (apply.backendIsD E p) := by
  unfold apply.backendIsD; infer_instance

/-- **A cluster method's request facts, restated** (`clusterFacts`, `Chain.lean:1147`, with the
rest state `rs` the applier contract's cluster row already binds): `ClusterVersionSet`'s version not
above the server's, `ClusterMemberAttrSet`'s member a member of `rs.mem` (the restated specs'
premises; `dispatch` takes them from `rqOkD` and `restReqOk`). -/
def apply.clusterFactsD (E : apply.AEnv GF) (m : GoString) (cr : apply.ClusterReq) (r : Loc)
    (rs : apply.RestM) : IProp GF :=
  match cr with
  | .ver v => iprop(⌜m = go!"ClusterVersionSet"⌝ ∗ apply.clusterVersionSetIs r v ∗
      ⌜apply.semverValid v ∧ apply.semverAtMostServer v⌝)
  | .attr a => iprop(⌜m = go!"ClusterMemberAttrSet"⌝ ∗ apply.memberAttrSetIs r a ∗
      ⌜(rs.mem.lookup a.memberID).isSome = true⌝)
  | .dg d => iprop(⌜m = go!"DowngradeInfoSet"⌝ ∗ apply.downgradeInfoSetIs r d ∗ E.RW)

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The callers' specs (restated) -/

/-- **`a.ClusterVersionSet(r, shouldApplyV3)`, restated**: `ClusterVersionSet.spec` with the
version not above the server's (`semverAtMostServer v`, beside `semverValid v`: the restated row's
premise; `dispatch` takes both from `rqOkD`). -/
abbrev apply.applierV3backend.ClusterVersionSet.specD : Prop :=
  ∀ (E : apply.AEnv GF) (p r : Loc) (v3 : Bool) (log : mvcc.Log) (Pre Q Post : IProp GF) (v : GoString)
    (rs : apply.RestM)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIsD E p ∗
      apply.clusterVersionSetIs r v ∗ ⌜apply.semverValid v ∧ apply.semverAtMostServer v⌝ ∗
      apply.mPreV v3 E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post ∗ mvcc.storeWT E.γ ∗
      E.FS ∗ E.RO rs }}
    (App (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"ClusterVersionSet")) (Val #r)) (Val #v3))
  {{ RET #(); apply.mPostV v3 E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Post ∗
      E.FS ∗ E.RO (apply.restSetVersion v3 v rs) }}

/-- **`a.ClusterMemberAttrSet(r, shouldApplyV3)`, restated**: `ClusterMemberAttrSet.spec` with
the request's member a member of the rest state's `mem` (the restated row's premise; `dispatch`
takes it from `restReqOk`). -/
abbrev apply.applierV3backend.ClusterMemberAttrSet.specD : Prop :=
  ∀ (E : apply.AEnv GF) (p r : Loc) (v3 : Bool) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (mm : apply.MemberAttrModel) (rs : apply.RestM)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIsD E p ∗
      apply.memberAttrSetIs r mm ∗ ⌜(rs.mem.lookup mm.memberID).isSome = true⌝ ∗
      apply.mPreV v3 E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post ∗ mvcc.storeWT E.γ ∗
      E.RO rs }}
    (App (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"ClusterMemberAttrSet")) (Val #r)) (Val #v3))
  {{ RET #(); apply.mPostV v3 E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Post ∗
      E.RO (apply.restUpdateAttrs v3 mm rs) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The glue: `ClusterMemberAttrSet` meets the restated row** (today's proof, the member's
premise passed on). -/
theorem apply.applierV3backend.ClusterMemberAttrSet.wp_proofD :
    apply.applierV3backend.ClusterMemberAttrSet.specD (GF := GF) (hG := hG) := by
  intro E p r v3 log Pre Q Post mm rs info
  wp_start as ⟨#Hb, #Hr, %Hmem, Hpre, Hwt, HRO⟩
  iunfold apply.mPreV at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  icases Hard with ⟨Hard, Hwo⟩
  icases mvcc.writerOwn_rt _ $$ Hwo with ⟨Hrt, Hrdb⟩
  iunfold apply.backendIsD at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOkD at Hok
  icases Hok with ⟨-, -, -, -, -, -, #Hc, -⟩
  iunfold apply.isClusterD at Hc
  icases Hc with ⟨%Hcnn, -, -, -, #HUA, -⟩
  iunfold apply.memberAttrSetIs at Hr
  icases Hr with ⟨%Hrnn, %a, %sl, #Hid, #Ha, %Hann, #Hname, #Hurls, #Hsl⟩
  iStructNamed Hopts
  wp_auto
  wp_apply HUA $$ [$Hcs $Hwt $Hrt $HRO] as ⟨HPP, Hrt, HRO⟩
  · iframe Hsl
    ipureintro; exact Hmem
  ihave Hwo := Hrdb $$ Hrt
  ihave Hkv : apply.kvOwn E log $$ [Hrd Hsw Hknown Hard Hwo]
  · iunfold apply.kvOwn; iframe
  iapply HΦ
  iunfold apply.mPostV
  iframe HRO
  iframe

/-- **The glue: `ClusterVersionSet` meets the restated row** (today's proof; the `onSet` the
code passes is the row's `api.UpdateCapability`, and the version's bound passed on). -/
theorem apply.applierV3backend.ClusterVersionSet.wp_proofD
    (hMP : semver.MustParse.spec (GF := GF) (hG := hG))
    (hLT : semver.Version.LessThan.spec (GF := GF) (hG := hG))
    (hVS : semver.Version.String.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.ClusterVersionSet.specD (GF := GF) (hG := hG) := by
  intro E p r v3 log Pre Q Post ver rs info
  wp_start as ⟨#Hb, #Hr, %Hvalid, Hpre, Hwt, HFSt, HRO⟩
  iunfold apply.mPreV at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
  icases Hard with ⟨Hard, Hwo⟩
  icases mvcc.writerOwn_rt _ $$ Hwo with ⟨Hrt, Hrdb⟩
  iunfold apply.backendIsD at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOkD at Hok
  icases Hok with ⟨%Hlg, -, -, -, -, -, #Hc, -, #Hss, -⟩
  iunfold apply.isClusterD at Hc
  icases Hc with ⟨%Hcnn, #HVer, -, #HSV, -⟩
  iunfold apply.isSnapshotServer at Hss
  icases Hss with ⟨%si, %Hsi, #HFS⟩
  iunfold apply.clusterVersionSetIs at Hr
  icases Hr with ⟨%Hrnn, #Hver⟩
  iStructNamed Hopts
  wp_auto
  wp_apply HVer as %prev -
  wp_apply hMP as %rv Hrv
  icases Hrv with (⟨-, %nv, %Hnv, #Hsv⟩ | %Hn)
  rotate_left
  · exact absurd Hvalid.1 Hn.1
  obtain ⟨rfl, Hnv⟩ := Hnv
  wp_auto
  ihave #Hpmb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hpapi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api $$ []
  · iPkgInit
  wp_apply HSV $$ [$Hpmb $Hpapi $Hcs $Hwt $Hrt $Hsv $HRO] as ⟨HPP, Hrt, HRO⟩
  · isplitr
    · ipureintro; exact Hnv
    ipureintro; exact Hvalid.2
  ihave Hwo := Hrdb $$ Hrt
  ihave Hkv : apply.kvOwn E log $$ [Hrd Hsw Hknown Hard Hwo]
  · iunfold apply.kvOwn; iframe
  wp_if_destruct
  · -- no previous version
    iapply HΦ
    iunfold apply.mPostV
    iframe HRO
    iframe
  wp_apply hLT as %b -
  · ipureintro; exact ⟨Hnv, Hif⟩
  have Hprev : prev ≠ null := Hif
  wp_if_destruct
  · -- not a downgrade
    iapply HΦ
    iunfold apply.mPostV
    iframe HRO
    iframe
  -- a downgrade: logged, a snapshot forced
  wp_if_destruct
  · exact absurd Hif Hlg
  wp_apply hVS as %s1 -
  · ipureintro; exact Hprev
  wp_apply hZS as %f1 -
  wp_apply hVS as %s2 -
  · ipureintro; exact Hnv
  wp_apply hZS as %f2 -
  wp_apply wp_slice_literal (l := [f1, f2])
  isplitr
  · ipureintro; rfl
  iintro %fsl -
  wp_auto
  wp_apply hInfo
  · ipureintro; exact Hlg
  rw [Hsi]
  wp_pures
  wp_bind (App (Val #(methods si.ty go!"ForceSnapshot" si.v)) (Val #()))
  iapply HFS $$ HFSt
  inext
  iintro HFSt
  (try wp_auto)
  iapply HΦ
  iunfold apply.mPostV
  iframe HRO
  iframe

/-- **The glue at `newApplierV3Backend`'s cluster row** (`newApplierV3Backend.lean:260-302`, the
applier contract's cluster row over `clusterFactsD`, from the restated specs). The draft takes
`backendIs` beside `backendIsD` for `DowngradeInfoSet`'s unchanged spec; at the switch they are
one. -/
theorem apply.clusterRow_backendD
    (hClusterVersionSet : apply.applierV3backend.ClusterVersionSet.specD (GF := GF) (hG := hG))
    (hClusterMemberAttrSet : apply.applierV3backend.ClusterMemberAttrSet.specD (GF := GF) (hG := hG))
    (hDowngradeInfoSet : apply.applierV3backend.DowngradeInfoSet.spec (GF := GF) (hG := hG))
    (E : apply.AEnv GF) (p : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.backendIs E p ∗ apply.backendIsD E p ⊢
    □ (∀ (m : GoString) (r : Loc) (v3 : Bool) (log : mvcc.Log) (Pre Q Post : IProp GF)
        (cr : apply.ClusterReq) (rs : apply.RestM) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
      ⌜m ∈ apply.clusterMethods⌝ -∗
      {{ apply.clusterFactsD E m cr r rs ∗
          apply.mPreV v3 E .backend (.ok ⟨go.GoType.PointerType applierV3backend.ty, #p⟩) info log
            Pre Q Post ∗ mvcc.storeWT E.γ ∗ E.FS ∗ E.RO rs }}
        (App (App (Val #(methods (go.GoType.PointerType applierV3backend.ty) m #p)) (Val #r))
          (Val #v3))
      {{ RET #(); apply.mPostV v3 E .backend (.ok ⟨go.GoType.PointerType applierV3backend.ty, #p⟩)
          info log Pre Post ∗ E.FS ∗ E.RO (cr.eff v3 rs) }}) := by
  iintro ⟨#Hinit, #Hbk, #HbkD⟩
  imodintro
  iintro %m %r %v3 %log %Pre %Q %Post %cr %rs %info %hm
  imodintro
  iintro %Φ' Hpre HΦ'
  icases Hpre with ⟨HR, Hm, Hwt, HFS, HRO⟩
  cases cr with
  | ver v =>
    iunfold apply.clusterFactsD at HR
    icases HR with ⟨%Hmv, #HR, %Hsv⟩
    subst Hmv
    iapply (hClusterVersionSet E p r v3 log Pre Q Post v rs info) $$ [Hm Hwt HFS HRO] [HΦ']
    · iframe
      iframe #
      ipureintro; exact Hsv
    inext
    iintro ⟨H1, H2, H3⟩
    iapply HΦ'
    iframe
  | attr a =>
    iunfold apply.clusterFactsD at HR
    icases HR with ⟨%Hmv, #HR, %Hmem⟩
    subst Hmv
    iapply (hClusterMemberAttrSet E p r v3 log Pre Q Post a rs info) $$ [Hm Hwt HRO] [HΦ' HFS]
    · iframe
      iframe #
      ipureintro; exact Hmem
    inext
    iintro ⟨Hpost, HRO⟩
    iapply HΦ'
    iframe
  | dg d =>
    iunfold apply.clusterFactsD at HR
    icases HR with ⟨%Hmv, #HR, HRW⟩
    subst Hmv
    iapply (hDowngradeInfoSet E p r v3 log Pre Q Post info) $$ [Hm Hwt HRW] [HΦ' HFS HRO]
    · iframe
      iframe #
    inext
    iintro Hpost
    iapply HΦ'
    iframe

end proof

end EtcdGrove
end Perennial
