/-
**The cluster contract's rows, restated: the server's side (Draft)** (the cluster-rows stage,
2026-11-02; `notes/cluster-rows-plan.md`). Imported by nothing; no `axiom`, no `sorry`; nothing
switched. Each `…D` drafts the unsuffixed statement it names, to replace it in place at the
switch; a new name is the name it will have. Built on the backend-auth-split stage's approved
restatement of `srvRestOwn` (§16), applied on `lean` at `a43af91055` and merged here:
`srvRestOwnD` is the applied `srvRestOwn` (`InvRest.lean:434-437`) over `clusterMemD`, with this
stage's conjunct.

The rows (`apply.isClusterD`, `apply/ClusterRowsDraft.lean`) need, besides their premises:

* **the rest buckets present** (every bucket of `restBootBk`; Go's `UnsafePut` on a missing
  bucket is fatal): `srvRestOwnD` and `srvRestRWD` hold `restPresent`, which every
  rest state of the model has (`restPresent_restModel`, from `restModel_present`) and the rows
  and `applyConfChange` keep (`restPresent_restSetVersion`, `_restUpdateAttrs`, `_ccRest`);
* **the members' client URLs read-only** (`UpdateAttributes` stores the request's slice in the
  member, `m.Attributes = attr`: the member's `ClientURLs` is the request's array, which the proof
  holds read-only, `↦*□`, and which no Go code writes): `membership.memberAtD`, `memberAt` with
  `cu ↦*□ mm.clientURLs` in place of the owned fraction, and the definitions carrying it
  (`memAtD`, `clusterMemD`); its laws (`memberAtD_split`, `memberAtD_agree`) and the way from
  today's (`memberAt_persistD`: an owned member's client URLs made read-only, an update).

The new premises' sources (the glue):

* the version's bound (`semverAtMostServer`) is a request premise (`apply.rqOkD`), from the
  monitors' requests (`monitorReqD`): `EtcdServer.monitorClusterVersions`'s axiom, whose text is
  unchanged, now claims it proposes only versions not above the server's;
* the attributes' member a member of the rest state (`apply.restReqOk`): the committed log's
  attribute requests name members of raft's configuration (`attrLogOk`, a new conjunct of the KV
  invariant's workload facts, `kvWorkD`), from the proposal's permission (`reqPropOkMD`: the
  request path's permissions name no attribute request, `reqPropOkMD_of_kind`; the monitors' names
  the server's own id, `monitorReqD`, which is a voter, `srvMonitorPermitMD_of`; `publishV3`'s
  axiom, its text unchanged, now claims it proposes only the server's own id, `s.MemberID()`);
  and every voter is a member of the rest state at every applied log (`srvMemOkD`, the apply
  thread's `srvMemOk` with its converse: the boot members are the voters, `memBoot_cover`, and
  the server's conf changes only add, `ccApplyOk`). `restReqOk_of_attr` puts them together at
  `EtcdServer.apply`'s call of `apply.Apply`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ClusterRowsDraft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestMemId
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MonitorsOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-! ## The rest buckets present -/

section pure
variable [GooseExts]

end pure

/-! ## The voters are members of every rest state -/

section pure2
variable [GooseExts]

end pure2

/-! ## The attribute requests' members -/

section pure3
variable [GooseExts]

/-- **The glue at `EtcdServer.apply`'s call of `apply.Apply`** (its `applyEntryNormal`): the next
entry's request, of a committed log whose attribute requests name voters, meets the rest state's
premise at the applied log `A`, whose members include the voters. -/
theorem restReqOk_of_attr (γs : ServerRaftNames) (c0 : w64) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (hmo : srvMemOk γs c0 A) (ha : attrEntryOk γs.raft.cfg m)
    (ht : m.typ = W32 0) (hne : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq) :
    apply.restReqOk rq (restModel c0 γs.raft.boot (γs.pre ++ A)) := by
  intro hk a ha'
  exact hmo.2.2 _ ((ha ht hne rq hdec hk).2 a ha')

end pure3

/-! ## The monitors' requests -/

section pure4
variable [GooseExts]

/-- **`rqShape` under the restated premise** (`rqShape`'s text read under `rqOkD`). -/
def rqShapeD (rq : apply.IRRModel) : Prop :=
  (∀ on, apply.dispatchOk on rq) ∧ ∀ log, rqSmall log rq → apply.rqOkD log rq

/-- A monitor's request has the restated shape (`rqShape_of_monitorReq`'s). -/
theorem rqShapeD_of_monitorReqD (lid : w64) (rq : apply.IRRModel) (h : monitorReq lid rq) :
    rqShapeD rq := by
  have hs := rqShape_of_monitorReq lid rq h
  refine ⟨hs.1, fun log hl => ?_⟩
  have h0 := hs.2 log hl
  obtain ⟨-, -, -, hk⟩ := h.1
  unfold apply.rqOkD
  rcases hk with hk | ⟨hk, hv⟩
  · rw [hk]; trivial
  · rw [hk]; exact fun v hv' => ⟨hv v hv', h.2.2 v hv'⟩

end pure4

/-! ## The resources -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The member `m` at the fraction `q`, with the value `mm`, restated**: `memberAt` with its
client URLs' elements read-only (`cu ↦*□`, until then at `q`). `UpdateAttributes` stores the
attributes' slice in the member (`m.Attributes = attr`, `cluster.go:472`), so after it the
member's `ClientURLs` is the request's array, which the proof holds read-only; no Go code writes a
member's client URLs' elements (`Clone` copies them, the writers replace the slice). Both halves
carry it: `clusterMem`'s and the cluster lock's (`rcLockInv`, through `memAt`). -/
def membership.memberAtD (m : Loc) (q : Qp) (mm : apply.MemberM) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ (pu cu : GoSlice),
    membership.mIDAddr m ↦{DFrac.own q} mm.id ∗ membership.mPeerURLsAddr m ↦{DFrac.own q} pu ∗
    membership.mIsLearnerAddr m ↦{DFrac.own q} mm.isLearner ∗
    membership.mNameAddr m ↦{DFrac.own q} mm.name ∗
    membership.mClientURLsAddr m ↦{DFrac.own q} cu ∗ pu ↦*{DFrac.own q} mm.peerURLs ∗
    cu ↦*□ mm.clientURLs)

/-- The members map at `q` over `memberAtD` (`memAt`'s text). -/
def membership.memAtD (c : Loc) (q : Qp) (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM) :
    IProp GF :=
  iprop(∃ mp : Loc, membership.rcMembersAddr c ↦{DFrac.own q} mp ∗ mp ↦${DFrac.own q} ms ∗
    ⌜membership.memDom ms mem⌝ ∗
    [∗map] k ↦ m ∈ ms, membership.memberAtD m q ((mem !! k).getD default))

/-- The apply thread's half (`clusterMem`'s text). -/
def membership.clusterMemD (c : Loc) (mem : GMap w64 apply.MemberM) : IProp GF :=
  iprop(∃ ms : GMap w64 Loc, membership.memAtD c (1 : Qp).half ms mem)

/-- **The server's `AEnv.RO`, restated**: the backend-auth-split stage's `srvRestOwn` (§16: the
cluster's buckets idle, the others a part, the members each under its own id) over `clusterMemD`,
and **the rest buckets present** (`restPresent`: the rows' `UnsafePut`s, fatal on a
missing bucket). -/
def srvRestOwnD (γB : backend.BNames) (c : Loc) (r : apply.RestM) : IProp GF :=
  iprop(backend.rbOwnIn γB membership.clusterBkts r.bk ∗
    backend.rbPart γB (fun n => ¬ membership.clusterBkts n) r.bk ∗ membership.clusterMemD c r.mem ∗
    ⌜memIdOk r.mem ∧ restPresent r.bk⌝)

/-- **The server's `AEnv.RW`, restated**: the writer's half at some buckets, **the rest buckets
present** (`SetDowngradeInfo`'s `MustSaveDowngradeToBackend` puts in `cluster`, the alarm store's
`MustPutAlarm` in `alarm`, the auth store's writers in theirs, each fatal on a missing bucket;
review rounds 1-2). Until then `∃ r, rbOwn γB r`. -/
def srvRestRWD (γB : backend.BNames) : IProp GF :=
  iprop(∃ bk, backend.rbOwn γB bk ∗ ⌜restPresent bk⌝)

/-- **The cluster's apply contract, restated** (`clusterApplyOk`'s text over `isClusterD`,
`srvRestOwnD` and `srvRestRWD`). -/
def clusterApplyOkD (c : Loc) : IProp GF :=
  iprop(□ ∀ (d : mvcc.KBReal) (W Pk : IProp GF) (γ' : mvcc.StoreNames) (f : GoFunc)
      (RO : apply.RestM → IProp GF) (RW : IProp GF),
    ⌜γ'.kb = some d⌝ -∗ backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗
    ⌜f ≠ func.nil⌝ -∗ (∃ n : Loc, membership.rcVersionChangedAddr c ↦□ n) -∗
    roLens RO (fun r => iprop(srvRestOwnD d.γB c r ∗ clusterBeOn c d.be)) -∗
    rwLens RW iprop(srvRestRWD d.γB ∗ clusterBeOn c d.be) -∗
    apply.isClusterD c γ' Pk #f RO RW)

instance clusterApplyOkD_persistent (c : Loc) : Persistent (clusterApplyOkD (GF := GF) c) := by
  unfold clusterApplyOkD; infer_instance

end defs

/-! ## The laws -/

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- A member at `q1 + q2` is two parts (`memberAt_split`'s). -/
theorem membership.memberAtD_split (m : Loc) (q1 q2 : Qp) (mm : apply.MemberM) :
    membership.memberAtD (GF := GF) m (q1 + q2) mm ⊣⊢
      membership.memberAtD m q1 mm ∗ membership.memberAtD m q2 mm := by
  unfold membership.memberAtD
  have hpt := fun {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) =>
    typedPointsto_frac_add (GF := GF) l v q1 q2
  have hsl := fun {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (sl : GoSlice) (vs : List V) =>
    (ownSlice_fractional (GF := GF) sl vs).fractional q1 q2
  refine ⟨?_, ?_⟩
  · iintro ⟨%Hnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, #Hcus⟩
    icases (hpt _ _).1 $$ Hid with ⟨Hid1, Hid2⟩
    icases (hpt _ _).1 $$ Hpu with ⟨Hpu1, Hpu2⟩
    icases (hpt _ _).1 $$ Hil with ⟨Hil1, Hil2⟩
    icases (hpt _ _).1 $$ Hnm with ⟨Hnm1, Hnm2⟩
    icases (hpt _ _).1 $$ Hcu with ⟨Hcu1, Hcu2⟩
    icases (hsl _ _).1 $$ Hpus with ⟨Hpus1, Hpus2⟩
    isplitl [Hid1 Hpu1 Hil1 Hnm1 Hcu1 Hpus1]
    · isplitr; (ipureintro; exact Hnn)
      iexists pu, cu; iframe; iframe Hcus
    · isplitr; (ipureintro; exact Hnn)
      iexists pu, cu; iframe; iframe Hcus
  · iintro ⟨⟨%Hnn, %pu, %cu, Hid1, Hpu1, Hil1, Hnm1, Hcu1, Hpus1, #Hcus1⟩,
      ⟨-, %pu', %cu', Hid2, Hpu2, Hil2, Hnm2, Hcu2, Hpus2, -⟩⟩
    ihave %Hpu := typedPointsto_agree_wand _ _ _ _ _ $$ Hpu1 Hpu2
    ihave %Hcu := typedPointsto_agree_wand _ _ _ _ _ $$ Hcu1 Hcu2
    subst Hpu Hcu
    isplitr; (ipureintro; exact Hnn)
    iexists pu, cu
    isplitl [Hid1 Hid2]; (iapply (hpt _ _).2; iframe)
    isplitl [Hpu1 Hpu2]; (iapply (hpt _ _).2; iframe)
    isplitl [Hil1 Hil2]; (iapply (hpt _ _).2; iframe)
    isplitl [Hnm1 Hnm2]; (iapply (hpt _ _).2; iframe)
    isplitl [Hcu1 Hcu2]; (iapply (hpt _ _).2; iframe)
    isplitl [Hpus1 Hpus2]; (iapply (hsl _ _).2; iframe)
    iframe Hcus1

/-- Two parts agree on the member's value (`memberAt_agree`'s). -/
theorem membership.memberAtD_agree (m : Loc) (q1 q2 : Qp) (mm1 mm2 : apply.MemberM) :
    membership.memberAtD (GF := GF) m q1 mm1 ∗ membership.memberAtD m q2 mm2 ⊢ ⌜mm1 = mm2⌝ := by
  unfold membership.memberAtD
  iintro ⟨⟨-, %pu, %cu, Hid1, Hpu1, Hil1, Hnm1, Hcu1, Hpus1, Hcus1⟩,
    ⟨-, %pu', %cu', Hid2, Hpu2, Hil2, Hnm2, Hcu2, Hpus2, Hcus2⟩⟩
  ihave %Hpu := typedPointsto_agree_wand _ _ _ _ _ $$ Hpu1 Hpu2
  ihave %Hcu := typedPointsto_agree_wand _ _ _ _ _ $$ Hcu1 Hcu2
  subst Hpu Hcu
  ihave %Hid := typedPointsto_agree_wand _ _ _ _ _ $$ Hid1 Hid2
  ihave %Hil := typedPointsto_agree_wand _ _ _ _ _ $$ Hil1 Hil2
  ihave %Hnm := typedPointsto_agree_wand _ _ _ _ _ $$ Hnm1 Hnm2
  ihave %Hpus := ownSlice_agree _ _ _ _ _ $$ Hpus1 Hpus2
  ihave %Hcus := ownSlice_agree _ _ _ _ _ $$ Hcus1 Hcus2
  ipureintro
  cases mm1; cases mm2
  simp_all

end lemmas

end EtcdGrove
end Perennial
