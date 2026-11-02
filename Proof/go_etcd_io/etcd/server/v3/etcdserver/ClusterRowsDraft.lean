/-
**The cluster contract's rows, restated: the server's side (Draft)** (the cluster-rows stage,
2026-11-02; `notes/cluster-rows-plan.md`). Imported by nothing; no `axiom`, no `sorry`; nothing
switched. Each `…D` drafts the unsuffixed statement it names, to replace it in place at the
switch; a new name is the name it will have. Built on the backend-auth-split stage's approved
restatement of `srvRestOwn` (`bks-trusted.md` §16), which this branch's base has not applied yet:
`srvRestOwnD` is §16's text with this stage's conjunct.

The rows (`apply.isClusterD`, `apply/ClusterRowsDraft.lean`) need, besides their premises:

* **the cluster's buckets present** (`members`, `members_removed`, `cluster`; Go's `UnsafePut`
  on a missing bucket is fatal): `srvRestOwnD` holds `membership.clusterPresent r.bk`, which every
  rest state of the model has (`clusterPresent_restModel`, from `restModel_present`) and the rows
  and `applyConfChange` keep (`clusterPresent_restSetVersion`, `_restUpdateAttrs`, `_ccRest`);
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

/-! ## The cluster's buckets present -/

section pure
variable [GooseExts]

/-- **The cluster's buckets are present in `bk`** (`members`, `members_removed`, `cluster`:
`SetBackend`'s `MustCreateBackendBuckets` makes them; the rows' and `applyConfChange`'s writers
`UnsafePut`/`UnsafeDelete` in them, fatal on a missing bucket). -/
def membership.clusterPresent (bk : GMap GoString backend.BktData) : Prop :=
  ∀ n, membership.clusterBkts n → (bk.lookup n).isSome = true

theorem clusterPresent_restBoot (bootLog : List EntryM) :
    membership.clusterPresent (restBoot bootLog).bk := by
  intro n hn
  rcases hn with (rfl | rfl) | rfl <;> simp [restBoot, restBootBk]

/-- **Every rest state of the model has them** (`restModel_present`). -/
theorem clusterPresent_restModel (c0 : w64) (bootLog : List EntryM) (L : List EntryModel) :
    membership.clusterPresent (restModel c0 bootLog L).bk :=
  fun n hn => restModel_present c0 bootLog L n (clusterPresent_restBoot bootLog n hn)

theorem clusterPresent_putIn (r : apply.RestM) (n k v : GoString)
    (h : membership.clusterPresent r.bk) : membership.clusterPresent (r.putIn n k v).bk :=
  fun n' hn => putIn_present r n k v n' (h n' hn)

theorem clusterPresent_delIn (r : apply.RestM) (n k : GoString)
    (h : membership.clusterPresent r.bk) : membership.clusterPresent (r.delIn n k).bk :=
  fun n' hn => delIn_present r n k n' (h n' hn)

/-- **Buckets agreeing on the cluster's keep them** (the lessor's revocation lens, §16: it gives
back `srvRestOwn` at buckets agreeing with `rs.bk` off `lease`, not a cluster bucket). -/
theorem clusterPresent_congr (bk bk' : GMap GoString backend.BktData)
    (h : ∀ n, membership.clusterBkts n → bk.lookup n = bk'.lookup n)
    (hp : membership.clusterPresent bk) : membership.clusterPresent bk' :=
  fun n hn => by rw [← h n hn]; exact hp n hn

/-- `SetVersion`'s row keeps them. -/
theorem clusterPresent_restSetVersion (b : Bool) (s : GoString) (r : apply.RestM)
    (h : membership.clusterPresent r.bk) :
    membership.clusterPresent (apply.restSetVersion b s r).bk := by
  unfold apply.restSetVersion; split
  · exact clusterPresent_putIn _ _ _ _ h
  · exact h

/-- `UpdateAttributes`' row keeps them. -/
theorem clusterPresent_restUpdateAttrs (b : Bool) (a : apply.MemberAttrModel) (r : apply.RestM)
    (h : membership.clusterPresent r.bk) :
    membership.clusterPresent (apply.restUpdateAttrs b a r).bk := by
  unfold apply.restUpdateAttrs; split
  · exact h
  · split
    · exact clusterPresent_putIn _ _ _ _ h
    · exact h

/-- `applyConfChange` keeps them. -/
theorem clusterPresent_ccRest (v3 : Bool) (cm : ConfChangeM) (r : apply.RestM)
    (h : membership.clusterPresent r.bk) : membership.clusterPresent (ccRest v3 cm r).bk := by
  unfold ccRest; split
  · split
    · exact clusterPresent_putIn _ _ _ _ h
    · split
      · exact clusterPresent_putIn _ _ _ _ (clusterPresent_delIn _ _ _ h)
      · exact h
  · exact h

end pure

/-! ## The voters are members of every rest state -/

section pure2
variable [GooseExts]

/-- **The boot members include every boot entry's node** (`memBoot_keys`' converse). -/
theorem memBoot_cover (bootLog : List EntryM) (e : EntryM) (he : e ∈ bootLog) (cc : ConfChangeM)
    (hd : ccDecodeV1 e.Data' = some cc) : ((memBoot bootLog) !! cc.nodeId).isSome = true := by
  unfold memBoot
  -- the fold only adds keys
  have mono : ∀ (l : List EntryM) (acc : GMap w64 apply.MemberM) (k : w64),
      (acc !! k).isSome = true →
      ((l.foldl (fun mem e => match ccDecodeV1 e.Data' with
        | some cc => mem.insert cc.nodeId (membership.ccMemberAt cc)
        | none => mem) acc) !! k).isSome = true := by
    intro l
    induction l with
    | nil => intro acc k h; exact h
    | cons e l ih =>
      intro acc k h
      rw [List.foldl_cons]
      apply ih
      cases hd' : ccDecodeV1 e.Data' with
      | none => exact h
      | some cc' =>
        simp only
        by_cases hk : cc'.nodeId = k
        · subst hk; rw [GMap.lookup_insert]; rfl
        · rw [GMap.lookup_insert_ne _ _ hk]; exact h
  suffices H : ∀ (l : List EntryM) (acc : GMap w64 apply.MemberM), e ∈ l →
      ((l.foldl (fun mem e => match ccDecodeV1 e.Data' with
        | some cc => mem.insert cc.nodeId (membership.ccMemberAt cc)
        | none => mem) acc) !! cc.nodeId).isSome = true from H bootLog ∅ he
  intro l
  induction l with
  | nil => intro acc h; cases h
  | cons e' l ih =>
    intro acc h
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · apply mono
      rw [hd]; simp only; rw [GMap.lookup_insert]; rfl
    · exact ih _ h

/-- **The voters are members of the rest state** at the applied log `A` (`srvMemOk`'s converse). -/
def srvMemCover (γs : ServerRaftNames) (c0 : w64) (A : List EntryModel) : Prop :=
  ∀ k, k ∈ γs.raft.cfg → ((restModel c0 γs.raft.boot (γs.pre ++ A)).mem !! k).isSome = true

/-- **`srvMemOk`, restated**: the in-memory members are exactly the voters (until then only
among them): what makes an attribute request of a voter's id a member's (`restReqOk_of_attr`). -/
def srvMemOkD (γs : ServerRaftNames) (c0 : w64) (A : List EntryModel) : Prop :=
  srvMemOk γs c0 A ∧ srvMemCover γs c0 A

/-- At the start of a new cluster (`srvMemOk_boot`'s premises). -/
theorem srvMemOkD_boot (γs : ServerRaftNames) (c0 : w64)
    (ps : List w64) (hpre : γs.pre = []) (hcfg : γs.raft.cfg = GMap.listToSet ps)
    (hnd : ps.Nodup) (hlen : (ps.length : Int) < 2 ^ 61) (hb : srvBootLogOk ps γs.raft.boot) :
    srvMemOkD γs c0 [] := by
  refine ⟨srvMemOk_boot γs c0 ps hpre hcfg hnd hlen hb, ?_⟩
  intro k hk
  rw [hpre, List.append_nil, restModel_nil]
  show ((memBoot γs.raft.boot) !! k).isSome = true
  rw [hcfg, GMap.elem_of_list_to_set] at hk
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hk
  have hlt : i < γs.raft.boot.length := by
    rw [hb.1]; exact (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨e, he⟩ : ∃ e, γs.raft.boot[i]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨-, -, -, ⟨m, hdm, -, hpk⟩⟩ := hb.2.2 i e he
  rw [hi] at hpk
  cases hpk
  exact memBoot_cover _ e (List.mem_of_getElem? he) m hdm

/-- A normal entry keeps it (`srvApRes_normal`'s step). -/
theorem srvMemCover_normal (γs : ServerRaftNames) (c0 : w64) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ = W32 0) (h : srvMemCover γs c0 A) : srvMemCover γs c0 (A ++ [m]) := by
  intro k hk
  rw [← List.append_assoc, restModel_append, restEntry_normal_memKeys _ _ _ ht]
  exact h k hk

/-- **A conf change of the server's policy keeps the members** (an `AddNode`: `ccRest` inserts or
leaves; no `RemoveNode`, `ccApplyOk`). -/
theorem ccRest_memKeys_mono (v3 : Bool) (cm : ConfChangeM) (r : apply.RestM) (ht : cm.type = W32 0)
    (k : w64) (h : (r.mem !! k).isSome = true) : ((ccRest v3 cm r).mem !! k).isSome = true := by
  unfold ccRest
  by_cases hc : v3 = true ∧ membership.ccValidOn r.bk cm = true
  · rw [if_pos hc, if_pos ht, apply.RestM.putIn_mem]
    simp only
    by_cases hkk : cm.nodeId = k
    · subst hkk; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ hkk]; exact h
  · rw [if_neg hc]; exact h

/-- Across committed entries `B` of the server's policy (`ccLogOk`; `srvMemOk_append`'s). -/
theorem srvMemCover_append (γs : ServerRaftNames) (c0 : w64) (A B : List EntryModel)
    (h : srvMemCover γs c0 A) (hB : ccLogOk γs.raft B) : srvMemCover γs c0 (A ++ B) := by
  induction B generalizing A with
  | nil => simpa using h
  | cons m B ih =>
    have h1 : srvMemCover γs c0 (A ++ [m]) := by
      intro k hk
      have e : γs.pre ++ (A ++ [m]) = (γs.pre ++ A) ++ [m] := by simp
      rw [e, restModel_append]
      by_cases ht : m.typ = W32 0
      · rw [restEntry_normal_memKeys _ _ _ ht]; exact h k hk
      · cases hdec : ccDecodeV1 m.data with
        | none =>
          unfold restEntry
          rw [if_neg ht, hdec]
          exact h k hk
        | some cc =>
          rw [restEntry_cc _ _ cc _ ht hdec]
          exact ccRest_memKeys_mono _ cc _ (hB m (by simp) ht cc hdec).1 k (h k hk)
    have := ih (A ++ [m]) h1 (fun e he => hB e (List.mem_cons_of_mem _ he))
    simpa using this

end pure2

/-! ## The attribute requests' members -/

section pure3
variable [GooseExts]

/-- **An attribute request names a member of `S`** (the cluster-rows stage): a request `dispatch`
sends to `ClusterMemberAttrSet` has its member in `S` (raft's configuration, the server's static
membership), and it has no range end `[0]` (`irrNoZeroEnd`: the wire then decodes the request
itself, `attrIdOk_wire`; a cluster kind wins `dispatchKind` over a range's). Any other request:
nothing. -/
def attrIdOk (S : GSet w64) (rq : apply.IRRModel) : Prop :=
  apply.dispatchKind rq = .clusterMemberAttrSet →
    irrNoZeroEnd rq ∧ ∀ a, rq.clusterMemberAttrSet = some a → a.memberID ∈ S

/-- **The permission's fact carries to the request the wire decodes** (`reqPropOk_wire`'s). -/
theorem attrIdOk_wire (S : GSet w64) (rq rq' : apply.IRRModel) (hm : apply.HeaderModel)
    (hw : irrWireOf (apply.withHeader rq hm) rq') (h : attrIdOk S rq) : attrIdOk S rq' := by
  intro hk'
  have hk : apply.dispatchKind rq = .clusterMemberAttrSet := by
    have := hw.2.2.1; rw [hk'] at this; exact this.symm
  obtain ⟨hz, ha⟩ := h hk
  have he : rq' = apply.withHeader rq hm := hw.2.2.2 hz
  subst he
  exact ⟨hz, ha⟩

theorem attrIdOk_of_kind (S : GSet w64) (rq : apply.IRRModel)
    (h : apply.dispatchKind rq ≠ .clusterMemberAttrSet) : attrIdOk S rq := fun hk => absurd hk h

/-- A committed entry's: its request's (a normal entry that decodes). -/
def attrEntryOk (S : GSet w64) (m : EntryModel) : Prop :=
  m.typ = W32 0 → ∀ rq, apply.irrDecode m.data = some rq → attrIdOk S rq

/-- **The committed log's attribute requests name members of `S`** (a new conjunct of the KV
invariant's workload facts, `kvWorkD`). -/
def attrLogOk (S : GSet w64) (L : List EntryModel) : Prop := ∀ m ∈ L, attrEntryOk S m

theorem attrLogOk_append (S : GSet w64) (A B : List EntryModel) :
    attrLogOk S (A ++ B) ↔ attrLogOk S A ∧ attrLogOk S B := by
  unfold attrLogOk; simp only [List.mem_append]
  exact ⟨fun h => ⟨fun m hm => h m (Or.inl hm), fun m hm => h m (Or.inr hm)⟩,
    fun h m hm => hm.elim (h.1 m) (h.2 m)⟩

/-- The entry a proposal of `d` commits, from its permission's `attrIdOk` (`kv_prop_auW`'s step). -/
theorem attrEntryOk_of (S : GSet w64) (e : EntryModel) (d : List w8) (rq : apply.IRRModel)
    (hed : e.data = d) (hdec : apply.irrDecode d = some rq) (h : attrIdOk S rq) :
    attrEntryOk S e := by
  intro _ rq' h'
  rw [hed, hdec] at h'
  cases h'
  exact h

/-- A conf entry asks nothing (`kvWork_snoc`'s conf case). -/
theorem attrEntryOk_conf (S : GSet w64) (e : EntryModel) (ht : e.typ ≠ W32 0) : attrEntryOk S e :=
  fun h => absurd h ht

/-- **The glue at `EtcdServer.apply`'s call of `apply.Apply`** (its `applyEntryNormal`): the next
entry's request, of a committed log whose attribute requests name voters, meets the rest state's
premise at the applied log `A`, whose members include the voters. -/
theorem restReqOk_of_attr (γs : ServerRaftNames) (c0 : w64) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (hmo : srvMemOkD γs c0 A) (ha : attrEntryOk γs.raft.cfg m)
    (ht : m.typ = W32 0) (hdec : apply.irrDecode m.data = some rq) :
    apply.restReqOk rq (restModel c0 γs.raft.boot (γs.pre ++ A)) := by
  intro hk a ha'
  exact hmo.2 _ ((ha ht rq hdec hk).2 a ha')

end pure3

/-! ## The monitors' requests -/

section pure4
variable [GooseExts]

/-- **The requests the monitors propose, restated** (`monitorReq` with this stage's two facts):
an attribute request's member is the server's own `lid` (`publishV3`: `Member_ID:
uint64(s.MemberID())`), a version not above the server's (`monitorClusterVersions`: the members'
minimum, the local member's among them, with patch `0`; `semverAtMostServer`). -/
def monitorReqD (lid : w64) (rq : apply.IRRModel) : Prop :=
  monitorReq rq ∧ (∀ a, rq.clusterMemberAttrSet = some a → a.memberID = lid) ∧
    ∀ v, rq.clusterVersionSet = some v → apply.semverAtMostServer v

theorem monitorReqD_monitorReq (lid : w64) (rq : apply.IRRModel) (h : monitorReqD lid rq) :
    monitorReq rq := h.1

/-- A monitor's request names the server's own id, a voter. -/
theorem attrIdOk_of_monitorReqD (S : GSet w64) (lid : w64) (rq : apply.IRRModel)
    (h : monitorReqD lid rq) (hl : lid ∈ S) : attrIdOk S rq := by
  intro _
  exact ⟨h.1.1, fun a ha => by rw [h.2.1 a ha]; exact hl⟩

/-- **`rqShape` under the restated premise** (`rqShape`'s text read under `rqOkD`). -/
def rqShapeD (rq : apply.IRRModel) : Prop :=
  (∀ on, apply.dispatchOk on rq) ∧ ∀ log, rqSmall log rq → apply.rqOkD log rq

/-- A monitor's request has the restated shape (`rqShape_of_monitorReq`'s). -/
theorem rqShapeD_of_monitorReqD (lid : w64) (rq : apply.IRRModel) (h : monitorReqD lid rq) :
    rqShapeD rq := by
  have hs := rqShape_of_monitorReq rq h.1
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
and **the cluster's buckets present** (`clusterPresent`: the rows' `UnsafePut`s, fatal on a
missing bucket). -/
def srvRestOwnD (γB : backend.BNames) (c : Loc) (r : apply.RestM) : IProp GF :=
  iprop(backend.rbOwnIn γB membership.clusterBkts r.bk ∗
    backend.rbPart γB (fun n => ¬ membership.clusterBkts n) r.bk ∗ membership.clusterMemD c r.mem ∗
    ⌜memIdOk r.mem ∧ membership.clusterPresent r.bk⌝)

/-- **The server's `AEnv.RW`, restated**: the writer's half at some buckets, **the cluster's
present** (`SetDowngradeInfo`'s `MustSaveDowngradeToBackend` puts in `cluster`, fatal on a missing
bucket; review round 1). Until then `∃ r, rbOwn γB r`. -/
def srvRestRWD (γB : backend.BNames) : IProp GF :=
  iprop(∃ bk, backend.rbOwn γB bk ∗ ⌜membership.clusterPresent bk⌝)

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

/-- **The workload facts, restated** (`kvWork` and the attribute requests' members, `attrLogOk`). -/
def kvWorkD (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) : IProp GF :=
  iprop(kvWork cfg γk L ∗ ⌜attrLogOk cfg.cfg L⌝)

/-- **The proposal's permission, restated** (`reqPropOkM` and `attrIdOk` at raft's
configuration). -/
def reqPropOkMD (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (rq : apply.IRRModel) (Qh : apply.HeaderModel → List EntryModel → IProp GF) : IProp GF :=
  iprop(reqPropOkM on γ γk Gb rq Qh ∗ ⌜attrIdOk γ.raft.cfg rq⌝)

/-- **The monitors' permission, restated**: the server's own id `lid` (its `memberID` field,
read-only), a voter, and the permission for the monitors' requests naming it (`monitorReqD`). -/
def srvMonitorPermitMD (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(isServerReqM on s E ρ ∗ ∃ lid : w64, srvMemberIDAddr s ↦□ lid ∗ ⌜lid ∈ ρ.raft.raft.cfg⌝ ∗
    □ ∀ (rq : apply.IRRModel) (Gb : apply.HeaderModel → IProp GF), ⌜monitorReqD lid rq⌝ -∗
      reqPropOkMD on ρ.raft ρ.kv Gb rq (fun _ _ => iprop(True)))

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

/-- **A member's client URLs made read-only** (an update): how today's producers of `memberAt`
(`AddMember`'s caller, from the context's unmarshalled member) give `memberAtD`. -/
theorem membership.memberAt_persistD (m : Loc) (q : Qp) (mm : apply.MemberM) :
    membership.memberAt (GF := GF) m q mm ⊢ |==> membership.memberAtD m q mm := by
  unfold membership.memberAt membership.memberAtD
  iintro ⟨%Hnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
  imod ownSlice_persist $$ Hcus with #Hcus
  imodintro
  isplitr; (ipureintro; exact Hnn)
  iexists pu, cu
  iframe
  iexact Hcus

/-- **The glue at the monitors' permission** (`srvMonitorPermitM_of`'s): from the request view,
the server's id field and that it is a voter (`srvApRes`'s `srvMemberIDAddr` and `srvDynLog`, which
`Start` extracts from `isServerBuilt`'s `srvApRes s γr []` with `srvApRes_lid`, where it builds
the permission: `EtcdServer__Start.lean:103,133,248,278`). -/
theorem srvMonitorPermitMD_of (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (lid : w64)
    (hl : lid ∈ ρ.raft.raft.cfg) :
    isServerReqM (GF := GF) on s E ρ ∗ srvMemberIDAddr s ↦□ lid ⊢ srvMonitorPermitMD on s E ρ := by
  iintro ⟨#H, #Hid⟩
  ihave #HP := srvMonitorPermitM_of on s E ρ $$ H
  iunfold srvMonitorPermitM at HP
  icases HP with ⟨-, #HP⟩
  iunfold srvMonitorPermitMD
  iframe H
  iexists lid
  iframe Hid
  isplitr
  · ipureintro; exact hl
  iintro !> %rq %Gb %hrq
  iunfold reqPropOkMD
  isplitl
  · iapply HP; ipureintro; exact hrq.1
  ipureintro; exact attrIdOk_of_monitorReqD _ lid rq hrq hl

/-- The request path's other permissions name no attribute request (each producer's one line). -/
theorem reqPropOkMD_of_kind (on : Bool) (γ : ServerRaftNames) (γk : KVNames)
    (Gb : apply.HeaderModel → IProp GF) (rq : apply.IRRModel)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF)
    (h : apply.dispatchKind rq ≠ .clusterMemberAttrSet) :
    reqPropOkM (GF := GF) on γ γk Gb rq Qh ⊢ reqPropOkMD on γ γk Gb rq Qh := by
  iintro H
  iunfold reqPropOkMD
  iframe H
  ipureintro; exact attrIdOk_of_kind _ rq h

/-- **The workload facts, one entry on** (`kvWork_snoc`'s, with the entry's attribute fact). -/
theorem kvWorkD_snoc (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (hs : entryShape e) (hc : e.typ ≠ W32 0 → ccPolOk cfg e.data) (hk : entryPutsOk e)
    (ha : attrEntryOk cfg.cfg e) :
    ⊢ kvWorkD (GF := GF) cfg γk L -∗ entryClaim γk.ids e -∗ kvWorkD cfg γk (L ++ [e]) := by
  iintro Hw #He
  iunfold kvWorkD at Hw
  icases Hw with ⟨Hw, %Ha⟩
  iunfold kvWorkD
  isplitl
  · iapply (kvWork_snoc cfg γk L e hs hc hk) $$ Hw He
  ipureintro
  rw [attrLogOk_append]
  exact ⟨Ha, fun m hm => by rw [List.mem_singleton] at hm; subst hm; exact ha⟩

/-- **The server's id field, a voter** (`srvApRes`'s `srvMemberIDAddr` and `srvDynLog`): what
`Start` extracts from `isServerBuilt`'s `srvApRes s γr []` to build the monitors' permission
(`srvMonitorPermitMD_of`, `srvApRes_cfg_size`'s pattern). -/
theorem srvApRes_lid (s : Loc) (γr : ReadNames) (A : List EntryModel) :
    srvApRes (GF := GF) s γr A ⊢
      srvApRes s γr A ∗ ∃ lid : w64, srvMemberIDAddr s ↦□ lid ∗ ⌜lid ∈ γr.raft.raft.cfg⌝ := by
  unfold srvApRes
  iintro ⟨%bh, %ix, %lgh, %tl, %lid, %cl, %lgc, %cid, %prs, #H1, #H2, #H3, #H4, #H5, #H6, %H7, #H8,
    Hmr, %Hp, #Hd⟩
  iunfold srvDynLog at Hd
  icases Hd with %Hd
  isplitl
  · iexists bh, ix, lgh, tl, lid, cl, lgc, cid, prs
    iframe H1 H2 H3 H4 H5 H6 H8
    iframe
    isplitr
    · ipureintro; exact H7
    isplitr
    · ipureintro; exact Hp
    iunfold srvDynLog; ipureintro; exact Hd
  iexists lid
  iframe H4
  ipureintro; exact Hd

/-- Across committed entries of the server's policy (`srvMemOk_append`'s). -/
theorem srvMemOkD_append (γs : ServerRaftNames) (c0 : w64) (A B : List EntryModel)
    (h : srvMemOkD γs c0 A) (hB : ccLogOk γs.raft B) : srvMemOkD γs c0 (A ++ B) :=
  ⟨srvMemOk_append γs c0 A B h.1 hB, srvMemCover_append γs c0 A B h.2 hB⟩

end lemmas

end EtcdGrove
end Perennial
