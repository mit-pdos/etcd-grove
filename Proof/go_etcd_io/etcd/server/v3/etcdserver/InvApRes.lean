/-
**The apply thread's membership resources** (D43 M5d/M5e, 2026-10-26; the user's (B): one
apply-thread resource). Lean-first (no Rocq counterpart).

`EtcdServer.applyConfChange` writes the cluster's members, raft's configuration and the
transport's peers. What it needs beyond the apply environment:
* `ccMembRes γs cl t lid rs`: in raft's static mode the cluster's static instance
  (`isRaftCluster`) and the frozen transport with its stop token (`trFrozenTok`: not stopped, so
  `AddPeer` of a known peer returns, `AddPeer_frozen`); in the dynamic mode the live transport
  (`trLive`, the peers' ids `rs`), the cluster's dynamic instance and the removed map's writer
  half (`rcRemovedOwn`).
* `ccPeersAfter v3 m bk rs`: the peers' ids after the change: a `RemoveNode` that passes the
  validation (`ccValidOn`, or no `v3`) removes its node (`transport.RemovePeer`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportState
public import Proof.go_etcd_io.etcd.server.v3.storage.InvHooks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- `s.beHooks`. -/
abbrev srvBeHooksAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"beHooks" s

/-- `s.r.transport` (the raft wrapper's `rnTransportAddr` at `s.r`). -/
abbrev srvTransportAddr (s : Loc) : Loc :=
  structFieldRef raftNodeConfig go!"transport" (structFieldRef raftNode go!"raftNodeConfig" (srvRAddr s))

/-- A `*rafthttp.Transport` as the server's `Transporter`. -/
abbrev srvTrIface (t : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty) #t

end addrs

section pure
variable [GooseExts]

/-- **The transport's peers after a conf change** (see the file header). -/
def ccPeersAfter (v3 : Bool) (m : ConfChangeM) (bk : GMap GoString backend.BktData) (rs : trIds) :
    trIds :=
  if m.type = W32 1 ∧ (v3 = false ∨ membership.ccValidOn bk m = true) then
    rs.filter (· != m.nodeId)
  else rs

/-- **The transport's peers cover the other boot members** (D43 M5d/M5e): in raft's static mode for
good, in the dynamic mode until the boot entries are applied (after them a `RemoveNode` may remove
one; an `AddNode` comes only before, the dynamic policy's `srvDynLog`). -/
def srvPeersCover (γs : ServerRaftNames) (lid : w64) (A : List EntryModel) (prs : trIds) : Prop :=
  (γs.raft.reDyn = none ∨ (γs.pre ++ A).length < γs.raft.reBoot.length) →
    ∀ f, f ∈ γs.raft.reCfg → f ≠ lid → f ∈ prs

/-- **The in-memory members stay among the boot configuration's** (D43 M5e: what keeps
`AddMember`'s bound, `size ≤ 2 ^ 62`): the members of the rest model at the applied log are
members of raft's boot configuration, of at most `2 ^ 62` members. -/
def srvMemOk (γs : ServerRaftNames) (c0 : w64) (A : List EntryModel) : Prop :=
  (∀ k, ((restModel c0 γs.raft.reBoot (γs.pre ++ A)).mem !! k).isSome = true → k ∈ γs.raft.reCfg) ∧
    GMap.size γs.raft.reCfg ≤ 2 ^ 62

/-- A normal entry keeps the members' ids. -/
theorem restEntry_normal_memKeys (c0 : w64) (m : EntryModel) (r : apply.RestM) (ht : m.typ = W32 0)
    (k : w64) : ((restEntry c0 m r).mem !! k).isSome = (r.mem !! k).isSome := by
  unfold restEntry
  rw [if_pos ht]
  split
  · rfl
  · split
    · rename_i rq _
      unfold apply.restAfter
      split
      · unfold apply.restSetVersion; split <;> rfl
      · split
        · rename_i a _
          unfold apply.restUpdateAttrs
          split
          · rfl
          · rename_i mm hl
            have hins : ((r.mem.insert a.memberID (mm.withAttrs a)) !! k).isSome = (r.mem !! k).isSome := by
              by_cases hk : a.memberID = k
              · subst hk; rw [GMap.lookup_insert, hl]; rfl
              · rw [GMap.lookup_insert_ne _ _ hk]
            split
            · exact hins
            · exact hins
        · rfl
    · rfl

theorem putIn_present (r : apply.RestM) (n' k v n : GoString) (h : (r.bk.lookup n).isSome) :
    ((r.putIn n' k v).bk.lookup n).isSome := by
  by_cases hn : n' = n
  · subst hn; simp [apply.RestM.putIn]
  · rw [putIn_other _ _ _ _ _ hn]; exact h

theorem delIn_present (r : apply.RestM) (n' k n : GoString) (h : (r.bk.lookup n).isSome) :
    ((r.delIn n' k).bk.lookup n).isSome := by
  by_cases hn : n' = n
  · subst hn; simp [apply.RestM.delIn]
  · rw [delIn_other _ _ _ _ hn]; exact h

/-- **A bucket present stays present** (every writer of the rest model puts or deletes in a
bucket, creating it if absent). -/
theorem restEntry_present (c0 : w64) (m : EntryModel) (r : apply.RestM) (n : GoString)
    (h : (r.bk.lookup n).isSome) : ((restEntry c0 m r).bk.lookup n).isSome := by
  unfold restEntry
  split
  · split
    · exact h
    · split
      · unfold apply.restAfter
        split
        · unfold apply.restSetVersion; split
          · exact putIn_present _ _ _ _ _ h
          · exact h
        · split
          · unfold apply.restUpdateAttrs
            split
            · exact h
            · split
              · exact putIn_present _ _ _ _ _ h
              · exact h
          · exact h
      · exact h
  · split
    · unfold ccRest
      split
      · split
        · exact putIn_present _ _ _ _ _ h
        · split
          · exact putIn_present _ _ _ _ _ (delIn_present _ _ _ _ h)
          · exact h
      · exact h
    · exact h

theorem restModel_present (c0 : w64) (bootLog : List EntryM) (L : List EntryModel) (n : GoString)
    (h : ((restBoot bootLog).bk.lookup n).isSome) : ((restModel c0 bootLog L).bk.lookup n).isSome := by
  unfold restModel
  generalize restBoot bootLog = r0 at h
  induction L generalizing r0 with
  | nil => exact h
  | cons m L ih => rw [List.foldl_cons]; exact ih _ (restEntry_present _ _ _ _ h)

theorem restModel_members (c0 : w64) (bootLog : List EntryM) (L : List EntryModel) :
    ((restModel c0 bootLog L).bk.lookup go!"members").isSome ∧
      ((restModel c0 bootLog L).bk.lookup go!"members_removed").isSome :=
  ⟨restModel_present _ _ _ _ (by simp [restBoot, restBootBk]),
    restModel_present _ _ _ _ (by simp [restBoot, restBootBk])⟩

/-- **The boot members' ids are the boot entries' nodes.** -/
theorem memBoot_keys (bootLog : List EntryM) (S : GSet w64)
    (h : ∀ e ∈ bootLog, ∀ cc, ccDecodeV1 e.Data' = some cc → cc.nodeId ∈ S) :
    ∀ k, ((memBoot bootLog) !! k).isSome = true → k ∈ S := by
  unfold memBoot
  suffices H : ∀ (l : List EntryM) (acc : GMap w64 apply.MemberM),
      (∀ k, (acc !! k).isSome = true → k ∈ S) →
      (∀ e ∈ l, ∀ cc, ccDecodeV1 e.Data' = some cc → cc.nodeId ∈ S) →
      ∀ k, ((l.foldl (fun mem e => match ccDecodeV1 e.Data' with
        | some cc => mem.insert cc.nodeId (membership.ccMemberOf cc.context)
        | none => mem) acc) !! k).isSome = true → k ∈ S from
    H bootLog ∅ (fun k hk => by simp at hk) h
  intro l
  induction l with
  | nil => intro acc hacc _ k hk; exact hacc k hk
  | cons e l ih =>
    intro acc hacc hl k hk
    rw [List.foldl_cons] at hk
    refine ih _ ?_ (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) k hk
    intro k' hk'
    cases hd : ccDecodeV1 e.Data' with
    | none => rw [hd] at hk'; exact hacc k' hk'
    | some cc =>
      rw [hd] at hk'
      by_cases hkk : cc.nodeId = k'
      · subst hkk; exact hl e (List.mem_cons_self) cc hd
      · rw [GMap.lookup_insert_ne _ _ hkk] at hk'; exact hacc k' hk'

/-- **The rest model's members at the start of a new cluster** are the boot peers (`BootLogOk`). -/
theorem srvMemOk_boot (γs : ServerRaftNames) (c0 : w64) (ccOk : w32 → List w8 → Prop)
    (ps : List w64) (hpre : γs.pre = []) (hcfg : γs.raft.reCfg = GMap.listToSet ps)
    (hnd : ps.Nodup) (hlen : (ps.length : Int) ≤ 2 ^ 62) (hb : BootLogOk ccOk ps γs.raft.reBoot) :
    srvMemOk γs c0 [] := by
  unfold srvMemOk
  rw [hpre, List.append_nil, restModel_nil, hcfg]
  refine ⟨memBoot_keys _ _ (fun e he cc hd => ?_), ?_⟩
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨-, -, -, ⟨m, hdm, -, hpk⟩, -⟩ := hb.2.2 k e hk
    rw [hd] at hdm
    cases hdm
    rw [GMap.elem_of_list_to_set]
    exact List.mem_of_getElem? hpk
  · rw [GMap.size_list_to_set _ hnd]; omega

/-- A map whose ids are members of a set is no larger than it. -/
theorem size_le_of_keys {V : Type} (mem : GMap w64 V) (S : GSet w64)
    (h : ∀ k, (mem !! k).isSome = true → k ∈ S) : GMap.size mem ≤ GMap.size S := by
  rw [← GMap.size_dom mem]
  apply GMap.subseteq_size
  rw [GMap.elem_of_subseteq]
  intro x hx
  apply h
  rw [GMap.elem_of_dom'] at hx
  exact hx

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The cluster and the transport, as `applyConfChange` writes them** (see the file header),
the transport `t` with the member `lid` and the peers' ids `rs`. -/
def ccMembRes (γs : ServerRaftNames) (cl t : Loc) (lid : w64) (rs : trIds) : IProp GF :=
  match γs.raft.reDyn with
  | none => iprop(membership.isRaftCluster cl ∗ ∃ (γn : NetNames GF) (c : TrN GF), ⌜c.lid = lid⌝ ∗
      trFrozen γn t c rs ∗ trFrozenTok c.γr rs)
  | some _ => iprop(∃ (γn : NetNames GF) (c : TrN GF) (γc : GName) (rm : GMap w64 Bool),
      ⌜c.lid = lid⌝ ∗ trLive γn t c rs ∗ membership.isRaftClusterG cl (membership.rcDyn γc) ∗
      membership.rcRemovedOwn γc rm)

/-- **The dynamic mode's positional policy** (persistent; D43 M5d, the user's decision: an
assumption of the dynamic mode, M8's dynamic `NewServer` establishes it): the local member `lid`
is a member of raft's configuration, and every conf entry of the committed log (`srvDynPol`, by
its position in raft's log) decodes to an `AddNode` among the boot entries (re-applied) or a
`RemoveNode` after them, never of the local member (the stopping server is M6's). True in raft's
static mode. -/
def srvDynLog (γs : ServerRaftNames) (lid : w64) : IProp GF :=
  match γs.raft.reDyn with
  | none => iprop(True)
  | some _ => iprop(⌜lid ∈ γs.raft.reCfg⌝ ∗ □ ∀ L : List EntryModel, srvRLogLb γs L -∗
      ⌜srvDynPol γs.raft.reBoot.length lid (srvLogOf γs L)⌝)

instance srvDynLog_persistent (γs : ServerRaftNames) (lid : w64) :
    Persistent (srvDynLog (GF := GF) γs lid) := by
  unfold srvDynLog; split <;> infer_instance

/-- **The apply thread's membership resource** (D43 M5d/M5e, the user's (B)) after the applied log
`A`: the server's fields `applyConfChange` reads (`s.beHooks` with the hooks' facts, `s.r.transport`,
`s.memberID`, `s.cluster` with its logger and id), the cluster and the transport as it writes them
(`ccMembRes`: in raft's static mode the frozen transport's stop token), the peers covering the other
boot members (`srvPeersCover`), the in-memory members among the boot configuration's
(`srvMemOk`), and the dynamic mode's positional policy (`srvDynLog`). -/
def srvApRes (s : Loc) (γr : ReadNames) (A : List EntryModel) : IProp GF :=
  iprop(∃ (bh : Loc) (ix : GoInterfaceOk) (lgh tl : Loc) (lid : w64) (cl lgc : Loc) (cid : w64)
      (prs : trIds),
    srvBeHooksAddr s ↦□ bh ∗ storage.isBackendHooks bh ix lgh ∗
    srvTransportAddr s ↦□ srvTrIface tl ∗ srvMemberIDAddr s ↦□ lid ∗
    srvClusterAddr s ↦□ cl ∗ membership.rcLgAddr cl ↦□ lgc ∗ ⌜lgc ≠ null⌝ ∗
    membership.rcCidAddr cl ↦□ cid ∗ ccMembRes γr.raft cl tl lid prs ∗
    ⌜srvPeersCover γr.raft lid A prs ∧ srvMemOk γr.raft γr.kv.c0 A⌝ ∗ srvDynLog γr.raft lid)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A normal entry keeps the resource** (the peers and the members as they are). -/
theorem srvApRes_normal (s : Loc) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ = W32 0) :
    srvApRes (GF := GF) s γr A ⊢ srvApRes s γr (A ++ [m]) := by
  unfold srvApRes
  iintro ⟨%bh, %ix, %lgh, %tl, %lid, %cl, %lgc, %cid, %prs, #H1, #H2, #H3, #H4, #H5, #H6, %H7, #H8,
    Hmr, %Hp, #Hd⟩
  iexists bh, ix, lgh, tl, lid, cl, lgc, cid, prs
  iframe Hmr
  iframe #
  ipureintro
  refine ⟨H7, ?_, ?_⟩
  · intro hc
    apply Hp.1
    rcases hc with h | h
    · exact .inl h
    · right; simp only [List.append_assoc, List.length_append, List.length_singleton] at h ⊢; omega
  · refine ⟨fun k hk => Hp.2.1 k ?_, Hp.2.2⟩
    rw [← List.append_assoc, restModel_append, restEntry_normal_memKeys _ _ _ ht] at hk
    exact hk

/-- The store's reader's token, lent from the apply thread's applier state (its sole writer's,
`mvcc.writerOwn_rt`). -/
theorem srvApplyKV_rt (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV) :
    srvApplyKV (GF := GF) s E γw x ⊢
      mvcc.storeRT E.γ ∗ (mvcc.storeRT E.γ -∗ srvApplyKV s E γw x) := by
  iintro H
  iunfold srvApplyKV at H
  icases H with ⟨%ua, Hua, #Hap, Hkv, Hbo, Hrest⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p, %Hp, Hu, Ho⟩
  iunfold apply.kvOwn at Ho
  icases Ho with ⟨Hsr, Hsw, Hll, Hrd, Hwo⟩
  icases mvcc.writerOwn_rt E.γ $$ Hwo with ⟨Hrt, Hwo⟩
  iframe Hrt
  iintro Hrt
  ihave Hwo := Hwo $$ Hrt
  iunfold srvApplyKV
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hap
  isplitl [Hu Hsr Hsw Hll Hrd Hwo]
  · iunfold apply.applyKV
    iexists p
    iframe Hu
    isplitr
    · ipureintro; exact Hp
    iunfold apply.kvOwn
    iframe
  isplitl [Hbo]
  · iexact Hbo
  iexact Hrest

/-- `srvApplyKV_ua` and `srvApplyKV_rt` at once. -/
theorem srvApplyKV_ua_rt (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV) :
    srvApplyKV (GF := GF) s E γw x ⊢ ∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗
      apply.applierFor ua E ∗ mvcc.storeRT E.γ ∗
      (srvUberApplyAddr s ↦ ua -∗ mvcc.storeRT E.γ -∗ srvApplyKV s E γw x) := by
  iintro H
  iunfold srvApplyKV at H
  icases H with ⟨%ua, Hua, #Hap, Hkv, Hbo, Hrest⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p, %Hp, Hu, Ho⟩
  iunfold apply.kvOwn at Ho
  icases Ho with ⟨Hsr, Hsw, Hll, Hrd, Hwo⟩
  icases mvcc.writerOwn_rt E.γ $$ Hwo with ⟨Hrt, Hwo⟩
  iexists ua
  iframe Hua Hrt
  isplitr
  · iexact Hap
  iintro Hua Hrt
  ihave Hwo := Hwo $$ Hrt
  iunfold srvApplyKV
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hap
  isplitl [Hu Hsr Hsw Hll Hrd Hwo]
  · iunfold apply.applyKV
    iexists p
    iframe Hu
    isplitr
    · ipureintro; exact Hp
    iunfold apply.kvOwn
    iframe
  isplitl [Hbo]
  · iexact Hbo
  iexact Hrest

/-- A conf change in the scope keeps the members among the boot configuration's. -/
theorem ccRest_memKeys (v3 : Bool) (cm : ConfChangeM) (r : apply.RestM) (S : GSet w64)
    (hin : cm.nodeId ∈ S) (h : ∀ k, (r.mem !! k).isSome = true → k ∈ S) :
    ∀ k, ((ccRest v3 cm r).mem !! k).isSome = true → k ∈ S := by
  intro k hk
  unfold ccRest at hk
  split at hk
  · split at hk
    · rw [apply.RestM.putIn_mem] at hk
      simp only at hk
      by_cases hkk : cm.nodeId = k
      · subst hkk; exact hin
      · rw [GMap.lookup_insert_ne _ _ hkk] at hk; exact h k hk
    · split at hk
      · rw [apply.RestM.putIn_mem, apply.RestM.delIn_mem] at hk
        simp only at hk
        by_cases hkk : cm.nodeId = k
        · subst hkk; rw [GMap.lookup_delete] at hk; cases hk
        · rw [GMap.lookup_delete_ne _ hkk] at hk; exact h k hk
      · exact h k hk
  · exact h k hk

/-- **The resource around a conf entry** `m` (decoding to `cm`, in the scope, the next entry after
`A`): the pieces `applyConfChange` takes, the premises it asks of them, and the way back, after
it, to the resource after `A ++ [m]`. -/
theorem srvApRes_cc (s : Loc) (γr : ReadNames) (A : List EntryModel) (m : EntryModel) (cm : ConfChangeM)
    (γs : ServerRaftNames) (hγs : γs = γr.raft)
    (hty : m.typ ≠ W32 0) (hdec : ccDecodeV1 m.data = some cm) (hok : ccApplyOkM γr.raft cm)
    (hidx : uint.Z m.index = (γr.raft.pre ++ A).length + 1) :
    srvApRes (GF := GF) s γr A ∗ srvRLogLb γr.raft (A ++ [m]) ⊢
      ∃ (bh : Loc) (ix : GoInterfaceOk) (lgh tl : Loc) (lid : w64) (cl lgc : Loc) (cid : w64)
        (prs : trIds),
        srvBeHooksAddr s ↦□ bh ∗ storage.isBackendHooks bh ix lgh ∗
        srvTransportAddr s ↦□ srvTrIface tl ∗ srvMemberIDAddr s ↦□ lid ∗
        srvClusterAddr s ↦□ cl ∗ membership.rcLgAddr cl ↦□ lgc ∗ ⌜lgc ≠ null⌝ ∗
        membership.rcCidAddr cl ↦□ cid ∗ ccMembRes γs cl tl lid prs ∗
        ⌜(cm.type = W32 0 → cm.nodeId ≠ lid → cm.nodeId ∈ prs) ∧
          (cm.type = W32 1 → cm.nodeId ≠ lid) ∧
          (cm.type = W32 0 → GMap.size (GMap.insert cm.nodeId (membership.ccMemberAt cm)
            (restModel γr.kv.c0 γr.raft.raft.reBoot (γr.raft.pre ++ A)).mem) ≤ 2 ^ 62) ∧
          (γr.raft.raft.reDyn.isSome = true →
            srvDynPol γr.raft.raft.reBoot.length lid (srvLogOf γr.raft (A ++ [m])) ∧
            lid ∈ γr.raft.raft.reCfg)⌝ ∗
        (∀ v3 : Bool, ccMembRes γs cl tl lid (ccPeersAfter v3 cm
            (restModel γr.kv.c0 γr.raft.raft.reBoot (γr.raft.pre ++ A)).bk prs) -∗
          srvApRes s γr (A ++ [m])) := by
  subst hγs
  iintro ⟨H, #Hlb⟩
  unfold srvApRes
  icases H with ⟨%bh, %ix, %lgh, %tl, %lid, %cl, %lgc, %cid, %prs, #H1, #H2, #H3, #H4, #H5, #H6,
    %H7, #H8, Hmr, %Hp, #Hd⟩
  -- the positional policy, in the dynamic mode
  ihave %Hdyn : ⌜γr.raft.raft.reDyn.isSome = true →
      srvDynPol γr.raft.raft.reBoot.length lid (srvLogOf γr.raft (A ++ [m])) ∧
      lid ∈ γr.raft.raft.reCfg⌝ $$ []
  · cases hrd : γr.raft.raft.reDyn with
    | none => ipureintro; intro h; cases h
    | some f =>
      unfold srvDynLog
      rw [hrd]
      icases Hd with ⟨%Hl, #Hd⟩
      ihave %Hd' := Hd $$ %(A ++ [m]) Hlb
      ipureintro; intro _
      exact ⟨Hd', Hl⟩
  have Hpos : γr.raft.raft.reDyn ≠ none → (cm.type = W32 0 →
      uint.Z m.index ≤ γr.raft.raft.reBoot.length) ∧
      (cm.type = W32 1 → γr.raft.raft.reBoot.length < uint.Z m.index ∧ cm.nodeId ≠ lid) := by
    intro hn
    have hs : γr.raft.raft.reDyn.isSome = true := by
      cases h : γr.raft.raft.reDyn with
      | none => exact absurd h hn
      | some _ => rfl
    have hp : (srvLogOf γr.raft (A ++ [m]))[(γr.raft.pre ++ A).length]? = some m.toM := by
      unfold srvLogOf; simp
    have := (Hdyn hs).1 _ m.toM cm hp hty hdec
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := this.1 h; omega
    · have := this.2 h; exact ⟨by omega, this.2⟩
  have hin : cm.nodeId ∈ γr.raft.raft.reCfg := by
    rcases hok with ⟨-, h, -⟩ | ⟨-, -, h⟩ <;> exact h
  have hstat1 : cm.type = W32 1 → γr.raft.raft.reDyn ≠ none := by
    intro h1 hn
    rcases hok with ⟨h0, -⟩ | ⟨h, -⟩
    · rw [h1] at h0; exact absurd h0 (by simp)
    · rw [hn] at h; cases h
  iexists bh, ix, lgh, tl, lid, cl, lgc, cid, prs
  iframe H1 H2 H3 H4 H5 H6 H8 Hmr
  isplitr
  · ipureintro; exact H7
  isplitr
  · ipureintro
    refine ⟨?_, ?_, ?_, Hdyn⟩
    · intro h0 hne
      apply Hp.1 _ _ hin hne
      by_cases hrd : γr.raft.raft.reDyn = none
      · exact .inl hrd
      · right; have := (Hpos hrd).1 h0; omega
    · intro h1; exact ((Hpos (hstat1 h1)).2 h1).2
    · intro _
      calc GMap.size (GMap.insert cm.nodeId (membership.ccMemberAt cm) _)
          ≤ GMap.size γr.raft.raft.reCfg := size_le_of_keys _ _ (by
            intro k hk
            by_cases hkk : cm.nodeId = k
            · subst hkk; exact hin
            · rw [GMap.lookup_insert_ne _ _ hkk] at hk; exact Hp.2.1 k hk)
        _ ≤ 2 ^ 62 := Hp.2.2
  iintro %v3 Hmr
  iexists bh, ix, lgh, tl, lid, cl, lgc, cid, _
  iframe Hmr
  iframe #
  ipureintro
  refine ⟨H7, ?_, ?_, Hp.2.2⟩
  · intro hc f hf hne
    unfold ccPeersAfter
    split
    · rename_i h
      exfalso
      have hd := hstat1 h.1
      have := ((Hpos hd).2 h.1).1
      rcases hc with hc | hc
      · exact hd hc
      · simp only [List.length_append, List.length_singleton] at hc hidx
        omega
    · apply Hp.1 _ f hf hne
      rcases hc with hc | hc
      · exact .inl hc
      · right; simp only [List.length_append, List.length_singleton] at hc ⊢; omega
  · intro k hk
    rw [← List.append_assoc, restModel_append, restEntry_cc _ _ cm _ hty hdec] at hk
    exact ccRest_memKeys _ cm _ _ hin Hp.2.1 k hk

end lemmas

end EtcdGrove
end Perennial
