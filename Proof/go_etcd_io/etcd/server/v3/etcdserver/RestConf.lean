/-
**The configuration a restart reads back** (the restart plan's R2b-3d gap 3, 2026-11-04; Lean-first):
the `members` bucket of the rest model at a committed log that starts with the bootstrap log holds
every boot member, each a voter, so every conf state `buildConfStateFromV3store` can build from it
(`v3ConfStateIs`) is the static cluster's membership (`restModel_confState`).

* Phase 1, the bootstrap log: each boot `AddNode` validates against the members saved before it
  (`membersOf_decode`: they decode to their peer URLs; `bootURLsOk`: none has the new member's;
  the ids distinct), so the bucket holds exactly the boot members saved so far (`bootInv`).
* Phase 2, the rest of the log: every entry of the bucket is a voter of the cluster under its own
  id, and every id of the cluster has an entry (`memVoters`): conf changes are `ccApplyOk`'s
  (`AddNode`s of voters of the cluster), attribute updates keep ids and learner flags.
* The conclusion: a conf state built from a bucket like that has the cluster's ids as voters and no
  learners (`memberEnc_id_learner`, `memberKey_inj`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestMemId

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The `members` bucket of the rest buckets `bk` (empty if absent). -/
abbrev memBktOf (bk : GMap GoString backend.BktData) : backend.BktData :=
  (bk.lookup go!"members").getD ∅

/-- The members the boot entries `P` save, in order (`ccMemberAt` of each decoded change). -/
def bootSaved (P : List EntryM) : List apply.MemberM :=
  P.filterMap fun e => (ccDecodeV1 e.Data').map membership.ccMemberAt

/-- The in-memory members are voters of `ps`, each under its own id. -/
def memOk (ps : List w64) (mem : GMap w64 apply.MemberM) : Prop :=
  ∀ id mm, mem.lookup id = some mm → mm.id = id ∧ id ∈ ps ∧ mm.isLearner = false

/-- **Phase 1's invariant**: after the boot entries `P`, the bucket holds exactly the members they
saved, nothing is removed, and the in-memory members are voters of `ps`. -/
def bootInv (ps : List w64) (P : List EntryM) (r : apply.RestM) : Prop :=
  memOk ps r.mem ∧
  (∀ k v, (memBktOf r.bk).lookup k = some v ↔
    ∃ mm ∈ bootSaved P, k = apply.memberKey mm.id ∧ v = apply.memberEnc mm) ∧
  (r.bk.lookup go!"members_removed").getD ∅ = ∅

/-- **Phase 2's invariant**: every entry of the bucket a voter of `ps` under its own id, every id of
`ps` with an entry; the in-memory members voters of `ps`. -/
def memVoters (ps : List w64) (r : apply.RestM) : Prop :=
  memOk ps r.mem ∧
  (∀ k v, (memBktOf r.bk).lookup k = some v →
    ∃ mm : apply.MemberM, k = apply.memberKey mm.id ∧ v = apply.memberEnc mm ∧ mm.id ∈ ps ∧
      mm.isLearner = false) ∧
  (∀ id ∈ ps, ∃ v, (memBktOf r.bk).lookup (apply.memberKey id) = some v)

/-! ### Rest-model steps on the `members` bucket -/

theorem memBktOf_putIn_other (r : apply.RestM) (n k v : GoString) (h : n ≠ go!"members") :
    memBktOf (r.putIn n k v).bk = memBktOf r.bk := by
  simp [memBktOf, apply.RestM.putIn, GMap.lookup_insert_eq_iff, h]

theorem memBktOf_putIn_members (r : apply.RestM) (k v : GoString) :
    memBktOf (r.putIn go!"members" k v).bk = (memBktOf r.bk).insert k v := by
  simp [memBktOf, apply.RestM.putIn, GMap.lookup_insert_eq_iff]

theorem removed_putIn_members (r : apply.RestM) (k v : GoString) :
    (r.putIn go!"members" k v).bk.lookup go!"members_removed" = r.bk.lookup go!"members_removed" := by
  have hne : go!"members" ≠ go!"members_removed" := by decide
  simp [apply.RestM.putIn, GMap.lookup_insert_eq_iff, hne]

/-! ### The in-memory members -/

theorem memOk_memBoot (ps : List w64) (boot : List EntryM)
    (hcc : ∀ e ∈ boot, ∀ cc, ccDecodeV1 e.Data' = some cc → ccApplyOk (GMap.listToSet ps) cc) :
    memOk ps (memBoot boot) := by
  unfold memBoot
  suffices H : ∀ (l : List EntryM), (∀ e ∈ l, ∀ cc, ccDecodeV1 e.Data' = some cc →
      ccApplyOk (GMap.listToSet ps) cc) → ∀ acc, memOk ps acc →
      memOk ps (l.foldl (fun mem e => match ccDecodeV1 e.Data' with
        | some cc => mem.insert cc.nodeId (membership.ccMemberAt cc)
        | none => mem) acc) from H boot hcc ∅ (fun id mm h => by simp at h)
  intro l
  induction l with
  | nil => intro _ acc h; exact h
  | cons e l ih =>
    intro hl acc h
    rw [List.foldl_cons]
    apply ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    split
    · next cc hd =>
      obtain ⟨-, hin, -, hlrn⟩ := hl e List.mem_cons_self cc hd
      intro id mm hm
      simp only [GMap.lookup_insert_eq_iff] at hm
      split at hm
      · next he =>
        cases hm
        exact ⟨he, by rw [← he]; exact (GMap.elem_of_list_to_set _ _).1 hin, hlrn⟩
      · exact h id mm hm
    · exact h

theorem memOk_insert (ps : List w64) (mem : GMap w64 apply.MemberM) (id : w64) (mm : apply.MemberM)
    (h : memOk ps mem) (hid : mm.id = id) (hin : id ∈ ps) (hl : mm.isLearner = false) :
    memOk ps (mem.insert id mm) := by
  intro id' mm' hm
  simp only [GMap.lookup_insert_eq_iff] at hm
  split at hm
  · next he => cases hm; exact ⟨hid.trans he, he ▸ hin, hl⟩
  · exact h id' mm' hm

/-! ### Phase 2 -/

theorem memVoters_putMember (ps : List w64) (r : apply.RestM) (mm : apply.MemberM)
    (h : memVoters ps r) (hin : mm.id ∈ ps) (hl : mm.isLearner = false) :
    memVoters ps (r.putIn go!"members" (apply.memberKey mm.id) (apply.memberEnc mm)) := by
  obtain ⟨hm, hf, hc⟩ := h
  refine ⟨hm, fun k v hk => ?_, fun id hid => ?_⟩
  · rw [memBktOf_putIn_members, GMap.lookup_insert_eq_iff] at hk
    split at hk
    · next he => cases hk; exact ⟨mm, he.symm, rfl, hin, hl⟩
    · exact hf k v hk
  · rw [memBktOf_putIn_members, GMap.lookup_insert_eq_iff]
    split
    · exact ⟨_, rfl⟩
    · exact hc id hid

theorem memVoters_other (ps : List w64) (r : apply.RestM) (n k v : GoString)
    (h : memVoters ps r) (hn : n ≠ go!"members") : memVoters ps (r.putIn n k v) := by
  obtain ⟨hm, hf, hc⟩ := h
  refine ⟨hm, ?_, ?_⟩
  · rw [memBktOf_putIn_other _ _ _ _ hn]; exact hf
  · rw [memBktOf_putIn_other _ _ _ _ hn]; exact hc

theorem restAfter_memVoters (ps : List w64) (rq : apply.IRRModel) (v3 : Bool) (r : apply.RestM)
    (h : memVoters ps r) : memVoters ps (apply.restAfter rq v3 r) := by
  unfold apply.restAfter
  split
  · unfold apply.restSetVersion
    split
    · exact memVoters_other _ _ _ _ _ h (by decide)
    · exact h
  · split
    · next a _ =>
      unfold apply.restUpdateAttrs
      split
      · exact h
      · next m hm =>
        obtain ⟨hid, hin, hl⟩ := h.1 _ _ hm
        have h1 : memVoters ps { r with mem := r.mem.insert a.memberID (m.withAttrs a) } :=
          ⟨memOk_insert ps r.mem _ _ h.1 hid hin hl, h.2.1, h.2.2⟩
        split
        · have := memVoters_putMember ps _ (m.withAttrs a) h1 (hid ▸ hin) hl
          simpa [apply.MemberM.withAttrs, hid] using this
        · exact h1
    · exact h

theorem ccRest_memVoters (ps : List w64) (v3 : Bool) (cc : ConfChangeM) (r : apply.RestM)
    (h : memVoters ps r) (hok : ccApplyOk (GMap.listToSet ps) cc) :
    memVoters ps (ccRest v3 cc r) := by
  obtain ⟨hty, hin, -, hl⟩ := hok
  have hin' : cc.nodeId ∈ ps := (GMap.elem_of_list_to_set _ _).1 hin
  unfold ccRest
  split
  · have h1 : memVoters ps { r with mem := r.mem.insert cc.nodeId (membership.ccMemberAt cc) } :=
      ⟨memOk_insert ps r.mem _ _ h.1 rfl hin' hl, h.2.1, h.2.2⟩
    exact memVoters_putMember ps _ (membership.ccMemberAt cc) h1 hin' hl
  · exact h

theorem restEntry_memVoters (ps : List w64) (c0 : w64) (e : EntryModel) (r : apply.RestM)
    (h : memVoters ps r)
    (hcc : e.typ ≠ W32 0 → ∀ cc, ccDecodeV1 e.data = some cc → ccApplyOk (GMap.listToSet ps) cc) :
    memVoters ps (restEntry c0 e r) := by
  unfold restEntry
  split
  · split
    · exact h
    · split
      · exact restAfter_memVoters _ _ _ _ h
      · exact h
  · next hty =>
    split
    · next cc hd => exact ccRest_memVoters _ _ _ _ h (hcc hty cc hd)
    · exact h

theorem fold_memVoters (ps : List w64) (c0 : w64) (R : List EntryModel) (r : apply.RestM)
    (h : memVoters ps r)
    (hcc : ∀ e ∈ R, e.typ ≠ W32 0 → ∀ cc, ccDecodeV1 e.data = some cc →
      ccApplyOk (GMap.listToSet ps) cc) :
    memVoters ps (R.foldl (fun r m => restEntry c0 m r) r) := by
  induction R generalizing r with
  | nil => exact h
  | cons e R ih =>
    rw [List.foldl_cons]
    exact ih _ (restEntry_memVoters ps c0 e r h (hcc e List.mem_cons_self))
      (fun e' he' => hcc e' (List.mem_cons_of_mem _ he'))


/-! ### Phase 1 -/

theorem bootSaved_append (P Q : List EntryM) : bootSaved (P ++ Q) = bootSaved P ++ bootSaved Q := by
  simp [bootSaved, List.filterMap_append]

theorem bootSaved_single (e : EntryM) (cc : ConfChangeM) (hd : ccDecodeV1 e.Data' = some cc) :
    bootSaved [e] = [membership.ccMemberAt cc] := by
  simp [bootSaved, hd]

/-- The saved members' peer URLs are the boot members'. -/
theorem bootSaved_peerURLs (P : List EntryM) :
    (bootSaved P).map (·.peerURLs) = (bootMembers P).map (·.peerURLs) := by
  induction P with
  | nil => rfl
  | cons e P ih =>
    simp only [bootSaved, bootMembers, List.filterMap_cons] at ih ⊢
    cases ccDecodeV1 e.Data' with
    | none => simpa using ih
    | some cc => simp [membership.ccMemberAt, ih]

/-- **One boot entry**: its `AddNode` validates and saves its member. -/
theorem boot_step (ps : List w64) (P : List EntryM) (e : EntryM) (r : apply.RestM)
    (h : bootInv ps P r) (hty : e.Type' = W32 1) (hidx : 0 < uint.Z e.Index')
    (cc : ConfChangeM) (hd : ccDecodeV1 e.Data' = some cc) (hok : ccApplyOk (GMap.listToSet ps) cc)
    (hnew : cc.nodeId ∉ (bootSaved P).map (·.id)) (hndP : ((bootSaved P).map (·.id)).Nodup)
    (hu : ∀ mm ∈ bootSaved P, ∀ u ∈ mm.peerURLs, utf8Valid u)
    (hdisj : ∀ mm ∈ bootSaved P, ∀ u ∈ mm.peerURLs, u ∉ (membership.ccMemberOf cc.context).peerURLs) :
    bootInv ps (P ++ [e]) (restEntry (W64 0) (EntryModel.ofM e) r) := by
  obtain ⟨hm, hb, hrm⟩ := h
  obtain ⟨hty0, hin, -, hl⟩ := hok
  have hin' : cc.nodeId ∈ ps := (GMap.elem_of_list_to_set _ _).1 hin
  -- the members read decode to the saved ones, none removed
  obtain ⟨hmems, hrmv⟩ := membership.membersOf_decode (r.bk.lookup go!"members")
    (r.bk.lookup go!"members_removed") (bootSaved P) [] hb hndP hu
    (fun k => by rw [hrm]; simp)
  have hvalid : membership.ccValidOn r.bk cc = true := by
    unfold membership.ccValidOn membership.membersOfBk
    classical
    apply decide_eq_true
    unfold membership.ccValidM
    refine ⟨by rw [hrmv]; simp, ?_⟩
    rw [if_pos hty0]
    refine ⟨?_, fun u hu' ⟨k, pus, hk, hupus⟩ => ?_⟩
    · rw [hmems]
      simp only [Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
      intro mm hmm hid
      exact hnew (List.mem_map.2 ⟨mm, hmm, hid⟩)
    · rw [hmems] at hk
      obtain ⟨mm, hf, rfl⟩ := Option.map_eq_some_iff.1 hk
      exact hdisj mm (List.mem_of_find?_eq_some hf) u hupus hu'
  have htyne : (EntryModel.ofM e).typ ≠ W32 0 := by
    simp only [EntryModel.ofM, hty]; decide
  have hv3 : decide (uint.Z (W64 0) < uint.Z (EntryModel.ofM e).index) = true := by
    simp only [EntryModel.ofM]; simpa using hidx
  unfold restEntry
  rw [if_neg htyne]
  simp only [EntryModel.ofM, hd]
  unfold ccRest
  rw [if_pos ⟨hv3, hvalid⟩, if_pos hty0]
  refine ⟨memOk_insert ps r.mem _ _ hm rfl hin' hl, fun k v => ?_, ?_⟩
  · rw [memBktOf_putIn_members, GMap.lookup_insert_eq_iff, bootSaved_append,
      bootSaved_single e cc hd]
    simp only [List.mem_append, List.mem_singleton]
    split
    · next hk =>
      constructor
      · intro hv; cases hv
        exact ⟨membership.ccMemberAt cc, Or.inr rfl, hk.symm, rfl⟩
      · rintro ⟨mm, hmm | rfl, rfl, rfl⟩
        · exfalso
          exact hnew (List.mem_map.2 ⟨mm, hmm, apply.memberKey_inj _ _ hk.symm⟩)
        · rfl
    · next hk =>
      rw [hb]
      constructor
      · rintro ⟨mm, hmm, h1, h2⟩; exact ⟨mm, Or.inl hmm, h1, h2⟩
      · rintro ⟨mm, hmm | rfl, h1, h2⟩
        · exact ⟨mm, hmm, h1, h2⟩
        · exact absurd h1.symm hk
  · rw [removed_putIn_members]; exact hrm

/-- **The boot entries `Q` after `P`**: each validates and saves its member. -/
theorem boot_fold (ps : List w64) (P Q : List EntryM) (r : apply.RestM) (h : bootInv ps P r)
    (hall : ∀ e ∈ Q, e.Type' = W32 1 ∧ 0 < uint.Z e.Index' ∧
      ∃ cc, ccDecodeV1 e.Data' = some cc ∧ ccApplyOk (GMap.listToSet ps) cc)
    (hnd : ((bootSaved (P ++ Q)).map (·.id)).Nodup) (hurl : bootURLsOk (P ++ Q)) :
    bootInv ps (P ++ Q) (Q.foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r) r) := by
  induction Q generalizing P r with
  | nil => simpa using h
  | cons e Q ih =>
    rw [List.foldl_cons]
    obtain ⟨hty, hidx, cc, hd, hok⟩ := hall e List.mem_cons_self
    have hPe : P ++ e :: Q = (P ++ [e]) ++ Q := by simp
    -- the ids and peer URLs of what is saved
    have hsv : bootSaved (P ++ e :: Q) = bootSaved P ++ membership.ccMemberAt cc :: bootSaved Q := by
      rw [hPe, bootSaved_append, bootSaved_append, bootSaved_single e cc hd]; simp
    have hnd0 := hnd
    have hurl0 := hurl
    rw [hsv, List.map_append, List.map_cons] at hnd
    have hndP : ((bootSaved P).map (·.id)).Nodup := (List.nodup_append.1 hnd).1
    have hnew : cc.nodeId ∉ (bootSaved P).map (·.id) := by
      intro hm
      exact (List.nodup_append.1 hnd).2.2 _ hm _ List.mem_cons_self rfl
    obtain ⟨hu, hpw⟩ := hurl
    have hpw' : ((bootSaved (P ++ e :: Q)).map (·.peerURLs)).Pairwise
        (fun a b => ∀ u ∈ a, u ∉ b) := by
      rw [bootSaved_peerURLs, List.pairwise_map]; exact hpw
    have huS : ∀ mm ∈ bootSaved (P ++ e :: Q), ∀ u ∈ mm.peerURLs, utf8Valid u := by
      intro mm hmm u hu'
      have : mm.peerURLs ∈ (bootMembers (P ++ e :: Q)).map (·.peerURLs) := by
        rw [← bootSaved_peerURLs]; exact List.mem_map.2 ⟨mm, hmm, rfl⟩
      obtain ⟨mm', hmm', he⟩ := List.mem_map.1 this
      exact hu mm' hmm' u (he ▸ hu')
    rw [hsv, List.map_append, List.map_cons, List.pairwise_append] at hpw'
    refine (hPe ▸ ih (P ++ [e]) _ (boot_step ps P e r h hty hidx cc hd hok hnew hndP
      (fun mm hmm => huS mm (by rw [hsv]; exact List.mem_append_left _ hmm))
      (fun mm hmm u hu' => hpw'.2.2 _ (List.mem_map.2 ⟨mm, hmm, rfl⟩) _ List.mem_cons_self u hu'))
      (fun e' he' => hall e' (List.mem_cons_of_mem _ he')) (hPe ▸ hnd0) (hPe ▸ hurl0))

/-! ### The conclusion -/

/-- **A conf state built from a bucket of voters of `ps` covering `ps` is `ps`'s membership.** -/
theorem confState_of_memVoters (ps : List w64) (hnd : ps.Nodup) (bk : backend.BktData)
    (hf : ∀ k v, bk.lookup k = some v →
      ∃ mm : apply.MemberM, k = apply.memberKey mm.id ∧ v = apply.memberEnc mm ∧ mm.id ∈ ps ∧
        mm.isLearner = false)
    (hc : ∀ id ∈ ps, ∃ v, bk.lookup (apply.memberKey id) = some v)
    (D : backend.Data) (hD : (D.lookup go!"members").getD ∅ = bk) :
    ∀ cs, v3ConfStateIs D cs → confStateIs cs (Membership.simple (GMap.listToSet ps)) := by
  intro cs ⟨ms, hms, hnd', hv, hlrn, hvo, hln, hal⟩
  rw [hD] at hms
  -- every member of `ms` a voter of `ps`
  have hmem : ∀ mm ∈ ms, mm.id ∈ ps ∧ mm.isLearner = false := by
    intro mm hmm
    obtain ⟨mm', hk, hv', hin, hl⟩ := hf _ _ ((hms _ _).2 ⟨mm, hmm, rfl, rfl⟩)
    obtain ⟨hid, hlr⟩ := apply.memberEnc_id_learner _ _ hv'
    have := apply.memberKey_inj _ _ hk
    exact ⟨this ▸ hin, hlr.trans hl⟩
  -- every id of `ps` some member's
  have hcov : ∀ id ∈ ps, id ∈ ms.map (·.id) := by
    intro id hid
    obtain ⟨v, hv'⟩ := hc id hid
    obtain ⟨mm, hmm, hk, -⟩ := (hms _ _).1 hv'
    exact List.mem_map.2 ⟨mm, hmm, (apply.memberKey_inj _ _ hk).symm⟩
  have hfl : ms.filter (fun mm => !mm.isLearner) = ms :=
    List.filter_eq_self.2 fun mm hmm => by simp [(hmem mm hmm).2]
  have hfl' : ms.filter (·.isLearner) = [] :=
    List.filter_eq_nil_iff.2 fun mm hmm => by simp [(hmem mm hmm).2]
  have hperm : ms.map (·.id) ≡ₚ ps :=
    (List.perm_ext_iff_of_nodup hnd' hnd).2 fun id =>
      ⟨fun h => by obtain ⟨mm, hmm, rfl⟩ := List.mem_map.1 h; exact (hmem mm hmm).1, hcov id⟩
  have hempty : ([] : List w64) ≡ₚ GMap.elements (∅ : GSet w64) := by
    refine (List.perm_ext_iff_of_nodup List.nodup_nil (GMap.NoDup_elements _)).2 ?_
    intro k
    rw [GMap.elem_of_elements]
    simp only [List.not_mem_nil, false_iff]
    exact GMap.not_elem_of_empty _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfl] at hv
    refine hv.trans (hperm.trans ?_)
    refine (List.perm_ext_iff_of_nodup hnd (GMap.NoDup_elements _)).2 ?_
    intro k; simp only [Membership.simple]; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]
  · rw [hvo]; exact hempty
  · rw [hfl'] at hlrn; exact hlrn.trans hempty
  · rw [hln]; exact hempty
  · exact hal

/-- The saved members' ids are the peers, when each boot entry adds its peer. -/
theorem bootSaved_ids_of (ps : List w64) (boot : List EntryM) (hlen : boot.length = ps.length)
    (hk : ∀ (k : Nat) (e : EntryM), boot[k]? = some e →
      ∃ m : ConfChangeM, ccDecodeV1 e.Data' = some m ∧ ps[k]? = some m.nodeId) :
    (bootSaved boot).map (·.id) = ps := by
  induction boot generalizing ps with
  | nil => cases ps with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons e boot ih =>
    cases ps with
    | nil => simp at hlen
    | cons p ps =>
      obtain ⟨cc, hd, hp⟩ := hk 0 e rfl
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      have hrest := ih ps (by simpa using hlen) (fun k e' he' => by
        simpa using hk (k + 1) e' (by simpa using he'))
      simp only [bootSaved, List.filterMap_cons, hd, Option.map_some] at hrest ⊢
      simp [membership.ccMemberAt, hp, hrest]

/-- The saved members' ids are the peers (`srvBootLogOk`). -/
theorem bootSaved_ids (ps : List w64) (boot : List EntryM) (h : srvBootLogOk ps boot) :
    (bootSaved boot).map (·.id) = ps := by
  obtain ⟨hlen, -, hk⟩ := h
  exact bootSaved_ids_of ps boot hlen fun k e he => by
    obtain ⟨-, -, -, m, hd, -, hp⟩ := hk k e he
    exact ⟨m, hd, hp⟩

/-- **What a restart reads back is the static cluster's membership** (see the file header): the
`members` bucket of the rest model at a committed log that starts with the bootstrap log `boot`
of the peers `ps` (distinct, their URLs `bootURLsOk`), whose conf changes are all `ccApplyOk`'s. -/
theorem restModel_confState (ps : List w64) (boot : List EntryM) (R : List EntryModel)
    (hps : srvBootLogOk ps boot) (hnd : ps.Nodup) (hurl : bootURLsOk boot)
    (hbcc : ∀ e ∈ boot, ∀ cc, ccDecodeV1 e.Data' = some cc → ccApplyOk (GMap.listToSet ps) cc)
    (hcc : ∀ e ∈ R, e.typ ≠ W32 0 → ∀ cc, ccDecodeV1 e.data = some cc →
      ccApplyOk (GMap.listToSet ps) cc)
    (D : backend.Data)
    (hD : D.lookup go!"members" =
      (restModel (W64 0) boot (boot.map EntryModel.ofM ++ R)).bk.lookup go!"members") :
    ∀ cs, v3ConfStateIs D cs → confStateIs cs (Membership.simple (GMap.listToSet ps)) := by
  have hids := bootSaved_ids ps boot hps
  -- phase 1
  have h0 : bootInv ps [] (restBoot boot) := by
    refine ⟨memOk_memBoot ps boot hbcc, fun k v => ?_, ?_⟩
    · simp [memBktOf, restBoot, restBootBk, GMap.lookup_insert_eq_iff, bootSaved]
    · simp [restBoot, restBootBk, GMap.lookup_insert_eq_iff]
  have hall : ∀ e ∈ boot, e.Type' = W32 1 ∧ 0 < uint.Z e.Index' ∧
      ∃ cc, ccDecodeV1 e.Data' = some cc ∧ ccApplyOk (GMap.listToSet ps) cc := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    obtain ⟨-, -, hkk⟩ := hps
    obtain ⟨-, hix, hty, cc, hd, -, -⟩ := hkk k _ (List.getElem?_eq_getElem hk)
    exact ⟨hty, by rw [hix]; omega, cc, hd, hbcc _ he cc hd⟩
  have h1 := boot_fold ps [] boot _ h0 hall (by simpa [hids] using hnd) (by simpa using hurl)
  simp only [List.nil_append] at h1
  -- phase 2
  have h2 : memVoters ps (boot.foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r)
      (restBoot boot)) := by
    obtain ⟨hm, hb, -⟩ := h1
    refine ⟨hm, fun k v hk => ?_, fun id hid => ?_⟩
    · obtain ⟨mm, hmm, rfl, rfl⟩ := (hb k v).1 hk
      refine ⟨mm, rfl, rfl, ?_, ?_⟩
      · rw [← hids]; exact List.mem_map.2 ⟨mm, hmm, rfl⟩
      · obtain ⟨e, he, hmm'⟩ := List.mem_filterMap.1 hmm
        obtain ⟨cc, hd, rfl⟩ := Option.map_eq_some_iff.1 hmm'
        exact (hbcc e he cc hd).2.2.2
    · rw [← hids] at hid
      obtain ⟨mm, hmm, rfl⟩ := List.mem_map.1 hid
      exact ⟨_, (hb _ _).2 ⟨mm, hmm, rfl, rfl⟩⟩
  have h3 := fold_memVoters ps (W64 0) R _ h2 hcc
  have hfold : restModel (W64 0) boot (boot.map EntryModel.ofM ++ R) =
      R.foldl (fun r m => restEntry (W64 0) m r)
        (boot.foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r) (restBoot boot)) := by
    simp [restModel, List.foldl_append, List.foldl_map]
  obtain ⟨-, hf, hc⟩ := h3
  rw [← hfold] at hf hc
  exact confState_of_memVoters ps hnd _ hf hc D (by rw [hD])

end pure

end EtcdGrove
end Perennial
