/- Lean-first (no Rocq counterpart).

# `etcd/dist/server`: what `bootstrap` computes at a well-formed deployment's members (`BootGoD.of_wf`)

`BootGoD d (distPs d) (distCtxs d)` (`MemberDefs.lean`), the pure facts the member boot takes of `bootstrap`'s
values, holds of every well-formed deployment (N5/N6, `notes/etcd-dist-plan.md` §19): at every `BootURLs` a
member's configuration names (`urlsN (gmsD d)`), the initial cluster is the deployment's (its keys the members'
names, each to the one peer URL `http://peer`), so `bootGo`'s members, peers, contexts and directory are the same
there as at the statement's `distURLs d`, and

* the peers are a permutation of the members' ids (`bootGo.memberID` of one URL is `memberId`), and the
  directory is `dirD d`;
* the URLs are plain (`addrOk` addresses), the names plain (`nameOk`), one URL per entry, at most `typed.maxMembers` entries,
  and `initMapOk` (the ids distinct and nonzero by their 16 low bits, the sizes from `maxMembers`,
  `maxNameLen` and `addrOk`'s length);
* no member id is one of raft's local message targets (`Deployment.WellFormed.idsRaft`, Go's `RaftIdOk`).

Pure; a defs module.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MemberSplit
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootBuild

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

namespace BootGoD

section pure
variable [GooseExts]

/-! ## Lists -/

theorem eq_of_mem_of_nodup_map {α β : Type _} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, h, a, b, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with h1 | h1 <;> rcases List.mem_cons.1 hb with h2 | h2
    · rw [h1, h2]
    · subst h1
      exact absurd (show f a ∈ l.map f by rw [hab]; exact List.mem_map_of_mem h2) h.1
    · subst h2
      exact absurd (show f b ∈ l.map f by rw [← hab]; exact List.mem_map_of_mem h1) h.1
    · exact eq_of_mem_of_nodup_map f h.2 h1 h2 hab

theorem sum_map_le {α : Type _} (l : List α) (f : α → Nat) (c : Nat) (h : ∀ x ∈ l, f x ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h x (List.mem_cons_self ..)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

/-- The member of a list with the id `i`, when the ids are distinct. -/
theorem find?_id (L : List apply.MemberM) (hnd : (L.map (·.id)).Nodup) (m : apply.MemberM) (hm : m ∈ L)
    (i : w64) (hi : m.id = i) : L.find? (fun x => decide (x.id = i)) = some m := by
  cases h : L.find? (fun x => decide (x.id = i)) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by simpa using hi) (h m hm)
  | some x =>
    have hx := List.find?_some h
    have hxm := List.mem_of_find?_eq_some h
    simp only [decide_eq_true_eq] at hx
    rw [eq_of_mem_of_nodup_map (·.id) hnd hxm hm (show x.id = m.id by rw [hx, hi])]

/-! ## The initial cluster -/

/-- **The deployment's initial cluster at `U`**: its URLs by name `iuOf (gmsD d)` and its keys the members'
names (what `urlsN (gmsD d)` says of the initial cluster). -/
def InitOf (d : Deployment) (U : BootURLs) : Prop :=
  U.initURLs = iuOf (gmsD d) ∧ ∀ n, (U.initMap.lookup n).isSome ↔ n ∈ (gmsD d).map (·.Name')

theorem ofList_isSome {V : Type _} (l : List (GoString × V)) (n : GoString) :
    ((GMap.ofList l).lookup n).isSome ↔ n ∈ l.map Prod.fst := by
  induction l with
  | nil => simp [GMap.ofList, GMap.empty]
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    show ((if k = n then some v else (GMap.ofList l).lookup n).isSome) ↔ _
    by_cases h : k = n
    · subst h; simp
    · simp [h, ih, Ne.symm h]

theorem distURLs_initURLs (d : Deployment) : (distURLs d).initURLs = iuOf (gmsD d) := by
  funext n
  show (match d.members.find? (fun m => decide (m.name = n)) with
    | some m => [peerURL m.peer]
    | none => []) = iuOf (gmsD d) n
  unfold iuOf gmsD
  induction d.members with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases h : m.name = n
    · simp [gmOf, h, peerURL, httpURL]
    · simp only [gmOf, h, decide_false]
      exact ih

theorem distURLs_initOf (d : Deployment) : InitOf d (distURLs d) := by
  refine ⟨distURLs_initURLs d, fun n => ?_⟩
  show ((GMap.ofList (d.members.map (fun m => (m.name, slice.nil)))).lookup n).isSome ↔ _
  rw [ofList_isSome, List.map_map, gms_names]
  all_goals rfl

theorem initOf_of_urlsN (d : Deployment) (m : GMember) (U : BootURLs) (h : urlsN (gmsD d) m U) :
    InitOf d U :=
  ⟨h.2.2.2, h.2.2.1⟩

/-- **The member of a deployment member's entry** (`bootGo.memberOf`): its id `memberId`, its one peer URL. -/
def memberD (d : Deployment) (mm : Member) : apply.MemberM :=
  ⟨memberId (go!"http://" ++ mm.peer) d.token, [go!"http://" ++ mm.peer], false, mm.name, []⟩

theorem foldl_cast (l : List w8) (acc : Nat) :
    l.foldl (fun (acc : Int) b => acc * 256 + ((b.toNat : Nat) : Int)) (acc : Int) =
      ((l.foldl (fun acc b => acc * 256 + b.toNat) acc : Nat) : Int) := by
  induction l generalizing acc with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldl_cons]
    rw [show (acc : Int) * 256 + ((b.toNat : Nat) : Int) = ((acc * 256 + b.toNat : Nat) : Int) by omega]
    exact ih _

theorem foldl_cast0 (l : List w8) :
    l.foldl (fun (acc : Int) b => acc * 256 + ((b.toNat : Nat) : Int)) 0 =
      ((l.foldl (fun acc b => acc * 256 + b.toNat) 0 : Nat) : Int) :=
  foldl_cast l 0

/-- `bootGo.memberID` of one URL is `memberId`. -/
theorem memberID_one (u token : GoString) : bootGo.memberID [u] token = memberId u token := by
  unfold bootGo.memberID memberId membership.memberIdOf
  rw [List.mergeSort_singleton, List.flatten_singleton, bootGo.sha1_eq]
  unfold bootGo.be64
  simp only [W64]
  rw [foldl_cast0, BitVec.ofInt_natCast]

theorem memberD_id (d : Deployment) (mm : Member) :
    (memberD d mm).id = memberId (go!"http://" ++ mm.peer) d.token := rfl

theorem memberD_peerURLs (d : Deployment) (mm : Member) :
    (memberD d mm).peerURLs = [go!"http://" ++ mm.peer] := rfl

theorem memberD_id_mem (d : Deployment) (mm : Member) (hmm : mm ∈ d.members) : (memberD d mm).id ∈ d.ids := by
  rw [memberD_id]
  exact List.mem_map_of_mem hmm

/-- `urlStr` of `http://host` is `http://host`. -/
theorem urlStr_httpURL (p : GoString) : bootGo.urlStr (httpURL p) = go!"http://" ++ p := rfl

section facts
variable {d : Deployment} (Hd : d.WellFormed) {U : BootURLs} (hU : InitOf d U)
include Hd hU

theorem names_nodup : ((gmsD d).map (·.Name')).Nodup := by
  rw [gms_names]; exact Hd.members.2.1

theorem initURLs_member (mm : Member) (hmm : mm ∈ d.members) :
    U.initURLs mm.name = [httpURL mm.peer] := by
  rw [hU.1]
  exact iuOf_mem (gmsD d) (names_nodup Hd hU) (gmOf mm) (List.mem_map_of_mem hmm)

theorem memberOf_member (mm : Member) (hmm : mm ∈ d.members) :
    bootGo.memberOf U d.token mm.name = memberD d mm := by
  unfold bootGo.memberOf memberD
  rw [initURLs_member Hd hU mm hmm]
  simp only [List.map_cons, List.map_nil, urlStr_httpURL, memberID_one]

theorem key_member (k : GoString) (hk : (U.initMap.lookup k).isSome) :
    ∃ mm ∈ d.members, mm.name = k := by
  have h := (hU.2 k).1 hk
  rw [gms_names, List.mem_map] at h
  exact h

theorem dom_perm : U.initMap.domList.Perm (d.members.map (·.name)) := by
  refine (List.perm_ext_iff_of_nodup (GMap.nodup_dom_list _) Hd.members.2.1).2 (fun k => ?_)
  rw [GMap.mem_dom_list]
  have := hU.2 k
  rw [gms_names] at this
  exact this

/-- The entries' ids are the members' ids (up to order). -/
theorem entryIds_perm :
    (U.initMap.domList.map (fun k => (bootGo.memberOf U d.token k).id)).Perm d.ids := by
  refine ((dom_perm Hd hU).map _).trans ?_
  rw [List.map_map, Deployment.ids]
  refine List.Perm.of_eq (List.map_congr_left (fun mm hmm => ?_))
  simp only [Function.comp_apply, memberOf_member Hd hU mm hmm, memberD]

theorem entryIds_nodup : (U.initMap.domList.map (fun k => (bootGo.memberOf U d.token k).id)).Nodup :=
  (entryIds_perm Hd hU).nodup_iff.2 Hd.idsNodup.1

/-- `bootGo`'s members are the deployment's members' (`memberD`). -/
theorem mem_members (x : apply.MemberM) :
    x ∈ bootGo.members U d.token ↔ ∃ mm ∈ d.members, x = memberD d mm := by
  unfold bootGo.members
  rw [List.mem_mergeSort, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨mm, hmm, rfl⟩ := key_member Hd hU k ((GMap.mem_dom_list _ k).1 hk)
    exact ⟨mm, hmm, memberOf_member Hd hU mm hmm⟩
  · rintro ⟨mm, hmm, rfl⟩
    refine ⟨mm.name, (GMap.mem_dom_list _ _).2 ((hU.2 _).2 ?_), memberOf_member Hd hU mm hmm⟩
    rw [gms_names]; exact List.mem_map_of_mem hmm

theorem members_ids_nodup : ((bootGo.members U d.token).map (·.id)).Nodup := by
  have hp : (bootGo.members U d.token).Perm (U.initMap.domList.map (bootGo.memberOf U d.token)) := by
    unfold bootGo.members; exact List.mergeSort_perm _ _
  refine (hp.map _).nodup_iff.2 ?_
  rw [List.map_map]
  exact entryIds_nodup Hd hU

end facts

/-- **`bootGo`'s members are the same at every initial cluster of the deployment.** -/
theorem members_eq {d : Deployment} (Hd : d.WellFormed) {U V : BootURLs} (hU : InitOf d U)
    (hV : InitOf d V) : bootGo.members U d.token = bootGo.members V d.token := by
  have hle : ∀ a b : apply.MemberM, (decide (a.id.toNat ≤ b.id.toNat) || decide (b.id.toNat ≤ a.id.toNat)) = true :=
    fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  have htr : ∀ a b c : apply.MemberM, decide (a.id.toNat ≤ b.id.toNat) = true →
      decide (b.id.toNat ≤ c.id.toNat) = true → decide (a.id.toNat ≤ c.id.toNat) = true :=
    fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega
  apply List.Perm.eq_of_pairwise (le := fun a b : apply.MemberM => decide (a.id.toNat ≤ b.id.toNat) = true)
  · intro a b ha hb hab hba
    simp only [decide_eq_true_eq] at hab hba
    have hb' : b ∈ bootGo.members U d.token := by
      rw [mem_members Hd hU]; exact (mem_members Hd hV b).1 hb
    have hid : a.id = b.id := BitVec.eq_of_toNat_eq (by omega)
    exact eq_of_mem_of_nodup_map (·.id) (members_ids_nodup Hd hU) ha hb' hid
  · unfold bootGo.members
    exact List.pairwise_mergeSort (le := fun a b : apply.MemberM => decide (a.id.toNat ≤ b.id.toNat)) htr hle _
  · unfold bootGo.members
    exact List.pairwise_mergeSort (le := fun a b : apply.MemberM => decide (a.id.toNat ≤ b.id.toNat)) htr hle _
  · have hnd : ∀ {W : BootURLs}, InitOf d W → (bootGo.members W d.token).Nodup := fun hW =>
      List.Pairwise.of_map _ (fun a b h e => h (by rw [e])) (members_ids_nodup Hd hW)
    refine (List.perm_ext_iff_of_nodup (hnd hU) (hnd hV)).2 (fun x => ?_)
    rw [mem_members Hd hU, mem_members Hd hV]

theorem ps_eq {d : Deployment} (Hd : d.WellFormed) {U : BootURLs} (hU : InitOf d U) :
    bootGo.ps U d.token = distPs d := by
  unfold distPs bootGo.ps; rw [members_eq Hd hU (distURLs_initOf d)]

theorem ctxs_eq {d : Deployment} (Hd : d.WellFormed) {U : BootURLs} (hU : InitOf d U) :
    bootGo.ctxs U d.token = distCtxs d := by
  unfold distCtxs bootGo.ctxs; rw [members_eq Hd hU (distURLs_initOf d)]

/-- **The peers are a permutation of the members' ids.** -/
theorem distPs_perm {d : Deployment} (Hd : d.WellFormed) : (distPs d).Perm d.ids := by
  have hU := distURLs_initOf d
  unfold distPs bootGo.ps bootGo.members
  refine (((List.mergeSort_perm _ _).map _).trans ?_)
  rw [List.map_map]
  exact entryIds_perm Hd hU

/-- **The directory is `dirD d`.** -/
theorem dir_eq {d : Deployment} (Hd : d.WellFormed) {U : BootURLs} (hU : InitOf d U) :
    bootGo.dir U d.token = dirD d := by
  funext i
  unfold bootGo.dir
  by_cases hi : i ∈ d.ids
  · obtain ⟨mm, hmm, rfl⟩ := List.mem_map.1 hi
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmm
    rw [find?_id _ (members_ids_nodup Hd hU) (memberD d mm) ((mem_members Hd hU _).2 ⟨mm, hmm, rfl⟩)
      (memberId (go!"http://" ++ mm.peer) d.token) (memberD_id d mm), dirD_self d Hd.idsNodup.1 j mm hj]
    exact memberD_peerURLs d mm
  · have hn : (bootGo.members U d.token).find? (fun x => decide (x.id = i)) = none := by
      rw [List.find?_eq_none]
      intro x hx
      obtain ⟨mm, hmm, rfl⟩ := (mem_members Hd hU x).1 hx
      simp only [decide_eq_true_eq]
      intro he
      apply hi
      rw [← he]
      exact memberD_id_mem d mm hmm
    rw [hn]
    have : dirD d i = [] := Classical.byContradiction fun h => hi ((dirD_ne_nil Hd i).1 h)
    exact this.symm

/-! ## The URLs' and names' facts -/

theorem urlRootPlain_httpURL (p : GoString) (h : Net.addrOk p = true) : http.urlRootPlain (httpURL p) := by
  have hne : p ≠ [] := by
    intro e
    have := (addrOk_plainHostPort h).2.1
    rw [e] at this
    simp at this
  have hbytes : ∀ c ∈ p, http.hostByteNoEscape c := by
    intro c hc
    unfold http.hostByteNoEscape
    rcases addrOk_bytes h c hc with h1 | h1 | h1
    · omega
    · omega
    · simp only [Net.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h1; omega
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, hne, hbytes⟩
  all_goals simp [httpURL, stringToGoString]

theorem nameOk_plainEnc (n : GoString) (h : typed.nameOk n = true) : ∀ c ∈ n, JsonScan.plainEnc c := by
  intro b hb
  unfold typed.nameOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  rcases h.2 b hb with h | h | h | h <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

section facts2
variable {d : Deployment} (Hd : d.WellFormed) {U : BootURLs} (hU : InitOf d U)
include Hd hU

theorem urlsPlain : bootGo.bootURLsPlain U := by
  intro k hk u hu
  obtain ⟨mm, hmm, rfl⟩ := key_member Hd hU k hk
  rw [initURLs_member Hd hU mm hmm, List.mem_singleton] at hu
  subst hu
  exact urlRootPlain_httpURL _ ((Hd.peerAddrs.2 mm hmm).1)

theorem namesPlain : bootNamesPlain U := by
  intro k hk
  obtain ⟨mm, hmm, rfl⟩ := key_member Hd hU k hk
  exact nameOk_plainEnc _ (Hd.members.2.2.1 mm hmm)

theorem urlsOne (k : GoString) (hk : (U.initMap.lookup k).isSome) : (U.initURLs k).length = 1 := by
  obtain ⟨mm, hmm, rfl⟩ := key_member Hd hU k hk
  rw [initURLs_member Hd hU mm hmm]; rfl

theorem size_le : GMap.size U.initMap ≤ typed.maxMembers := by
  rw [GMap.size_eq_dom_list_length, (dom_perm Hd hU).length_eq, List.length_map]
  exact Hd.members.2.2.2.1

theorem initMapOk : bootGo.initMapOk U d.token := by
  have hp := entryIds_perm Hd hU
  have hsz := size_le Hd hU
  unfold typed.maxMembers at hsz
  have hlen : U.initMap.domList.length ≤ 1000 := by rwa [GMap.size_eq_dom_list_length] at hsz
  refine ⟨entryIds_nodup Hd hU, fun h0 => Hd.idsNodup.2 (hp.subset h0), by omega, ?_, ?_⟩
  · have := sum_map_le U.initMap.domList (fun k => (U.initURLs k).length) 1 (fun k hk =>
      Nat.le_of_eq (urlsOne Hd hU k ((GMap.mem_dom_list _ k).1 hk)))
    omega
  · have := sum_map_le U.initMap.domList
      (fun k => ((U.initURLs k).map (fun u => k.length + (bootGo.urlStr u).length + 2)).sum) 300
      (fun k hk => by
        obtain ⟨mm, hmm, rfl⟩ := key_member Hd hU k ((GMap.mem_dom_list _ k).1 hk)
        rw [initURLs_member Hd hU mm hmm]
        have h1 := Hd.members.2.2.2.2 mm hmm
        have h2 := addrOk_length_le (Hd.peerAddrs.2 mm hmm).1
        simp only [typed.maxNameLen] at h1
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, urlStr_httpURL,
          List.length_append]
        have : (go!"http://" : GoString).length = 7 := rfl
        omega)
    omega

theorem urlsNe : bootGo.urlsNe U := by
  intro k hk
  rw [← List.length_pos_iff, urlsOne Hd hU k hk]
  omega

end facts2

end pure

end BootGoD

open BootGoD in
/-- **What `bootstrap` computes at a well-formed deployment's members is `BootGoD`'s** (see the file header):
the peers `distPs d`, a permutation of the members' ids, and at every member's URLs Go's values and
`etcd_safe`'s shape, every member id one raft accepts. -/
theorem BootGoD.of_wf [GooseExts] {d : Deployment} (Hd : d.WellFormed) : BootGoD d (distPs d) (distCtxs d) := by
  refine ⟨distPs_perm Hd, fun m id hmid => ⟨Hd.idsRaft id (List.of_mem_zip hmid).2, fun U hu => ?_⟩⟩
  have hU := initOf_of_urlsN d m U hu
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmid
  rw [List.getElem?_zip_eq_some] at hj
  obtain ⟨hgm, hid⟩ := hj
  obtain ⟨mm, hmm, rfl⟩ : ∃ mm, d.members[j]? = some mm ∧ gmOf mm = m := by
    simp only [gmsD, List.getElem?_map, Option.map_eq_some_iff] at hgm
    exact hgm
  rw [ids_getElem? d j mm hmm, Option.some.injEq] at hid
  subst hid
  have hmem : mm ∈ d.members := List.mem_of_getElem? hmm
  refine ⟨urlsPlain Hd hU, ps_eq Hd hU, ctxs_eq Hd hU, dir_eq Hd hU, ?_, namesPlain Hd hU, urlsNe Hd hU,
    initMapOk Hd hU, urlsOne Hd hU, size_le Hd hU, ?_, ?_⟩
  · show (bootGo.memberOf U d.token mm.name).id = _
    simp only [memberOf_member Hd hU mm hmem, memberD]
  · rw [hu.1]
    show [httpURL mm.peer] = U.initURLs mm.name
    rw [initURLs_member Hd hU mm hmem]
  · simp [hu.2.1]

end etcd_dist
end EtcdGrove
end Perennial

end
