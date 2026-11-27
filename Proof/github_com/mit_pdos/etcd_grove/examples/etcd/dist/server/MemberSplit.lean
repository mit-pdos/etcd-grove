/- Lean-first (no Rocq counterpart).

# `etcd/dist/server`: lemmas of the member machine's proof (N5, `notes/etcd-dist-plan.md` §19)

What `server.MainLogger`'s proof uses besides its callees' specs:
* the facts a well-formed deployment gives of its members (`Deployment.WellFormed.idsLow`, `.peerAddrs`, the
  directory `dirD d` well formed, a member's own entry, a host of the directory a start member's peer address);
* the peer address facts of the start (`peerAddrFactsAt`, at the cluster's record) at a member's own record
  (`httpAddrAt` reads the record only through its cluster `γ.cl`: `httpAddrAt_cl`, `peerFactAt`);
* **`memberBuilt_split`**: before `Start`, a built member's receiver share of `s.readych` (`srvReadyRecv`), its
  place in the network and what `http.Serve`'s request goroutines borrow (`memberPeerServeRes`) split off
  `memberBuilt`, which is left with its peer address served (`true`);
* `memberUp_req`: a started member's request view (persistent), split off `memberUp`.
No program proof here.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MemberDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.MemberLessor
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadyRecv
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Start

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

/-! ## The deployment's members: pure facts -/

section pure
variable [GooseExts]

theorem zip_mem_getElem? {α β : Type _} : ∀ {l1 : List α} {l2 : List β} {i : Nat} {a : α} {b : β},
    l1[i]? = some a → l2[i]? = some b → (a, b) ∈ l1.zip l2
  | [], _, _, _, _, h1, _ => by simp at h1
  | _ :: _, [], _, _, _, _, h2 => by simp at h2
  | x :: xs, y :: ys, 0, a, b, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1; subst h2
    simp
  | x :: xs, y :: ys, i + 1, a, b, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    rw [List.zip_cons_cons]
    exact List.mem_cons_of_mem _ (zip_mem_getElem? h1 h2)

/-- Member `i`'s id, by index. -/
theorem ids_getElem? (d : Deployment) (i : Nat) (m : Member) (h : d.members[i]? = some m) :
    d.ids[i]? = some (memberId (go!"http://" ++ m.peer) d.token) := by
  simp [Deployment.ids, h]

theorem ids_getD (d : Deployment) (i : Nat) (m : Member) (h : d.members[i]? = some m) :
    d.ids.getD i (W64 0) = memberId (go!"http://" ++ m.peer) d.token := by
  simp [List.getD_eq_getElem?_getD, ids_getElem? d i m h]

theorem members_getD (d : Deployment) (i : Nat) (m : Member) (h : d.members[i]? = some m) :
    d.members.getD i ⟨go!"", go!"", go!""⟩ = m := by
  simp [List.getD_eq_getElem?_getD, h]

theorem ids_length (d : Deployment) : d.ids.length = d.members.length := by
  simp [Deployment.ids]

theorem gmsD_length (d : Deployment) : (gmsD d).length = d.members.length := by
  simp [gmsD]

/-- Member `i`, with its id, among the directory's members. -/
theorem gms_zip_mem (d : Deployment) (i : Nat) (m : Member) (h : d.members[i]? = some m) :
    (gmOf m, memberId (go!"http://" ++ m.peer) d.token) ∈ (gmsD d).zip d.ids :=
  zip_mem_getElem? (by simp [gmsD, h]) (ids_getElem? d i m h)

theorem gms_peers (d : Deployment) : (gmsD d).map (·.Peer') = d.members.map (·.peer) := by
  unfold gmsD; rw [List.map_map]; rfl

theorem gms_names (d : Deployment) : (gmsD d).map (·.Name') = d.members.map (·.name) := by
  unfold gmsD; rw [List.map_map]; rfl

theorem peerOf_names (d : Deployment) : (d.members.map peerOf).map (·.Name') = d.members.map (·.name) := by
  rw [List.map_map]; rfl

/-- Member `i`'s own directory entry. -/
theorem dirD_self (d : Deployment) (hnd : d.ids.Nodup) (i : Nat) (m : Member)
    (h : d.members[i]? = some m) :
    dirD d (memberId (go!"http://" ++ m.peer) d.token) = [go!"http://" ++ m.peer] := by
  unfold dirD
  rw [etcd_putgetN.dirN_of_mem _ _ hnd _ _ (gms_zip_mem d i m h)]
  rfl

/-- **A host of the directory is the peer address of a start member with that id.** -/
theorem cmsD_of_dirD (d : Deployment) (pid : w64) (a : GoString) (h : go!"http://" ++ a ∈ dirD d pid) :
    ∃ cm ∈ cmsD d, cm.id = pid ∧ cm.peer = a := by
  rcases etcd_putgetN.dirN_cases (gmsD d) d.ids pid with hd | ⟨g, hg, hd⟩
  · unfold dirD at h; rw [hd] at h; simp at h
  · unfold dirD at h
    rw [hd, List.mem_singleton] at h
    have ha : a = g.Peer' := List.append_cancel_left h
    unfold gmsD at hg
    rw [List.zip_map_left] at hg
    obtain ⟨⟨mm, id'⟩, hmem, he⟩ := List.mem_map.1 hg
    simp only [Prod.map, id, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨⟨mm.peer, mm.client, id'⟩, List.mem_map.2 ⟨(mm, id'), hmem, rfl⟩, rfl, ?_⟩
    rw [ha]; rfl

/-- A valid member name is ASCII. -/
theorem nameOk_ascii (n : GoString) (h : typed.nameOk n = true) : asciiStr n := by
  intro b hb
  unfold typed.nameOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  rcases h.2 b hb with h | h | h | h <;> omega

/-- The members' peer addresses are among the deployment's addresses. -/
theorem peers_sublist (ms : List Member) :
    (ms.map (·.peer)).Sublist (ms.flatMap (fun m => [m.peer, m.client])) := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
    exact List.Sublist.cons_cons m.peer (List.Sublist.cons m.client ih)

/-- **A well-formed deployment's members' ids have distinct, nonzero 16 low bits.** -/
theorem Deployment.WellFormed.idsLow {d : Deployment} (h : d.WellFormed) :
    (d.ids.map (fun id => uint.Z id % 2 ^ 16)).Nodup ∧ ∀ id ∈ d.ids, uint.Z id % 2 ^ 16 ≠ 0 := by
  obtain ⟨t, he, hw⟩ := h
  have e : t.ids = d.ids := by
    simp only [typed.Deployment.ids, Deployment.ids, he.1, he.2.1]
  rw [← e]
  exact ⟨hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1⟩

theorem Deployment.WellFormed.idsNodup {d : Deployment} (h : d.WellFormed) :
    d.ids.Nodup ∧ W64 0 ∉ d.ids := by
  obtain ⟨h1, h2⟩ := h.idsLow
  exact ⟨List.Pairwise.of_map _ (fun a b h e => h (by rw [e])) h1, fun h0 => h2 _ h0 (by decide)⟩

/-- **A well-formed deployment's members' peer addresses are distinct, and every member's addresses valid.** -/
theorem Deployment.WellFormed.peerAddrs {d : Deployment} (h : d.WellFormed) :
    (d.members.map (·.peer)).Nodup ∧
      ∀ m ∈ d.members, Net.addrOk m.peer = true ∧ Net.addrOk m.client = true := by
  obtain ⟨hnd, hok⟩ := h.addrs
  refine ⟨List.Nodup.sublist ((peers_sublist d.members).trans (List.sublist_append_left _ _)) hnd,
    fun m hm => ⟨hok _ ?_, hok _ ?_⟩⟩
  · exact List.mem_append_left _ (List.mem_flatMap.2 ⟨m, hm, by simp⟩)
  · exact List.mem_append_left _ (List.mem_flatMap.2 ⟨m, hm, by simp⟩)

/-- **The directory of a well-formed deployment is well formed** (`netDirOk`, `NewServer`'s premise). -/
theorem dirD_ok {d : Deployment} (h : d.WellFormed) : netDirOk (dirD d) := by
  obtain ⟨hnd, h0⟩ := h.idsNodup
  obtain ⟨hp, hok⟩ := h.peerAddrs
  refine etcd_putgetN.dirN_ok _ _ hnd h0 (by rw [gms_peers]; exact hp) (fun g hg => ?_)
  obtain ⟨mm, hmm, rfl⟩ := List.mem_map.1 hg
  exact addrOk_plainPeerURL (hok mm hmm).1

/-- The directory's members are the ids. -/
theorem dirD_ne_nil {d : Deployment} (h : d.WellFormed) (f : w64) : dirD d f ≠ [] ↔ f ∈ d.ids :=
  etcd_putgetN.dirN_ne_nil _ _ (by rw [gmsD_length, ids_length]) h.idsNodup.1 f

end pure

/-! ## The start's peer address facts at a member's record -/

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [π : NetProtoGS]

/-- `httpAddrAt` reads the server record only through its cluster. -/
theorem httpAddrAt_cl (γ γ' : SrvRaft) (hcl : γ'.cl = γ.cl) (id : w64) (a : GoString) :
    httpAddrAt (Gg := hG.goose_globalGS) γ' id a = httpAddrAt (Gg := hG.goose_globalGS) γ id a := by
  unfold httpAddrAt; rw [hcl]

/-- `bigSepL_mem` at an abstract `Φ` (no instance search on the predicate's unfolding). -/
theorem bigSepL_mem_any {A : Type _} (Φ : A → IProp GF) (l : List A) (x : A) (h : x ∈ l) :
    ([∗list] y ∈ l, Φ y) ⊢ Φ x :=
  BigSepL.bigSepL_mem h

/-- **A peer address fact of the start, at a record of the same cluster**: every host `a` of the directory at
`pid` has `httpAddrAt γ' pid a`. -/
theorem peerFactAt (γ γ' : SrvRaft) (hcl : γ'.cl = γ.cl) (d : Deployment) (pid : w64) (a : GoString)
    (h : go!"http://" ++ a ∈ dirD d pid) :
    peerAddrFactsAt (GF := GF) (G := hG.goose_globalGS) γ (cmsD d) ⊢
      httpAddrAt (Gg := hG.goose_globalGS) γ' pid a := by
  obtain ⟨cm, hcm, hid, hpe⟩ := cmsD_of_dirD d pid a h
  rw [httpAddrAt_cl γ γ' hcl, ← hid, ← hpe]
  exact bigSepL_mem_any (fun m : ClusterMember => httpAddrAt (Gg := hG.goose_globalGS) γ m.id m.peer)
    (cmsD d) cm hcm

end facts

/-! ## The built member, split before `Start` -/

section split
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `serverConfig`'s configuration with auth off is its configuration at a member configuration whose `Auth`
field is the literal `false` (so that its fields reduce). -/
theorem memberCfg_off (c : server.Config) (lg cluster : Loc) (pu cu : GoSlice) (fg : GoInterface)
    (h : c.Auth' = false) :
    memberCfg c lg cluster pu cu fg = memberCfg { c with Auth' := false } lg cluster pu cu fg := by
  cases c
  simp only at h
  subst h
  rfl

/-- `serverConfig`'s configuration with auth on is its configuration at a member configuration whose `Auth`
field is the literal `true` (so that its fields reduce: the simple token provider, a TTL of 300 s). -/
theorem memberCfg_on (c : server.Config) (lg cluster : Loc) (pu cu : GoSlice) (fg : GoInterface)
    (h : c.Auth' = true) :
    memberCfg c lg cluster pu cu fg = memberCfg { c with Auth' := true } lg cluster pu cu fg := by
  cases c
  simp only at h
  subst h
  rfl

/-- **`serverConfig`'s token provider with auth on** (`NewServer_dist`'s auth premise): the simple provider, with a
TTL (300 s) positive and below `2 ^ 32`. -/
theorem memberCfg_tokenOk (c : server.Config) (lg cluster : Loc) (pu cu : GoSlice) (fg : GoInterface)
    (h : c.Auth' = true) :
    (memberCfg c lg cluster pu cu fg).AuthToken' = go!"simple" ∧
      0 < uint.Z (memberCfg c lg cluster pu cu fg).TokenTTL' ∧
      uint.Z (memberCfg c lg cluster pu cu fg).TokenTTL' < 2 ^ 32 := by
  unfold memberCfg
  simp only [h, ↓reduceIte]
  refine ⟨?_, ?_, ?_⟩ <;> trivial

/-- **The WAL's slot of `serverConfig`'s configuration** (`wal.bootRes`): its data directory is the member's and
its dedicated WAL directory that directory's (`srvWalDirOf_lit`). -/
theorem memberCfg_bootRes (c : server.Config) (lg cluster : Loc) (pu cu : GoSlice) (fg : GoInterface) :
    memberAreasFresh (GF := GF) (memberDataDir c.Name') ⊢ wal.bootRes (memberCfg c lg cluster pu cu fg) :=
  wal.bootRes_intro _ _ (by unfold memberCfg; cases c.Auth' <;> rfl)
    (by unfold memberCfg; cases c.Auth' <;> exact srvWalDirOf_lit _)

theorem memberPeerServeRes_false (γn : NetNames GF) (τ : SrvTr GF) :
    memberPeerServeRes γn τ false ⊢
      [∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ := by
  unfold memberPeerServeRes
  simp only [Bool.false_eq_true, ↓reduceIte]
  try exact .rfl

theorem memberPeerServeRes_true (γn : NetNames GF) (τ : SrvTr GF) :
    ⊢ memberPeerServeRes γn τ true := by
  unfold memberPeerServeRes
  simp only [↓reduceIte]
  exact BI.true_intro

/-- **A built member, split before `Start`** (see the file header): the receiver's share of `s.readych`
(`srvReadyCh_recv`), and the member's place in the network with what `http.Serve`'s request goroutines borrow,
for the peer handler's server; `memberBuilt` is left with its peer address served. -/
theorem memberBuilt_split (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (N : Nat) (lm : lease.Mode) :
    etcdstart.memberBuilt s ρ E₀ lg γn id N false (m := lm) ⊢
      etcdstart.memberBuilt s ρ E₀ lg γn id N true (m := lm) ∗ srvReadyRecv s ∗
      ∃ τ : SrvTr GF, srvNetMember γn s id τ ∗
        [∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ := by
  iintro H
  iunfold etcdstart.memberBuilt at H
  icases H with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, Hstk, Hwb, Hsb, Hserve, Hsv, Hoff, Hmr,
    Hrc, #Hnm, Htokp, Hps, Hlr, Hkeep⟩
  ihave Hps := memberPeerServeRes_false γn τ $$ Hps
  iunfold srvReadyCloser at Hrc
  icases Hrc with ⟨Hrch, Hrc⟩
  icases srvReadyCh_recv s $$ Hrch with ⟨Hrch, #Hrr⟩
  isplitl [Hstk Hwb Hsb Hserve Hsv Hoff Hmr Hrch Hrc Htokp Hlr Hkeep]
  · iunfold etcdstart.memberBuilt
    iexists γA, ci, TM, E, γrn, b, cfg, γk, τ
    isplitr
    · ipureintro; exact HE
    isplitl [Hstk]
    · iexact Hstk
    isplitl [Hwb]
    · iexact Hwb
    isplitl [Hsb]
    · iexact Hsb
    isplitl [Hserve]
    · iexact Hserve
    isplitl [Hsv]
    · iexact Hsv
    isplitl [Hoff]
    · iexact Hoff
    isplitl [Hmr]
    · iexact Hmr
    isplitl [Hrch Hrc]
    · iunfold srvReadyCloser
      isplitl [Hrch]
      · iexact Hrch
      iexact Hrc
    isplitr
    · iexact Hnm
    isplitl [Htokp]
    · iexact Htokp
    isplitr
    · iapply memberPeerServeRes_true γn τ
    isplitl [Hlr]
    · iexact Hlr
    iexact Hkeep
  · isplitr
    · iexact Hrr
    iexists τ
    isplitr
    · iexact Hnm
    iexact Hps

/-- **A started member's request view** (persistent), split off `memberUp`: what etcd's peer handler takes
(`NewPeerHandler_dist`, `PeerServe_dist`, at auth off). -/
theorem memberUp_req (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (lm : lease.Mode) :
    etcdstart.memberUp s ρ E₀ lg γn id lm ⊢
      etcdstart.memberUp s ρ E₀ lg γn id lm ∗ ∃ (E : apply.AEnv GF) (ρ' : ReqNames),
        isServerReqM false s E ρ' := by
  iintro H
  iunfold etcdstart.memberUp at H
  icases H with ⟨%E, %cfg, %γw, %HE, Hstk, Hrs, #Hreq, Hrest⟩
  isplitl [Hstk Hrs Hrest]
  · iunfold etcdstart.memberUp
    iexists E, cfg, γw
    isplitr
    · ipureintro; exact HE
    isplitl [Hstk]
    · iexact Hstk
    isplitl [Hrs]
    · iexact Hrs
    isplitr
    · iexact Hreq
    iexact Hrest
  · iexists E, { ρ with wait := γw }
    rw [isServerReqM_false]
    iexact Hreq

/-- **`memberBuilt_split` with the lessor at `γl`** (F7 step 3's preparation): the same split of
`etcdstart.memberBuiltL`, which keeps its lessor name. -/
theorem memberBuiltL_split (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (N : Nat) (lm : lease.Mode) (γl : GName) :
    etcdstart.memberBuiltL s ρ E₀ lg γn id N false lm γl ⊢
      etcdstart.memberBuiltL s ρ E₀ lg γn id N true lm γl ∗ srvReadyRecv s ∗
      ∃ τ : SrvTr GF, srvNetMember γn s id τ ∗
        [∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ := by
  iintro H
  iunfold etcdstart.memberBuiltL at H
  icases H with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, Hstk, Hwb, Hsb, Hserve, Hsv, Hoff, Hmr,
    Hrc, #Hnm, Htokp, Hps, Hlr, Hkeep⟩
  ihave Hps := memberPeerServeRes_false γn τ $$ Hps
  iunfold srvReadyCloser at Hrc
  icases Hrc with ⟨Hrch, Hrc⟩
  icases srvReadyCh_recv s $$ Hrch with ⟨Hrch, #Hrr⟩
  isplitl [Hstk Hwb Hsb Hserve Hsv Hoff Hmr Hrch Hrc Htokp Hlr Hkeep]
  · iunfold etcdstart.memberBuiltL
    iexists γA, ci, TM, E, γrn, b, cfg, γk, τ
    isplitr
    · ipureintro; exact HE
    isplitl [Hstk]
    · iexact Hstk
    isplitl [Hwb]
    · iexact Hwb
    isplitl [Hsb]
    · iexact Hsb
    isplitl [Hserve]
    · iexact Hserve
    isplitl [Hsv]
    · iexact Hsv
    isplitl [Hoff]
    · iexact Hoff
    isplitl [Hmr]
    · iexact Hmr
    isplitl [Hrch Hrc]
    · iunfold srvReadyCloser
      isplitl [Hrch]
      · iexact Hrch
      iexact Hrc
    isplitr
    · iexact Hnm
    isplitl [Htokp]
    · iexact Htokp
    isplitr
    · iapply memberPeerServeRes_true γn τ
    isplitl [Hlr]
    · iexact Hlr
    iexact Hkeep
  · isplitr
    · iexact Hrr
    iexists τ
    isplitr
    · iexact Hnm
    iexact Hps

/-- **`memberUp_req` with the lessor at `γl`** (F7 step 3's preparation): the request view split off
`etcdstart.memberUpL`, which keeps its lessor name; at a mode (auth off's), as `NewPeerHandler_dist` takes it. -/
theorem memberUpL_req (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (lm : lease.Mode) (γl : GName) :
    etcdstart.memberUpL s ρ E₀ lg γn id lm γl ⊢
      etcdstart.memberUpL s ρ E₀ lg γn id lm γl ∗ ∃ (on : Bool) (E : apply.AEnv GF) (ρ' : ReqNames),
        isServerReqM on s E ρ' := by
  iintro H
  iunfold etcdstart.memberUpL at H
  icases H with ⟨%E, %cfg, %γw, %HE, Hstk, Hrs, #Hreq, Hrest⟩
  isplitl [Hstk Hrs Hrest]
  · iunfold etcdstart.memberUpL
    iexists E, cfg, γw
    isplitr
    · ipureintro; exact HE
    isplitl [Hstk]
    · iexact Hstk
    isplitl [Hrs]
    · iexact Hrs
    isplitr
    · iexact Hreq
    iexact Hrest
  · iexists false, E, { ρ with wait := γw }
    rw [isServerReqM_false]
    iexact Hreq

/-- **`memberBuiltL_split` with auth on** (#50 F7 S2 step 4): the same split of `etcdstart.memberBuiltOnL`. -/
theorem memberBuiltOnL_split (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (N : Nat) (γa : auth.AuthNames) (lm : lease.Mode) (γl : GName) :
    etcdstart.memberBuiltOnL s ρ E₀ lg γn id N false γa lm γl ⊢
      etcdstart.memberBuiltOnL s ρ E₀ lg γn id N true γa lm γl ∗ srvReadyRecv s ∗
      ∃ τ : SrvTr GF, srvNetMember γn s id τ ∗
        [∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ := by
  iintro H
  iunfold etcdstart.memberBuiltOnL at H
  icases H with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, Hstk, Hwb, Hsb, Hserve, Hsv, Hoff, Hmr,
    Hrc, #Hnm, Htokp, Hps, Hlr, Hkeep, #Htls, #HBF⟩
  ihave Hps := memberPeerServeRes_false γn τ $$ Hps
  iunfold srvReadyCloser at Hrc
  icases Hrc with ⟨Hrch, Hrc⟩
  icases srvReadyCh_recv s $$ Hrch with ⟨Hrch, #Hrr⟩
  isplitl [Hstk Hwb Hsb Hserve Hsv Hoff Hmr Hrch Hrc Htokp Hlr Hkeep]
  · iunfold etcdstart.memberBuiltOnL
    iexists γA, ci, TM, E, γrn, b, cfg, γk, τ
    isplitr
    · ipureintro; exact HE
    isplitl [Hstk]
    · iexact Hstk
    isplitl [Hwb]
    · iexact Hwb
    isplitl [Hsb]
    · iexact Hsb
    isplitl [Hserve]
    · iexact Hserve
    isplitl [Hsv]
    · iexact Hsv
    isplitl [Hoff]
    · iexact Hoff
    isplitl [Hmr]
    · iexact Hmr
    isplitl [Hrch Hrc]
    · iunfold srvReadyCloser
      isplitl [Hrch]
      · iexact Hrch
      iexact Hrc
    isplitr
    · iexact Hnm
    isplitl [Htokp]
    · iexact Htokp
    isplitr
    · iapply memberPeerServeRes_true γn τ
    isplitl [Hlr]
    · iexact Hlr
    isplitl [Hkeep]
    · iexact Hkeep
    isplitr
    · iexact Htls
    iexact HBF
  · isplitr
    · iexact Hrr
    iexists τ
    isplitr
    · iexact Hnm
    iexact Hps

/-- **`memberUpL_req` with auth on** (#50 F7 S2 step 4): the request view (at the auth slot `AuthC.on γa`'s
mode), split off `etcdstart.memberUpOnL`. -/
theorem memberUpOnL_req (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames) (lm : lease.Mode) (γl : GName) :
    etcdstart.memberUpOnL s ρ E₀ lg γn id γa lm γl ⊢
      etcdstart.memberUpOnL s ρ E₀ lg γn id γa lm γl ∗ ∃ (on : Bool) (E : apply.AEnv GF) (ρ' : ReqNames),
        isServerReqM on s E ρ' := by
  iintro H
  iunfold etcdstart.memberUpOnL at H
  icases H with ⟨%E, %cfg, %γw, %HE, Hstk, Hrs, #Hreq, Hrest⟩
  isplitl [Hstk Hrs Hrest]
  · iunfold etcdstart.memberUpOnL
    iexists E, cfg, γw
    isplitr
    · ipureintro; exact HE
    isplitl [Hstk]
    · iexact Hstk
    isplitl [Hrs]
    · iexact Hrs
    isplitr
    · iexact Hreq
    iexact Hrest
  · iexists (AuthC.on γa).isOn, E, { ρ with wait := γw }
    iexact Hreq

end split

end etcd_dist
end EtcdGrove
end Perennial

end
