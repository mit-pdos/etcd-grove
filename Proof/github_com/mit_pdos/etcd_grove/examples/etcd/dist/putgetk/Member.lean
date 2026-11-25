/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putgetk/Member.lean` (plan item 4,
`notes/putget-dist-plan.md` §13b). Lean-first (no Rocq counterpart).

`Member(i, peers, clients)`: unless `i < len(peers)` and `Valid(peers, clients)` (whose `true` gives `cfgOk`), it
returns at once. Else the start's share applies (`memberShareK`): the initial cluster's map is built as
`etcdstart.StartMembers` builds it (after `k` members its keys are their names `nameOf j`, each slice the
member's one peer URL, `iuOf`); member `i`'s `memberBoot` comes from its slice (`etcdstart.memberBoot_of_slice`,
at the cluster's names); `StartMember` on a member machine is the named hypothesis
`etcd_dist.StartMember_dist.spec S5` (S5's), its premises discharged from the configuration (the directory
`etcd_putgetN.dirN`, well formed by `dirN_ok`, within the transport's bound since the ids' 16 low bits are
distinct, `idPfxsOf_ok`; the URLs `urlsN`; the names `nameOf j` distinct, ASCII and short) and from the share
(every peer address's `httpAddrAt`, `peerAddrFacts`); `etcdstart.Serve` on a member machine is
`etcd_dist.Serve_dist` (interim axiom) at the cluster's view, the request names' KV names `kvCongr` to its
(`memberBoot_of_slice`; O1 option B, `notes/etcd-dist-plan.md` §18.3, no publication); `holdForever()` does not
return.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Member
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Valid
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Name
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.holdForever
public import Spec.go_uber_org.zap.NewNop
public import Spec.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.go_etcd_io.raft.v3.BootMarshal
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ServeDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.StartMemberDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Start

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

/-! ## The configuration's members: pure facts -/

section pure
variable [GooseExts]

theorem mOf_length (peers clients : List GoString) :
    (membersOf peers clients).length = peers.length := by
  simp [membersOf]

theorem mOf_getElem? (peers clients : List GoString) (j : Nat) :
    (membersOf peers clients)[j]? =
      peers[j]?.map (fun p => (⟨nameOf j, p, clients.getD j go!""⟩ : GMember)) := by
  simp [membersOf, List.getElem?_mapIdx]

theorem mOf_at (peers clients : List GoString) (j : Nat) (p c : GoString) (hp : peers[j]? = some p)
    (hc : clients[j]? = some c) :
    (membersOf peers clients)[j]? = some (⟨nameOf j, p, c⟩ : GMember) := by
  rw [mOf_getElem?, hp]
  simp [List.getD_eq_getElem?_getD, hc]

theorem mOf_names (peers clients : List GoString) :
    (membersOf peers clients).map (·.Name') = (List.range peers.length).map nameOf := by
  apply List.ext_getElem (by simp [mOf_length])
  intro n h1 h2
  simp [membersOf]

theorem mOf_peers (peers clients : List GoString) :
    (membersOf peers clients).map (·.Peer') = peers := by
  apply List.ext_getElem (by simp [mOf_length])
  intro n h1 h2
  simp [membersOf]

theorem mOf_peer_mem (peers clients : List GoString) (m : GMember) (hm : m ∈ membersOf peers clients) :
    m.Peer' ∈ peers := by
  rw [← mOf_peers peers clients]
  exact List.mem_map_of_mem hm

theorem ids_at (peers : List GoString) (j : Nat) (p : GoString) (hp : peers[j]? = some p) :
    (idsOf peers)[j]? = some (memberIdOf p) := by
  simp [idsOf, hp]

/-- The start's members, by index. -/
theorem cms_eq (peers clients : List GoString) :
    cmsOf (membersOf peers clients) (idsOf peers) =
      peers.mapIdx (fun j p => (⟨p, clients.getD j go!"", memberIdOf p⟩ : etcd_dist.ClusterMember)) := by
  apply List.ext_getElem (by simp [cmsOf, membersOf, idsOf])
  intro n h1 h2
  simp [cmsOf, membersOf, idsOf]

theorem cms_ids (peers clients : List GoString) :
    (cmsOf (membersOf peers clients) (idsOf peers)).map (·.id) = idsOf peers := by
  rw [cms_eq]
  apply List.ext_getElem (by simp [idsOf])
  intro n h1 h2
  simp [idsOf]

theorem cms_peers (peers clients : List GoString) :
    (cmsOf (membersOf peers clients) (idsOf peers)).map (·.peer) = peers := by
  rw [cms_eq]
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp

theorem cms_getD (peers clients : List GoString) (j : Nat) (p c : GoString) (hp : peers[j]? = some p)
    (hc : clients[j]? = some c) :
    (cmsOf (membersOf peers clients) (idsOf peers)).getD j ⟨go!"", go!"", W64 0⟩ =
      (⟨p, c, memberIdOf p⟩ : etcd_dist.ClusterMember) := by
  rw [cms_eq]
  simp [List.getD_eq_getElem?_getD, List.getElem?_mapIdx, hp, hc]

theorem zip_mem_of {α β : Type _} : ∀ {l1 : List α} {l2 : List β} {i : Nat} {a : α} {b : β},
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
    exact List.mem_cons_of_mem _ (zip_mem_of h1 h2)

/-- Member names are distinct (`decStr` injective). -/
theorem nameOf_inj {j j' : Nat} (hj : j < 2 ^ 64) (hj' : j' < 2 ^ 64) (h : nameOf j = nameOf j') :
    j = j' := by
  unfold nameOf at h
  have h1 := List.append_cancel_left h
  have h2 : W64 j = W64 j' := decStr_inj h1
  have h3 := congrArg BitVec.toNat h2
  simp [W64] at h3
  omega

theorem nameOf_len (j : Nat) : (nameOf j).length ≤ 200 := by
  have h := etcdstart.decStr_length_le (W64 j)
  have h8 : (go!"putgetk-" : GoString).length = 8 := by decide
  unfold decStr at h
  unfold nameOf
  rw [List.length_append]
  omega

theorem nameOf_utf8 (j : Nat) : utf8Valid (nameOf j) := by
  have h : asciiStr (go!"putgetk-" ++ decStr (W64 j)) :=
    etcdstart.ascii_append (fun b hb => by revert b; decide) (etcdstart.decStr_ascii _)
  exact utf8Valid_of_ascii _ h

theorem mOf_names_nodup (peers clients : List GoString) (h : peers.length ≤ 2 ^ 64) :
    ((membersOf peers clients).map (·.Name')).Nodup := by
  rw [mOf_names]
  refine List.pairwise_map.2 (List.Pairwise.imp_of_mem ?_ List.nodup_range)
  intro a b ha hb hne he
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  exact hne (nameOf_inj (by omega) (by omega) he)

theorem iuOf_at (peers clients : List GoString)
    (hnd : ((membersOf peers clients).map (·.Name')).Nodup) (j : Nat) (p : GoString)
    (h : peers[j]? = some p) :
    iuOf (membersOf peers clients) (nameOf j) = [httpURL p] :=
  iuOf_mem _ hnd ⟨nameOf j, p, clients.getD j go!""⟩
    (List.mem_of_getElem? (show (membersOf peers clients)[j]? =
      some (⟨nameOf j, p, clients.getD j go!""⟩ : GMember) by simp [mOf_getElem?, h]))

end pure

/-! ## Every peer's address fact, from the start's share -/

section facts
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
  [GoGlobalContext] [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
  [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

theorem peerFact_of (S5 : etcd_dist.S5Draft GF) (ms : List etcd_dist.ClusterMember) (a : GoString)
    (h : a ∈ ms.map (·.peer)) : etcd_dist.peerAddrFacts S5 ms ⊢ S5.httpAddrAt a := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
  unfold etcd_dist.peerAddrFacts
  exact BigSepL.bigSepL_mem (Φ := fun m => S5.httpAddrAt m.peer) hm

end facts

open Lean Elab Tactic Meta in
/-- Case on an innermost `decide p` of the goal (one whose `p` has no `decide`): `Hd : decide p = bd`,
`bd` split (`false`, `true`), and the conditions on `bd` simplified. -/
local elab "dcase" : tactic => do
  let isDec : Lean.Expr → Bool := fun e => e.isAppOfArity ``Decidable.decide 2
  let tgt ← instantiateMVars (← getMainTarget)
  let some d := tgt.find? (fun e => isDec e && !(e.appFn!.appArg!.find? isDec).isSome)
    | throwError "dcase: no decide in the goal"
  let dStx ← Term.exprToSyntax d
  let hd := mkIdent `Hd
  let bd := mkIdent `bd
  evalTactic (← `(tactic| (generalize $hd:ident : $dStx = $bd:ident; cases $bd:ident <;> cleanup_bool_decide <;>
    (try simp only [Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false, eq_self_iff_true,
      decide_eq_true_eq, ↓reduceIte]))))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 3200000 in
theorem Member.wp_proof
    (wp_Valid : Valid.spec (GF := GF) (hG := hG))
    (wp_Name : Name.spec (GF := GF) (hG := hG))
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_holdForever : holdForever.spec (GF := GF) (hG := hG))
    (wp_Serve_dist : etcd_dist.Serve_dist.spec (GF := GF) (hG := hG))
    (wp_StartMember_dist : ∀ [π : Net.NetProtoGS] (S5 : etcd_dist.S5Draft (G := hG.goose_globalGS) GF),
      etcd_dist.StartMember_dist.spec (GF := GF) (hG := hG) S5)
    (hne : mvcc.api.names_nonempty.law)
    -- (etcd-safe-main, 2026-11-25: hprem-axioms' swap; until then the premise `bootMarshal`)
    -- `proto.Marshal`'s spec at a boot conf change
    (wp_MarshalBoot : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG))
    -- (2026-11-25; until then the members' premise `bootPremise`) the interim axiom on `bootstrap` at
    -- `etcd_safe`'s shape
    (wp_bootstrap_dist : ∀ [π : Net.NetProtoGS] [MemStorReg GF],
      _root_.Perennial.EtcdGrove.bootstrap.specDist (GF := GF) (hG := hG)) :
    Member.spec (GF := GF) (hG := hG) := by
  intro CS π TB RB S5 peers clients ps ctxs boot i peersSl clientsSl Hfips Hblf Hbgo Hi64 HLv Haf
    Hbuq Hrf Hdbo Hms
  have Htb : threadBound GF ≤ 2 ^ 28 := TB.threadBound_le
  have Hrb48 : receiptBound GF ≤ 2 ^ 48 := Nat.le_trans RB.receiptBound_le (by decide)
  have HrbN : receiptBound GF ≤ 2 ^ 28 + 1 := Nat.le_trans RB.receiptBound_le (by decide)
  have HwbN : 2 ^ 28 + 7 + bootWB ≤ backend.wbInit := by unfold bootWB backend.wbInit; omega
  wp_start as ⟨Htok, Hp, Hc, Hvoff, Hwa, Hshare⟩
  try simp only [github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Token]
  ihave %Hpl := ownSlice_len $$ Hp
  ihave %Hcl := ownSlice_len $$ Hc
  imod ownSlice_persist _ _ _ $$ Hp with #Hp
  imod ownSlice_persist _ _ _ $$ Hc with #Hc
  have hplen : peers.length < 2 ^ 63 := by rw [Hpl.1]; word
  -- the imports' package facts
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  (try wp_auto)
  -- `i >= uint64(len(peers))`: return
  dcase
  rotate_left
  · (try wp_auto)
    iapply HΦ; itrivial
  have Hilt : i < peers.length := by
    have h := of_decide_eq_false Hd
    rw [Hpl.1]; word
  (try wp_auto)
  -- `!Valid(peers, clients)`: return
  wp_apply (wp_Valid peersSl clientsSl peers clients DFrac.discard DFrac.discard Hfips) $$ []
    as %b ⟨%Hb, -, -⟩
  · iframe #
  cases b
  · (try wp_auto)
    iapply HΦ; itrivial
  have Hcfg := Hb rfl
  -- the share of the start
  ihave Hshare := Hshare $$ %(And.intro Hcfg Hilt)
  icases Hshare with ⟨%c, Hshare⟩
  obtain ⟨Hne, Hlen, Hids⟩ := Hcfg
  obtain ⟨Hids1, Hids2⟩ := Hids
  obtain ⟨pi, hpi⟩ : ∃ p, peers[i]? = some p := ⟨_, List.getElem?_eq_getElem Hilt⟩
  obtain ⟨ci, hci⟩ : ∃ p, clients[i]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  iunfold memberShareK at Hshare
  icases Hshare with ⟨%Hsh, Hmss⟩
  obtain ⟨Hcok, Hand, Haok⟩ := Hsh
  obtain ⟨hvs, hrule, hboot, hc0, hch, hlog, hiss, hwn, hfs, hgen, hkc, hkr, hklg, hpo, hns, -⟩ := Hcok
  have hcm := cms_getD peers clients i pi ci hpi hci
  iunfold etcd_dist.memberStartShare at Hmss
  isimp only [hcm] at Hmss
  icases Hmss with ⟨#Hcf, #Hpaf, Hsl, #Hat⟩
  -- the configuration's pure facts
  obtain ⟨Hpfxnd, -, HidsLen⟩ := idPfxsOf_ok (idsOf peers) Hids1 Hids2
  have Hidnd : (idsOf peers).Nodup := by
    unfold idPfxsOf at Hpfxnd
    exact List.Pairwise.of_map _ (fun a b h e => h (by rw [e])) Hpfxnd
  have H0 : W64 0 ∉ idsOf peers := fun h => Hids2 _ h (by decide)
  have Hmlen : (membersOf peers clients).length = (idsOf peers).length := by
    rw [mOf_length]; simp [idsOf]
  have Hnd2 : (peers ++ clients).Nodup := Hand
  have Hpnd : peers.Nodup := (List.nodup_append.1 Hnd2).1
  have Haokp : ∀ a ∈ peers, Net.addrOk a = true := fun a ha => Haok a (List.mem_append_left _ ha)
  have Hnnd : ((membersOf peers clients).map (·.Name')).Nodup :=
    mOf_names_nodup peers clients (by omega)
  have Hdok : netDirOk (etcd_putgetN.dirN (membersOf peers clients) (idsOf peers)) :=
    etcd_putgetN.dirN_ok _ _ Hidnd H0 (by rw [mOf_peers]; exact Hpnd)
      (fun m hm => etcd_dist.addrOk_plainPeerURL (Haokp _ (mOf_peer_mem peers clients m hm)))
  have hmi := mOf_at peers clients i pi ci hpi hci
  have hidi := ids_at peers i pi hpi
  have Hdir : go!"http://" ++ pi ∈
      etcd_putgetN.dirN (membersOf peers clients) (idsOf peers) (memberIdOf pi) := by
    rw [etcd_putgetN.dirN_of_mem _ _ Hidnd ⟨nameOf i, pi, ci⟩ (memberIdOf pi) (zip_mem_of hmi hidi)]
    simp
  have Hbc : rafthttp.bootCfg (etcd_putgetN.dirN (membersOf peers clients) (idsOf peers)) ps :=
    rafthttp.bootCfg_of_le _ ps
      (fun f => by rw [etcd_putgetN.dirN_ne_nil _ _ Hmlen Hidnd, Hblf.perm.mem_iff])
      (by rw [Hblf.perm.length_eq]; unfold peersMax; omega)
  have hblen : boot.length = (idsOf peers).length := by rw [Hblf.boot.1, Hblf.perm.length_eq]
  have Hbl : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen]; omega
  have Hx : xsOf ((cmsOf (membersOf peers clients) (idsOf peers)).map (·.id)) c.idx
      (idPfxOf (W16 (uint.Z (memberIdOf pi)))) = (c.idx (memberIdOf pi)).slog := by
    rw [cms_ids]; exact xsOf_at _ _ Hpfxnd _ (List.mem_of_getElem? hidi)
  -- `proto.Marshal`'s bytes at the bootstrap log's conf changes, from its trust-boundary spec and the
  -- log's bytes (`Hblf.wire`), as putgetN's
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hmarsh := bootMarshal_of_spec wp_MarshalBoot _ _ _ Hblf.wire $$ Hpp
  -- the member's bootstrap contract, given the round tripper's, from the interim axiom (`BootDist.lean`) and
  -- what Go computes at its URLs (`Hbgo`)
  ihave #Pesrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  haveI : ThreadBoundLe GF (2 ^ 29) := ⟨Nat.le_trans TB.threadBound_le (by decide)⟩
  haveI : ReceiptBoundLe GF (2 ^ 60) := ⟨Nat.le_trans RB.receiptBound_le (by decide)⟩
  obtain ⟨Hidr, HU⟩ := Hbgo ⟨nameOf i, pi, ci⟩ (memberIdOf pi) (zip_mem_of hmi hidi)
  ihave #Hbp := etcd_dist.bootPremiseDist_of_specDist wp_bootstrap_dist (2 ^ 28) ps
      (LogEntry.toEntries boot 0) ctxs (etcd_putgetN.dirN (membersOf peers clients) (idsOf peers)) token
      (nameOf i) (urlsN (membersOf peers clients) ⟨nameOf i, pi, ci⟩) (memberIdOf pi) Hfips Hidr HU
      ⟨boot, Hblf.boot, rfl⟩ $$ Pesrv
  -- the member's peer address and every other peer's
  ihave #Hown : S5.httpAddrAt pi $$ []
  · iapply (peerFact_of (G := hG.goose_globalGS) S5 (cmsOf (membersOf peers clients) (idsOf peers)) pi
      (by rw [cms_peers peers clients]; exact List.mem_of_getElem? hpi))
    iexact Hpaf
  ihave #Hoth : □ ∀ (pid : w64) (a : GoString), ⌜pid ∈ ps ∧ pid ≠ memberIdOf pi ∧
      go!"http://" ++ a ∈ etcd_putgetN.dirN (membersOf peers clients) (idsOf peers) pid⌝ -∗
      S5.httpAddrAt a $$ []
  · imodintro
    iintro %pid %a %ha
    iapply (peerFact_of (G := hG.goose_globalGS) S5 (cmsOf (membersOf peers clients) (idsOf peers)) a
      (by rw [cms_peers peers clients]; exact mOf_peers peers clients ▸
        etcd_putgetN.dirN_host (membersOf peers clients) (idsOf peers) pid a ha.2.2))
    iexact Hpaf
  -- the member's `memberBoot`, from its slice
  have γm : mvcc.api.MvccName := Classical.choice hne.1
  imod (etcdstart.memberBoot_of_slice c.γ ps ctxs (LogEntry.toEntries boot 0) (c.reg (memberIdOf pi))
      c.issued c.cnt c.wn c.fs c.gen c.γk (fun _ => srvFloorFacts (GF := GF) (c.idx (memberIdOf pi)).slog)
      (memberIdOf pi) γm (c.idx (memberIdOf pi)) (c.cok (memberIdOf pi)) (c.rev (memberIdOf pi))
      (xsOf ((cmsOf (membersOf peers clients) (idsOf peers)).map (·.id)) c.idx
        (idPfxOf (W16 (uint.Z (memberIdOf pi)))))
      Hx hiss hwn hfs hgen hc0 hch hlog hvs false hkc .none lease.runCfg_none hklg (fun h => nomatch h)
      hpo rfl hns) $$ Hmarsh Hcf Hsl with ⟨%ρ, %Hρ, Hmb⟩
  have Hcg : kvCongr ρ.rd.kv c.view.kv := Hρ.2.2.2.2.2
  -- the initial cluster's map
  irename i => Hiv
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs) as %pm Hpm
  (try wp_auto)
  ihave HI : (∃ (k : w64) (jv : w64) (M : GMap GoString GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "j" ∷ j_ptr ↦ jv ∗ "Hpm" ∷ pm ↦$ M ∗
      "#Hsls" ∷ □ ([∗map] n ↦ sl ∈ M, sl ↦*□ iuOf (membersOf peers clients) n) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z peersSl.len ∧
        ∀ n, (M.lookup n).isSome ↔ n ∈ (List.range (sint.nat k)).map nameOf⌝ : IProp GF)
      $$ [i j Hpm]
  · iexists W64 0, _, ∅
    iframe
    isplitl
    · iintro !>
      iapply BigSepM.bigSepM_empty.2; itrivial
    ipureintro
    refine ⟨by word, by word, fun n => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp
  wp_for HI
  dcase
  rotate_left
  · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z peersSl.len := ⟨Hk.1, of_decide_eq_true Hd⟩
    have hkn : sint.nat k < peers.length := by rw [Hpl.1]; word
    obtain ⟨pk, hpk⟩ : ∃ x, peers[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem hkn⟩
    have hnew : (M.lookup (nameOf (sint.nat k))).isSome = false := by
      rw [Bool.eq_false_iff]; intro h
      obtain ⟨j', hj', he⟩ := List.mem_map.1 ((Hk.2.2 _).1 h)
      have hj'' := List.mem_range.1 hj'
      have := nameOf_inj (by omega) (by omega) he
      omega
    (try wp_auto)
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z k) peers _ pk Hb.1 $$ [] as -
    · iframe #; ipureintro; exact hpk
    (try wp_auto)
    try simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z k) peers _ pk Hb.1 $$ [] as -
    · iframe #; ipureintro; exact hpk
    (try wp_auto)
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %peer ⟨Hpeer, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    imod ownSlice_persist _ _ _ $$ Hpeer with #Hpeer
    (try wp_auto)
    wp_apply wp_Name
    have hku : uint.nat k = sint.nat k := by word
    rw [hku]
    (try wp_auto)
    wp_apply wp_mapInsert $$ Hpm as Hpm
    (try wp_auto)
    wp_for_post
    iframe
    iexists k + W64 1, k, _
    iframe
    isplitl
    · iintro !>
      iapply (BigSepM.bigSepM_insert (by
        rw [gmap_get?_eq]; cases hl : M.lookup (nameOf (sint.nat k)) <;> simp_all)).2
      isplitr
      · iExactEq Hpeer
        rw [iuOf_at peers clients Hnnd (sint.nat k) pk hpk]
        rfl
      iexact Hsls
    ipureintro
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    refine ⟨by word, by word, fun n => ?_⟩
    rw [hk1, List.range_succ, List.map_append, List.mem_append, GMap.lookup_insert_is_Some, ← Hk.2.2 n]
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    constructor
    · rintro (rfl | ⟨-, h⟩)
      · exact Or.inr rfl
      · exact Or.inl h
    · rintro (h | rfl)
      · by_cases he : nameOf (sint.nat k) = n
        · exact Or.inl he
        · exact Or.inr ⟨he, h⟩
      · exact Or.inl rfl
  -- the map built: every member's name, its one peer URL
  have Hif' : ¬ sint.Z k < sint.Z peersSl.len := of_decide_eq_false Hd
  have hkl : sint.nat k = peers.length := by rw [Hpl.1]; word
  have Hdom : ∀ n, (M.lookup n).isSome ↔ n ∈ (membersOf peers clients).map (·.Name') := by
    intro n
    rw [Hk.2.2 n, mOf_names, hkl]
  have hutf : ∀ n, (M.lookup n).isSome → utf8Valid n := by
    intro n hn
    have h := (Hdom n).1 hn
    rw [mOf_names] at h
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
    exact nameOf_utf8 j
  (try wp_auto)
  -- `StartMember(Name(i), cluster[Name(i)], peers[i], clients[i], cluster, Token, zap.NewNop())`
  have hiu : uint.nat (W64 i) = i := by word
  wp_apply wp_Name
  try rw [hiu]
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  (try wp_auto)
  try (wp_apply wp_Name; try rw [hiu]; (try wp_auto))
  have hnmem : nameOf i ∈ (membersOf peers clients).map (·.Name') := by
    rw [mOf_names]; exact List.mem_map_of_mem (List.mem_range.2 Hilt)
  obtain ⟨sl, hsl⟩ : ∃ sl, M.lookup (nameOf i) = some sl :=
    Option.isSome_iff_exists.1 ((Hdom _).2 hnmem)
  have hsl' : (M !! nameOf i) = some sl := hsl
  ihave #Hpeer := (BigSepM.bigSepM_lookup (Φ := fun k sl => iprop(sl ↦*□ iuOf (membersOf peers clients) k))
    hsl') $$ Hsls
  rw [iuOf_at peers clients Hnnd i pi hpi]
  wp_apply (wp_map_lookup1 go.string go_etcd_io.etcd.client.pkg.v3.types.URLs.ty pm M (nameOf i)
    DFrac.discard) $$ Hpm as -
  simp only [hsl', Option.getD_some]
  (try wp_auto)
  have hsi : sint.nat (W64 i) = i := by word
  have Hbi : 0 ≤ sint.Z (W64 i) ∧ sint.Z (W64 i) < sint.Z peersSl.len := by
    constructor <;> word
  have Hbc' : 0 ≤ sint.Z (W64 i) ∧ sint.Z (W64 i) < sint.Z clientsSl.len := by
    have := Hcl.1
    constructor <;> word
  try simp only [Hbi, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 i)) peers _ pi Hbi.1 $$ [] as -
  · iframe #; ipureintro
    show peers[sint.nat (W64 i)]? = some pi
    rw [hsi]; exact hpi
  (try wp_auto)
  try simp only [Hbc', _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 i)) clients _ ci Hbc'.1 $$ [] as -
  · iframe #; ipureintro
    show clients[sint.nat (W64 i)]? = some ci
    rw [hsi]; exact hci
  try simp only [github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Token]
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  wp_apply (wp_StartMember_dist S5 (2 ^ 28) (nameOf i) pi ci token sl pm lg M
      (iuOf (membersOf peers clients)) (urlsN (membersOf peers clients) ⟨nameOf i, pi, ci⟩) ps
      (LogEntry.toEntries boot 0) ctxs (etcd_putgetN.dirN (membersOf peers clients) (idsOf peers))
      (memberIdOf pi) { c.γ with reg := c.reg (memberIdOf pi) } ρ
      (etcdstart.env₀ γm (c.idx (memberIdOf pi)) (c.rev (memberIdOf pi)) (srvApi.kvNx ρ.rd false) false)
      (fun _ => srvFloorFacts (GF := GF) (c.idx (memberIdOf pi)).slog) .none
      Htb Hrb48 HrbN HwbN hvs hrule hboot Hbl Hdok Hdir Hbc ⟨rfl, rfl, Hdom, rfl⟩ hutf (nameOf_len i)
      Haf Hbuq Hdbo) $$ [Htok Hmb Hvoff Hwa] as %s %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, %γn, Hup⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    (try wp_auto)
    iapply HΦ; itrivial
  subst Herr
  (try wp_auto)
  -- `Serve(s, clients[i])` on a member machine (`Serve_dist`)
  try simp only [Hbc', _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 i)) clients _ ci Hbc'.1 $$ [] as -
  · iframe #; ipureintro
    show clients[sint.nat (W64 i)]? = some ci
    rw [hsi]; exact hci
  (try wp_auto)
  wp_apply (wp_Serve_dist s ci ρ
      (etcdstart.env₀ γm (c.idx (memberIdOf pi)) (c.rev (memberIdOf pi)) (srvApi.kvNx ρ.rd false) false)
      lg γn (memberIdOf pi) c.view) $$ [Hup] as %serr -
  · iframe; iframe #
    ipureintro; exact ⟨Hms, Hbuq, Hrf, HLv, Hcg⟩
  cases serr with
  | ok ei =>
    (try wp_auto)
    iapply HΦ; itrivial
  | nil =>
  (try wp_auto)
  -- `holdForever()`: it does not return
  wp_apply wp_holdForever as HF
  iexfalso
  iexact HF

end proof

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
