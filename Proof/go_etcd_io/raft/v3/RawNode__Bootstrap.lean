/- Lean-first (no Rocq counterpart). See `Spec/go_etcd_io/raft/v3/RawNode__Bootstrap.lean`. -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Bootstrap
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__Enum
public import Spec.go_etcd_io.raft.v3.raftpb.EntryType__Enum
public import Spec.go_etcd_io.raft.v3.raftLog__append
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Proof.go_etcd_io.raft.v3.LemmasMiscR
public import Proof.go_etcd_io.raft.v3.TracedUntraced
public import Proof.go_etcd_io.raft.v3.TracedHooks
public import Proof.go_etcd_io.raft.v3.TracedNodeBoot
public import Proof.go_etcd_io.raft.v3.TracedHooksGlobal
public import Proof.go_etcd_io.raft.v3.TracedFamilies
public import Proof.go_etcd_io.raft.v3.LemmasSnapCfg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (2026-11-12, trace-check step 5) **The end of a traced bootstrap**: the capability at the last
bootstrap event (position `|ps| + 3`) mints the completion witness (`trCapB_bootDone`, amendment A8.2:
the last point where the capability's `Λ` records it), then becomes the node's trace capability
(`rnTrace`): re-keyed to the struct's configuration, its phase the idle relation at the bootstrapped
state (`simIdle_boot`), any last event; with the scope's facts, the check-quorum field and the storage's
no-compaction (`TrNoSnap` at the fresh base). -/
private theorem boot_rnTrace (γ : RaftNames) (γd : GName) (r : Loc) (id : w64) (si : GoInterfaceOk)
    (ps : List w64) (es : List EntryM) (sF : NState) (cF : CfgM)
    (htr : sF.gh.tr = some γd) (hid : id ∈ ps) (hnd : ps.Nodup)
    (hpv : sF.prevote = false) (hlrn : cF.learners = ∅) (hinc : (elements cF.incoming).Perm ps)
    (hout : cF.outgoing = ∅) (hal : cF.autoLeave = false)
    (hsc : TrScope sF) (hboot : ∀ e ∈ γ.reBoot, IsConfEnt e)
    (hterm : sF.term = W64 1) (hrole : sF.role = .follower) (hvote : sF.vote = W64 0)
    (hlead : sF.lead = W64 0) (hprev : sF.logst.prev = entryID.mk (W64 0) (W64 0))
    (hlog : sF.logst.sents ++ sF.logst.uents = es) (hlen : es.length = ps.length)
    (hlt : (ps.length : Int) < 2 ^ 61) (hcom : sF.logst.committed = W64 (ps.length : Int))
    (hob : sF.outbox = []) (hwf : PlogWf (entryID.mk (W64 0) (W64 0)) es)
    (hones : ∀ e ∈ es, e.Term' = W64 1) (hst : sF.logst.storage = interface.ok si) :
    (r.[raft, go!"checkQuorum"] ↦□ false ∗ trNoCut (some γd) (interface.ok si) ∗
        trCapB (some γd) γ r id (bootCfg ps) false (bootPhase ps id) (bootAt ps id (ps.length + 3)) :
        IProp GF) ⊢
      |={⊤}=> bootDoneG (some γd) id ∗ rnTrace γ r id cF [] sF := by
  iintro ⟨#Hcq, #Hnc, Hcap⟩
  imod trCapB_bootDone γd γ r id (bootCfg ps) (bootPhase ps id) (bootAt ps id (ps.length + 3)) ⊤
      CoPset.subseteq_top
      (fun C cs P o hP ho => by
        obtain ⟨rfl, -, -⟩ := hP
        obtain ⟨x, rfl, hx⟩ := ho
        exact ⟨x, rfl, hx⟩)
    $$ Hcap with ⟨Hcap, %tn, #Hdir, #Hbd⟩
  imodintro
  isplitr
  · unfold bootDoneG; iexists tn; iframe Hdir Hbd
  ihave Hcap := trCapB_cfg γd γ r id (bootCfg ps) cF false _ _
    (fun C hC _ _ => ⟨hinc.trans ((perm_elements_listToSet ps hnd).trans hC), hout⟩) $$ Hcap
  ihave Hcap := trCapB_mono (some γd) γ r id cF false (bootPhase ps id) (fun C => SimIdle C sF) _
    (fun C cs P hP => by
      obtain ⟨rfl, rfl, rfl⟩ := hP
      exact simIdle_boot C id hid sF es hterm hrole hvote hlead hprev hlog hlen hlt hcom hob hwf hones)
    $$ Hcap
  ihave Hcap := trCapB_monoΛ (some γd) γ r id cF false (fun C => SimIdle C sF) _ (fun _ => True)
    (fun _ _ => trivial) $$ Hcap
  unfold rnTrace
  rw [htr]
  isplitr
  · ipureintro; exact ⟨hpv, hlrn⟩
  isplitr
  · ipureintro
    exact ⟨hsc, (fun m hm => by rw [hob] at hm; cases hm), hal, hboot, (fun h => absurd hrole h)⟩
  iframe Hcq
  isplitr
  · rw [← htr]
    iapply trNoCut_trNoSnap _ _ (by rw [hprev]; rfl)
    rw [hst, htr]; iexact Hnc
  iexists false
  isplitr
  · ipureintro; intro h; exact absurd rfl h
  rw [← htr]
  iExactEq Hcap; rw [htr]

-- (2026-10-19, D21 M3) past the default budget with the no-snapshot facts of `ownRaftPhys`
set_option maxHeartbeats 1600000 in
theorem RawNode.Bootstrap.wp_proof
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (wp_ConfChangeType_Enum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG))
    (wp_EntryType_Enum : raftpb.EntryType.Enum.spec (GF := GF) (hG := hG))
    (wp_raftLog_append : raftLog.append.spec (GF := GF) (hG := hG))
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    RawNode.Bootstrap.spec (GF := GF) (hG := hG) := by
  intro γ md rn r id si sdr pre s peers dq pv ps ctxs bootLog R1 R2 R3 R4 R5 R6 R7 R8 R9 Rns Hgtr0
    Htrsc
  wp_start as ⟨Hfresh, Hpeers, #Hctx, #Hmarshal, Hghost, #Hcommitted, #Hcl, Hcap, #Hnc⟩
  iunfold rawNodeFresh at Hfresh
  icases Hfresh with ⟨%rnv, %sv, %hprev, Hfresh⟩
  iNamed Hfresh
  subst Hr
  -- (step 5) the check-quorum field (for the trace capability's scope)
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  icases ownRaftPhysC_cq _ _ _ $$ Hphys with ⟨#Hcqf, Hphys⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  -- (2026-11-12, trace-check step 5) the capability after `newRaft`'s lines, at the node's mode
  ihave Hcap : trCapB (GF := GF) s.gh.tr γ rnv.raft' id (bootCfg ps) false (bootPhase ps id)
      (bootAt ps id 2) $$ [Hcap]
  · rw [Hgtr0]; iexact Hcap
  obtain ⟨Hp, Hse, Hue, Hsd, Hcm0, Hap0, Hapg0, Hun, Hsn, Hsg, Hdtk0'⟩ := Hlog
  obtain ⟨Ht0, Hv0, Hr, Ho, Hrst, Hrpd⟩ := Hterm0
  ihave %Hplen := ownSlice_len $$ Hpeers
  have Hpslen : ps.length = pv.length := by rw [R1, List.length_map]
  obtain ⟨HbLen, HbBnd, HbEnt⟩ := R9
  have Hpv62 : (pv.length : Int) ≤ 2 ^ 62 := by rw [← Hpslen]; exact R5
  wp_auto
  -- `len(peers) == 0`: dead
  wp_if_destruct
  · exfalso
    apply R2
    rw [R1]
    apply List.map_eq_nil_iff.2
    apply List.eq_nil_of_length_eq_zero
    have := Hplen.1; rw [this]; word
  -- `rn.raft.raftLog.storage.LastIndex()`: the storage is empty, so `0`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same _ _ _ s $$ Hphys with ⟨Hlog, Hlogback⟩
  iNamed Hlog
  wp_auto
  ihave #Hsto : isStorageWith (ownStorage s.logst.sn lv.storage') (storCut lv.storage')
      (svCert s.logst.sn) lv.storage' $$ [HisStorage]
  · unfold isStorageD; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  rw [Hstok]
  wp_auto
  have Hpnil : σ.pend = [] := by rw [Hpend.1]; exact Hun
  take_storage Hsn
  wp_apply HLastIndex $$ [$HStorage] as %li ⟨%Hli, HStorage⟩
  · ipureintro; exact Hpnil
  rw [← Hstok]
  try wp_auto
  ihave Hlog : ownRaftLog s.log s.logst $$ [Hl HStorage Huents Huents_cap]
  · reseal_raftLog
  ihave Hphys := Hlogback $$ Hlog
  have Hli0 : li = W64 0 := by
    obtain ⟨Hsp, -, Hsents⟩ : LogStoreOk none σ s.logst.prev s.logst.sents s.logst.uents :=
      Hsn ▸ Hstore
    have Hse' := Hsents Hue
    rw [Hsp, Hp, ← Hse', Hse] at Hli
    simp at Hli
    word
  subst Hli0
  wp_auto
  -- `rn.prevHardSt = emptyState`
  ihave Hinit := isInitialized_access $$ Hpkg
  ihave ⟨%es, #Hg, #Hesz⟩ := emptyState_hsRO $$ Hinit
  wp_auto
  -- `rn.raft.becomeFollower(1, None)`
  -- (step 5) position 3 of the bootstrap: a bootstrap `BecomeFollower` line (`b = false`)
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  have Hdom0 : domSet s.progress \ (∅ : GSet w64) = ∅ := by
    rw [Hdom]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_difference]
    exact ⟨fun h => h.1, fun h => absurd h (GMap.not_elem_of_empty _)⟩
  ihave Hphys : ownRaftPhysCV (GF := GF) (CfgM.simple ∅ ∅) (CfgM.simple ∅ ∅).voters rnv.raft' id s $$ [Hphys]
  · iExactEq Hphys; rw [Hdom0]
  have Hel0 : (elements (CfgM.simple (∅ : GSet w64) ∅).incoming).length ≤
      (elements (bootCfg ps).incoming).length := by
    show (elements (∅ : GSet w64)).length ≤ _
    rw [show elements (∅ : GSet w64) = [] from
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])]
    exact Nat.zero_le _
  have Hbf3 : ∀ e, NodeEvOf (W64 2) id (becomeFollower s (W64 1) (W64 0)) (CfgM.simple ∅ ∅) e →
      TraceSim.BootEvAt ps id 3 e := fun e he => (nodeEvOf_bootEvAtBF _ _ _ _ _ he).2 rfl
  have Hpl3 : uint.nat (plastIndex (toPState (becomeFollower s (W64 1) (W64 0)))) < 2 ^ 40 := by
    show uint.nat (W64 (uint.Z s.logst.prev.index' + ((s.logst.sents ++ s.logst.uents).length : Int))) < _
    rw [Hp, Hse, Hue]; simp only [List.append_nil, List.length_nil]; word
  wp_apply (raft.becomeFollower.traced wp_raft_becomeFollower (CfgM.simple ∅ ∅)
      (V := (CfgM.simple ∅ ∅).voters) (bootCfg ps) rnv.raft' id s (W64 1) (W64 0) γ false
      (bootPhase ps id) (bootPhase ps id) (bootAt ps id 2) (bootAt ps id 3) (by rw [Ht0]; word)
      (fun _ => rfl) (fun h => by cases h) (fun _ => rfl) (fun h => by cases h)
      (fun _ C cs P hP => ⟨hP, fun _ e he o ho => by
        obtain ⟨rfl, -, -⟩ := hP
        obtain ⟨x, rfl, hx⟩ := ho
        exact TraceSim.bootNext_some C id x e 2 hx (Hbf3 e he)⟩)
      (fun e he => ⟨e, rfl, Hbf3 e he⟩)
      (fun _ => ⟨(fun h => by cases h), fun _ e he => nodeEvOf_okBoot _ _ _ _ e _ he
          (by show uint.nat (W64 1) < 2 ^ 61; decide)
          (by show uint.nat s.logst.committed < 2 ^ 61; rw [Hcm0]; decide) Hpl3 Hel0⟩))
    $$ [$Hphys $Hcap] as %pvs1 ⟨Hphys, Hcap⟩
  · cases s.gh.tr <;> (simp only [trOwn]; try iempintro)
  ihave Hphys : ownRaftPhysC (GF := GF) (CfgM.simple ∅ (domSet ({ becomeFollower s (W64 1) (W64 0) with prvals := pvs1 } : NState).progress \ ∅)) rnv.raft' id { becomeFollower s (W64 1) (W64 0) with prvals := pvs1 } $$ [Hphys]
  · have Hc0 : CfgM.simple (∅ : GSet w64)
        (domSet ({ becomeFollower s (W64 1) (W64 0) with prvals := pvs1 } : NState).progress \ ∅) =
        CfgM.simple ∅ ∅ := by
      show CfgM.simple ∅ (domSet s.progress \ ∅) = _; rw [Hdom0]
    rw [Hc0]; iexact Hphys
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  -- the state after `becomeFollower(1, None)`, as a variable (`s1`): term `1`, no vote, no leader
  generalize Hs1 : ({ becomeFollower s (W64 1) (W64 0) with prvals := pvs1 } : NState) = s1
  have Hs1f : s1.term = W64 1 ∧ s1.vote = W64 0 ∧ s1.lead = W64 0 ∧ s1.role = .follower ∧
      s1.votes = ∅ ∧ s1.outbox = s.outbox ∧ s1.logst = s.logst ∧ s1.log = s.log ∧ s1.gh = s.gh ∧
      s1.prevote = s.prevote ∧ s1.sdr = s.sdr ∧ s1.rd.states = s.rd.states ∧
      s1.rd.pend = s.rd.pend ∧ s1.stepfn = stepFuncOf .follower ∧ s1.ticking = true := by
    rw [← Hs1]
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    show (if W64 1 = s.term then s.vote else W64 0) = W64 0
    rw [Ht0]; exact ite_eq_right (by decide)
  obtain ⟨Hs1t, Hs1v, Hs1l, Hs1r, Hs1vs, Hs1o, Hs1ls, Hs1lg, Hs1gh, Hs1pv, Hs1sdr, Hs1rs, Hs1rp,
    Hs1sf, Hs1tk⟩ := Hs1f
  -- `ents := make([]*pb.Entry, len(peers))`
  wp_apply wp_slice_make2 (V := Loc) peers.len as %ents ⟨Hents, Hents_cap⟩
  · ipureintro; exact Hplen.2
  try wp_auto
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Hi
  -- the first loop: entry `k` built from peer `k` (`ConfChange` marshalled, `Entry` at term `1`,
  -- index `k + 1`), stored at `ents[k]`; after `n` iterations the first `n` boot entries
  iunfold peersCtx at Hctx
  ihave %Hctxlen := BigSepL2.bigSepL2_length $$ Hctx
  ihave IH : iprop(∃ (n : w64) (lc : List Loc) (x : w64) (pr : Peer),
      "i" ∷ i_ptr ↦ n ∗
      "Hi" ∷ igo ↦ x ∗
      "peer" ∷ peer_ptr ↦ pr ∗
      "Hents" ∷ ents ↦* (lc ++ List.replicate (pv.length - sint.nat n) (zero_val Loc)) ∗
      "#Hlc" ∷ ([∗list] l;e ∈ lc;bootLog.take (sint.nat n), entRO l e) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (pv.length : Int) ∧ lc.length = sint.nat n⌝)
    $$ [i Hi peer Hents]
  · iexists W64 0, [], _, _
    simp only [named]
    iframe i Hi peer
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.nil_append, Nat.sub_zero,
      Hplen.1]
    iframe Hents
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for IH
  wp_if_destruct
  · -- iteration `n`: `peer := peers[n]`
    have Hlt : sint.nat n < pv.length := by word
    obtain ⟨p, Hpn⟩ : ∃ p, pv[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z peers.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index peers (sint.Z n) _ dq p Hn.1 $$ [Hpeers] as Hpeers
    · iframe; ipureintro; exact Hpn
    try wp_auto
    -- the peer's conf change: `&pb.ConfChange{Type: AddNode.Enum(), NodeId: new(peer.ID),
    -- Context: peer.Context}`, owned (`ownConfChange`)
    obtain ⟨ctx, Hcn⟩ : ∃ ctx, ctxs[sint.nat n]? = some ctx :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hctxlen]; exact Hlt)⟩
    ihave #Hpctx := BigSepL2.bigSepL2_lookup (Φ := fun _ (p : Peer) ctx => (p.Context' ↦*□ ctx : IProp GF))
      Hpn Hcn $$ Hctx
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_ConfChangeType_Enum (W32 0) as %pty Hpty
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hpty with #cTy
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$v1» with #cN
    -- the conf change as built (`bootConfChange`: `Type` and `NodeId` set, `Id` unset, no
    -- unknown fields), which `bootMarshal` is stated over (premise fixes 1)
    imod bootConfChange_of_struct «$r0_ptr» (⟨zero_val _, pty, «$v1_ptr», p.Context', null, slice.nil, 0⟩ : raftpb.ConfChange)
        ⟨W32 0, p.ID', ctx, W64 0⟩ ⊤ rfl rfl $$ [«$r0»] with Hcc
    · iframe «$r0» cTy cN Hpctx
    -- `proto.Marshal(cc)`: the boot entry's bytes (`bootMarshal`)
    obtain ⟨e, Hen⟩ : ∃ e, bootLog[sint.nat n]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [HbLen, Hpslen]; exact Hlt)⟩
    have Hpsn : ps[sint.nat n]? = some p.ID' := by
      rw [R1, List.getElem?_map, Hpn]; rfl
    obtain ⟨HeT, HeI, HeY, -, -⟩ := HbEnt _ _ Hen
    have Hpure : ps[sint.nat n]? = some (⟨W32 0, p.ID', ctx, W64 0⟩ : ConfChangeM).nodeId ∧
        ctxs[sint.nat n]? = some (⟨W32 0, p.ID', ctx, W64 0⟩ : ConfChangeM).context ∧
        bootLog[sint.nat n]? = some e ∧ (⟨W32 0, p.ID', ctx, W64 0⟩ : ConfChangeM).type = W32 0 ∧
        (⟨W32 0, p.ID', ctx, W64 0⟩ : ConfChangeM).id = W64 0 := ⟨Hpsn, Hcn, Hen, rfl, rfl⟩
    iunfold bootMarshal at Hmarshal
    icases Hmarshal with ⟨-, #Hmarshal'⟩
    ihave #Hmk := Hmarshal' $$ %(sint.nat n) %«$r0_ptr» %(DFrac.own 1) %(⟨W32 0, p.ID', ctx, W64 0⟩ : ConfChangeM)
      %e %Hpure
    wp_apply Hmk $$ [$Hcc] as %d Hcc Hd
    try wp_auto
    -- the boot entry: `&pb.Entry{Type: EntryConfChange.Enum(), Term: new(1), Index: new(i + 1),
    -- Data: data}`, read-only (`entRO`)
    wp_apply wp_EntryType_Enum (W32 1) as %pety Hpety
    imod cellRO_alloc $$ Hpety with #cY
    imod cellRO_alloc $$ «$v1» with #cT
    imod cellRO_alloc $$ «$v2» with #cI
    imod ownSlice_persist $$ Hd with #Hd
    imod entOwn_of_struct «$r0_ptr» (⟨zero_val _, «$v1_ptr», «$v2_ptr», pety, d, slice.nil, 0⟩ : raftpb.Entry)
        e ⊤ rfl $$ [«$r0»] with He
    · have HeI' : e.Index' = n + W64 1 := by word
      iframe «$r0» Hd
      rw [HeT, HeY, HeI']
      iframe cT cY cI
    imod entOwn_freeze $$ He with #He
    -- `ents[i] = &pb.Entry{...}`
    ihave %Hentsl := ownSlice_len $$ Hents
    simp only [List.length_append, List.length_replicate] at Hentsl
    have Hnn : (sint.nat n : Int) = sint.Z n := Int.toNat_of_nonneg Hn.1
    have Hesn : (sint.nat ents.len : Int) = sint.Z ents.len := Int.toNat_of_nonneg Hentsl.2
    have Hlc := Hn.2.2
    have Hbndc : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ents.len := ⟨Hn.1, by
      have h1 := Hentsl.1; omega⟩
    try wp_auto
    simp only [Hbndc, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index ents (sint.Z n) _ «$r0_ptr» $$ [Hents] as Hents
    · iframe; ipureintro
      simp only [List.length_append, List.length_replicate]; omega
    have Hset : (lc ++ List.replicate (pv.length - sint.nat n) (zero_val Loc)).set (sint.Z n).toNat «$r0_ptr»
        = (lc ++ [«$r0_ptr»]) ++ List.replicate (pv.length - (sint.nat n + 1)) (zero_val Loc) := by
      rw [show (sint.Z n).toNat = lc.length by omega]
      rw [List.set_append_right _ _ (by omega), Nat.sub_self]
      obtain ⟨k, hk⟩ : ∃ k, pv.length - sint.nat n = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      rw [hk, List.replicate_succ, List.set_cons_zero, List.append_assoc, List.singleton_append]
      rw [show pv.length - (sint.nat n + 1) = k by omega]
    rw [Hset]
    wp_for_post
    iframe
    iexists n + W64 1, lc ++ [«$r0_ptr»], _, _
    simp only [named]
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    iframe i Hi peer Hents
    isplitr
    · rw [List.take_succ, Hen, show (some e).toList = [e] from rfl]
      iapply entsBig_app lc [«$r0_ptr»] (List.take (sint.nat n) bootLog) [e] $$ [$Hlc]
      iapply BigSepL2.bigSepL2_singleton.2
      iexact He
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [List.length_append, List.length_singleton, Hn.2.2]
  -- the loop's exit: `ents` holds the boot entries
  have Hnlen : sint.nat n = pv.length := by word
  have Hrep : lc ++ List.replicate (pv.length - sint.nat n) (zero_val Loc) = lc := by
    rw [Hnlen, Nat.sub_self, List.replicate_zero, List.append_nil]
  have Htake : List.take (sint.nat n) bootLog = bootLog := by
    rw [Hnlen, ← Hpslen, ← HbLen]; exact List.take_length
  ihave Hes : entsPts ents (DFrac.own 1) bootLog $$ [Hents]
  · iunfold entsPts
    iexists lc
    isplitl [Hents]
    · iExactEq Hents; rw [Hrep]
    · iExactEq Hlc; rw [Htake]
  -- `rn.raft.raftLog.append(ents...)`: the boot entries join the (empty) log, unstable
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_at ∅ _ id _ $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
  have Hidx1 : ∀ e0, bootLog[0]? = some e0 →
      (uint.Z s.logst.committed < uint.Z e0.Index' ∧
        uint.Z e0.Index' ≤ uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
          + (s.logst.uents.length : Int) + 1) ∧
      (∀ (k : Nat) e, bootLog[k]? = some e → uint.Z e.Index' = uint.Z e0.Index' + (k : Int)) ∧
      uint.Z e0.Index' + (bootLog.length : Int) < 2 ^ 64 := by
    intro e0 He0
    obtain ⟨-, HI0, -, -, -⟩ := HbEnt _ _ He0
    rw [Hcm0, Hp, Hse, Hue]
    refine ⟨⟨by word, by word⟩, ?_, by word⟩
    intro k e He
    obtain ⟨-, HIk, -, -, -⟩ := HbEnt _ _ He
    omega
  have Hfirst : ∀ e0, bootLog[0]? = some e0 →
      uint.Z e0.Index' = uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
        + (s.logst.uents.length : Int) + 1 := by
    intro e0 He0
    obtain ⟨h1, h2⟩ := (Hidx1 e0 He0).1
    clear Hidx1
    have z0 : uint.Z (W64 0) = 0 := by first | rfl | decide | simp
    rw [Hcm0, z0] at h1
    rw [Hp, Hse, Hue] at h2
    rw [Hp, Hse, Hue]
    dsimp only at h2 ⊢
    rw [z0] at h2 ⊢
    simp only [List.length_nil] at h2 ⊢
    omega
  have Hcont := logTruncateAppend_cont s.logst bootLog Hfirst
  wp_apply wp_raftLog_append s1.log s1.logst bootLog ents (DFrac.own 1) (by rw [Hs1ls]; exact Hidx1)
    $$ [$Hlog $Hes] as %li ⟨Hlog, Hes, %Hpost⟩
  · rw [Hs1ls, Hcont.2]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  ihave Hes : entsPts ents (DFrac.own 1) bootLog $$ [Hes]
  · iExactEq Hes; rw [Hs1ls, Hcont.2]; simp only [Bool.false_eq_true, ↓reduceIte]
  ihave Hlog : ownRaftLog s1.log (logAppend s.logst bootLog) $$ [Hlog]
  · iExactEq Hlog; rw [Hs1ls, Hcont.1]
  ihave Hphys := Hlogback $$ %(logAppend s.logst bootLog) Hlog
    %(⟨⟨(by intro h; rw [Hs1gh, Hgh] at h; cases h),
        (by have h := Hgh0.1.2.1; rw [Hs1ls] at h; exact h.of_fields rfl rfl rfl rfl rfl (Int.le_refl _)),
        (by have h := Hgh0.1.2.2; rw [Hs1ls] at h; exact h)⟩,
      (by intro h; rw [Hs1gh, Hgh] at h; cases h), (by rw [Hs1ls]; rfl)⟩)
    %(by intro h; rw [Hs1r] at h; cases h)
  generalize Hs2 : ({ s1 with logst := logAppend s.logst bootLog } : NState) = s2
  have Hs2ls : s2.logst = logAppend s.logst bootLog := by rw [← Hs2]
  have Hs2lg : s2.log = s1.log := by rw [← Hs2]
  -- `rn.raft.raftLog.committed = uint64(len(ents))`: the raw store (D12), the entries committed
  -- although unstable
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_at ∅ _ id _ $$ Hphys with ⟨Hlog, %Hgh1, Hlogback⟩
  ihave %Hesl := entsPts_len $$ Hes
  have Hlen' : uint.Z ents.len = (bootLog.length : Int) := by word
  have Hlenw : ents.len = W64 bootLog.length := by word
  wp_apply (ownRaftLog_setCommitted s2.log s2.logst ents.len
      (by rw [Hs2ls]; simp only [logAppend, Hp]; word)
      (by rw [Hs2ls]; simp only [logAppend, Hp, Hse, Hue, List.nil_append]; word)
      (by rw [Hs2ls]; simp only [logAppend, Hapg0]; word)
      (by rw [Hs2ls]; simp only [logAppend, Hcm0]; word))
    $$ [$Hlog] as Hlog
  ihave Hphys := Hlogback $$ %_ Hlog
    %(LogGhOk.of_fields Hgh1 rfl rfl rfl rfl rfl
      (hcm := by simp only; rw [Hs2ls]; simp only [logAppend, Hcm0]; word))
    %(by intro h; rw [← Hs2] at h; exact absurd h (by rw [Hs1r]; decide))
  generalize Hs3 : ({ s2 with logst := { s2.logst with committed := ents.len } } : NState) = s3
  have Hs3pr : s3.progress = s.progress := by rw [← Hs3, ← Hs2, ← Hs1]; rfl
  have Hs3r : s3.role = .follower := by rw [← Hs3, ← Hs2]; exact Hs1r
  -- (step 5) the bootstrap `ApplyConfChange` lines' numbers (term `1`, the bootstrap log committed)
  have Hs3t : s3.term = W64 1 := by rw [← Hs3, ← Hs2]; exact Hs1t
  have Hs3v : s3.vote = W64 0 := by rw [← Hs3, ← Hs2]; exact Hs1v
  have Hs3gh : s3.gh = s.gh := by rw [← Hs3, ← Hs2]; exact Hs1gh
  have Hs3c : s3.logst.committed = W64 (ps.length : Int) := by
    rw [← Hs3]; show ents.len = _; rw [Hlenw, HbLen]
  have Hs3pl : plastIndex (toPState s3) = W64 (ps.length : Int) := by
    rw [← Hs3, ← Hs2]
    show W64 (uint.Z s.logst.prev.index' + ((s.logst.sents ++ (s.logst.uents ++ bootLog)).length : Int)) = _
    rw [Hp, Hse, Hue, List.nil_append, List.nil_append, HbLen]
    show W64 (uint.Z (W64 0) + (ps.length : Int)) = _
    rw [show uint.Z (W64 0) = 0 from rfl, Int.zero_add]
  try wp_auto
  -- the second loop: `applyConfChange(AddNode peer)` per peer, at a follower: the voters so far
  -- (`CfgM.simple (listToSet (ps.take k)) ∅`), the state but for the progress map, the `Progress`
  -- values and `isLearner` unchanged
  have Hd3 : domSet s3.progress \ (∅ : GSet w64) = ∅ := by
    rw [Hs3pr, Hdom]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_difference]
    exact ⟨fun h => h.1, fun h => absurd h (GMap.not_elem_of_empty _)⟩
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  ihave IH2 : iprop(∃ (k : w64) (pr : Peer) (sk : NState),
      "i" ∷ i_ptr ↦ k ∗
      "peer" ∷ peer_ptr ↦ pr ∗
      "Hphys" ∷ ownRaftPhysC (CfgM.simple (GMap.listToSet (ps.take (sint.nat k))) ∅) rnv.raft' id sk ∗
      -- (step 5) the capability after the `k`-th peer's line (position `k + 3`)
      "Hcap" ∷ trCapB s.gh.tr γ rnv.raft' id (bootCfg ps) false (bootPhase ps id)
        (bootAt ps id (sint.nat k + 3)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (pv.length : Int) ∧
        ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress) (b : Bool),
          sk = { s3 with progress := prs, prvals := pvs, isLearner := b }⌝)
    $$ [i peer Hphys Hcap]
  · iexists W64 0, _, s3
    simp only [named]
    iframe i peer
    isplitl [Hphys]
    · iExactEq Hphys
      rw [Hd3, show sint.nat (W64 0) = 0 by rfl, List.take_zero, GMap.listToSet_nil]
    isplitl [Hcap]
    · iExactEq Hcap; rfl
    · ipureintro
      refine ⟨by word, by word, s3.progress, s3.prvals, s3.isLearner, rfl⟩
  -- (step 5) the end's ghost updates (`trCapB_bootDone`) after the loop: under an update
  iapply wp_fupd
  wp_for IH2
  wp_if_destruct
  · -- iteration `k`: `peer := peers[k]`
    have Hif' : sint.Z k < sint.Z peers.len := by
      first
        | exact Hif
        | (rcases Decidable.em (sint.Z k < sint.Z peers.len) with h | h
           · exact h
           · rw [decide_eq_false h] at Hif; exact absurd Hif false_neq_true)
    clear Hif
    obtain ⟨Hk1, Hk2, prs, pvs, b, Hsk⟩ := Hk
    have Hlt : sint.nat k < pv.length := by clear Hsk; word
    obtain ⟨p, Hpk⟩ : ∃ p, pv[sint.nat k]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hpsk : ps[sint.nat k]? = some p.ID' := by
      rw [R1, List.getElem?_map, Hpk]; rfl
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z peers.len := ⟨Hk1, Hif'⟩
    simp only [Hbnd', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index peers (sint.Z k) _ dq p Hk1 $$ [Hpeers] as Hpeers
    · iframe; ipureintro; exact Hpk
    try wp_auto
    -- `(&pb.ConfChange{NodeId: new(peer.ID), Type: AddNode.Enum()}).AsV2()`
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_ConfChangeType_Enum (W32 0) as %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    imod cellRO_alloc $$ «$v0» with #cN
    wp_alloc cc as Hcc
    imod ownConfChange_of_struct cc (⟨zero_val _, pty, «$v0_ptr», slice.nil, null, slice.nil, 0⟩ : raftpb.ConfChange)
        ⟨W32 0, p.ID', [], W64 0⟩ ⊤ rfl $$ [Hcc] with Hcc
    · iframe Hcc cTy cN
      isplitl []
      · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
      iapply ownSlice_nil
    wp_apply wp_ConfChange_AsV2 cc (DFrac.own 1) _ $$ [$Hcc] as %v ⟨-, Hcc2⟩
    -- `rn.raft.applyConfChange(cc)`: the peer joins the voters (`bootCC_apply`)
    have Hskr : sk.role = .follower := by rw [Hsk]; exact Hs3r
    have Hp0 : p.ID' ≠ W64 0 := by
      intro h; apply R4; rw [← h]
      exact (List.getElem?_eq_some_iff.1 Hpsk).2 ▸ List.getElem_mem _
    have Hids : (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅).cfg.ids
        = GMap.listToSet (ps.take (sint.nat k + 1)) := by
      rw [cfgState_ids, listToSet_take_succ ps (sint.nat k) p.ID' Hpsk]
    have Hsz : (GMap.size (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅).cfg.ids : Int)
        ≤ 2 ^ 62 := by
      rw [Hids, GMap.size_list_to_set _ (R3.sublist (List.take_sublist _ _))]
      have := List.length_take_le (sint.nat k + 1) ps
      omega
    -- (step 5) the `ApplyConfChange` line at position `k + 4`, through the bootstrap gate
    have Hskgh : sk.gh = s.gh := by rw [Hsk]; exact Hs3gh
    have Hskt : sk.term = W64 1 := by rw [Hsk]; exact Hs3t
    have Hskv : sk.vote = W64 0 := by rw [Hsk]; exact Hs3v
    have Hskc : sk.logst.committed = W64 (ps.length : Int) := by rw [Hsk]; exact Hs3c
    have Hskpl : plastIndex (toPState sk) = W64 (ps.length : Int) := by rw [Hsk]; exact Hs3pl
    have Hklt : sint.nat k < ps.length := by rw [Hpslen]; exact Hlt
    have Hinc1 : (elements (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅).cfg.incoming).Perm
        (ps.take (sint.nat k + 1)) := by
      show (elements (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k))))).Perm _
      rw [← listToSet_take_succ ps (sint.nat k) p.ID' Hpsk]
      exact (perm_elements_listToSet _ (R3.sublist (List.take_sublist _ _))).symm
    have HlenC : (elements (bootCfg ps).incoming).length = ps.length :=
      (perm_elements_listToSet ps R3).length_eq.symm
    have Hlen_k : (elements (CfgM.simple (GMap.listToSet (ps.take (sint.nat k))) ∅).incoming).length ≤
        (elements (bootCfg ps).incoming).length := by
      rw [HlenC]
      show (elements (GMap.listToSet (ps.take (sint.nat k)))).length ≤ _
      rw [← (perm_elements_listToSet _ (R3.sublist (List.take_sublist _ _))).length_eq,
        List.length_take]
      exact Nat.min_le_right _ _
    have Hlen_k1 : (elements (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅).cfg.incoming).length ≤
        (elements (bootCfg ps).incoming).length := by
      rw [HlenC, Hinc1.length_eq, List.length_take]; exact Nat.min_le_right _ _
    have HevK : ∀ e, CCEvOf id sk (CfgM.simple (GMap.listToSet (ps.take (sint.nat k))) ∅)
        (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅).cfg e →
        TraceSim.BootEvAt ps id (sint.nat k + 4) e := fun e he =>
      ccEvOf_bootEvAtK ps id sk _ _ e (sint.nat k) Hklt he Hskt Hskv Hskc Hskpl Hskr Hinc1
    icases ownRaftPhysC_traceLoggerG _ _ _ _ _ $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
    ihave Hcap : trCapB (GF := GF) sk.gh.tr γ rnv.raft' id (bootCfg ps) false (bootPhase ps id)
        (bootAt ps id (sint.nat k + 3)) $$ [Hcap]
    · rw [Hskgh]; iexact Hcap
    ihave Hgate := trCapB_hookGate_ccBoot sk.gh.tr γ rnv.raft' id
      (CfgM.simple (GMap.listToSet (ps.take (sint.nat k))) ∅)
      (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅).cfg (bootCfg ps) sk tl
      (bootPhase ps id) (bootAt ps id (sint.nat k + 3)) (bootAt ps id (sint.nat k + 4))
      (fun _ C cs P hP e he o ho => by
        obtain ⟨rfl, -, -⟩ := hP
        obtain ⟨x, rfl, hx⟩ := ho
        exact TraceSim.bootNext_some C id x e (sint.nat k + 3) hx (HevK e he))
      (fun e he => ⟨e, rfl, HevK e he⟩)
      (fun hsome e he => by
        have Hps40 : ps.length < 2 ^ 40 :=
          (Htrsc (fun hn => by
            have h0 : sk.gh.tr = none := by rw [Hskgh, Hgtr0]; exact hn
            rw [h0] at hsome; cases hsome)).2.2
        have h40 : uint.nat (W64 (ps.length : Int)) = ps.length := by word
        exact ccEvOf_okBoot _ _ _ _ e _ he
          (by rw [Hskt]; show uint.nat (W64 1) < 2 ^ 61; decide)
          (by rw [Hskc, h40]; unfold traceNumBound; omega)
          (by rw [Hskpl, h40]; exact Hps40)
          Hlen_k Hlen_k1)
      Htlok
      $$ [$Htl $Hcap]
    wp_apply wp_raft_applyConfChange (CfgM.simple (GMap.listToSet (ps.take (sint.nat k))) ∅) rnv.raft' id
        sk v _ (DFrac.own 1) (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅) _
        (bootCC_apply _ _ Hp0) Hsz (by intro h; rw [Hskr] at h; cases h)
        (by intro h; rcases h with h | h <;> rw [Hskr] at h <;> cases h)
        (by intro _ h; rw [Hskr] at h; cases h)
      (fun _ => Hskr) $$ [$Hphys $Hcc2 $Hgate] as %cs %xs %os %ls %lns %sk' ⟨Hphys, -, -, -, %Hok, Hcap⟩
    obtain ⟨prs', pvs', Hsk'⟩ := applyCCOkC_nonleader _ _ _ _ Hok (by rw [Hskr]; decide)
    wp_for_post
    iframe
    iexists k + W64 1, _, sk'
    simp only [named]
    iframe i peer
    isplitl [Hphys]
    · iExactEq Hphys
      rw [show sint.nat (k + W64 1) = sint.nat k + 1 by clear Hsk Hsk'; word,
        listToSet_take_succ ps (sint.nat k) p.ID' Hpsk, cfgM_eq_simple]
    isplitl [Hcap]
    · iExactEq Hcap
      rw [Hskgh, show sint.nat (k + W64 1) = sint.nat k + 1 by clear Hsk Hsk'; word]
    · ipureintro
      refine ⟨by clear Hsk Hsk'; word, by clear Hsk Hsk'; word, prs', pvs',
        learnerOfC (cfgState (<[p.ID' := ()]> (GMap.listToSet (ps.take (sint.nat k)))) ∅).cfg id, ?_⟩
      rw [Hsk', Hsk]
  -- the loop's exit: every peer a voter, `ownRaftPhys` at the cluster's configuration
  obtain ⟨Hk1, Hk2, prs, pvs, b, Hsk⟩ := Hk
  have Hklen : sint.nat k = pv.length := by clear Hsk Hs3t Hs3v Hs3gh Hs3c Hs3pl; word
  have Htakek : ps.take (sint.nat k) = ps := by
    rw [Hklen, ← Hpslen]; exact List.take_length
  ihave Hphys : ownRaftPhysC (CfgM.simple (GMap.listToSet ps) ∅) rnv.raft' id sk $$ [Hphys]
  · iExactEq Hphys; rw [Htakek]
  -- (D19p) the tracker holds the voters only
  icases ownRaftPhysC_dom _ rnv.raft' id sk $$ Hphys with ⟨%Hpd, Hphys⟩
  have Hsub : domSet sk.progress ⊆ γ.reCfg := by
    rw [R7, GMap.elem_of_subseteq]; intro k hk
    rcases (GMap.elem_of_union _ _ _).1 ((GMap.elem_of_subseteq _ _).1 Hpd k hk) with h | h
    · rw [CfgM.voters_simple] at h; exact h
    · simp only [CfgM.simple] at h; exact absurd h (GMap.not_elem_of_empty _)
  icases ownRaftPhysC_sdr _ rnv.raft' id sk $$ Hphys with ⟨#Hsd0, Hphys⟩
  ihave #Hsdrf : sdrOk (GF := GF) rnv.raft' md $$ []
  · iunfold sdrOk; iexists sk.sdr; iexact Hsd0
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  ihave Hphys : ownRaftPhys γ.reCfg rnv.raft' id sk $$ [Hphys]
  · rw [R7]; iexact Hphys
  -- the state: a follower at term `1`, the boot log committed -- `bootPState bootLog`
  have HN : sk.term = W64 1 ∧ sk.vote = W64 0 ∧ sk.lead = W64 0 ∧ sk.role = .follower ∧
      sk.votes = ∅ ∧ sk.outbox = [] ∧
      sk.logst = { logAppend s.logst bootLog with committed := ents.len } ∧ sk.gh = { sn := s.gh.sn, tr := s.gh.tr } ∧
      sk.prevote = pre ∧ sk.rd.states = [] ∧ sk.rd.pend = [] ∧
      sk.stepfn = stepFuncOf .follower ∧ sk.ticking = true := by
    rw [Hsk, ← Hs3, ← Hs2]
    refine ⟨Hs1t, Hs1v, Hs1l, Hs1r, Hs1vs, ?_, rfl, ?_, ?_, ?_, ?_, Hs1sf, Hs1tk⟩
    · show s1.outbox = []; rw [Hs1o, Ho]
    · show s1.gh = { sn := s.gh.sn, tr := s.gh.tr }; rw [Hs1gh]; exact Hgh
    · show s1.prevote = pre; rw [Hs1pv, Hpvoff]
    · show s1.rd.states = []; rw [Hs1rs, Hrst]
    · show s1.rd.pend = []; rw [Hs1rp, Hrpd]
  obtain ⟨HNt, HNv, HNl, HNr, HNvs, HNo, HNls, HNgh, HNpv, HNrs, HNrp, HNsf, HNtk⟩ := HN
  have HNrel : NStateRel sk (bootPState bootLog) :=
    boot_post_rel bootLog sk ⟨by rw [HNsf, HNr], HNtk⟩ HNt HNv HNl HNr HNvs HNo
      (by rw [HNls]; simp only [logAppend]; exact Hp)
      (by rw [HNls]; simp only [logAppend]; exact Hse)
      (by rw [HNls]; simp only [logAppend, Hue, List.nil_append])
      (by rw [HNls]; exact Hlenw) HNrs HNrp
  -- (step 5) the end of the bootstrap: the completion witness (`trCapB_bootDone`, the capability at
  -- the last bootstrap event) and the node's trace capability (`rnTrace`, `boot_rnTrace`)
  have Hdiff0 : domSet sk.progress \ γ.reCfg = ∅ := by
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_difference]
    constructor
    · rintro ⟨h1, h2⟩; exact absurd ((GMap.elem_of_subseteq _ _).1 Hsub k h1) h2
    · intro h; exact absurd h (GMap.not_elem_of_empty _)
  have HsFtr : ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).gh.tr = s.gh.tr := by
    show sk.gh.tr = _; rw [HNgh]
  ihave Hcap : trCapB (GF := GF) s.gh.tr γ rnv.raft' id (bootCfg ps) false (bootPhase ps id)
      (bootAt ps id (ps.length + 3)) $$ [Hcap]
  · iExactEq Hcap; rw [Hklen, ← Hpslen]
  ihave Hfin : |={⊤}=> (bootDoneG (GF := GF) γ.reTrace id ∗
      rnTrace γ rnv.raft' id (CfgM.simple γ.reCfg (domSet ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).progress \ γ.reCfg))
        [] ({ sk with gh := { sk.gh with tc := W64 1 } } : NState)) $$ [Hcap]
  · rw [← Hgtr0]
    rcases Option.eq_none_or_eq_some s.gh.tr with Htn | ⟨γd, Htn⟩
    · rw [Htn]
      imodintro
      isplitr
      · unfold bootDoneG; ipureintro; trivial
      iapply rnTrace_none
      exact HsFtr.trans Htn
    · rw [Htn]
      have Hsc := Htrsc (by rw [← Hgtr0, Htn]; simp)
      ihave Hcq0 : rnv.raft'.[raft, go!"checkQuorum"] ↦□ false $$ []
      · iExactEq Hcqf; rw [Hsc.2.1]
      ihave Hnc0 : trNoCut (GF := GF) (some γd) (interface.ok si) $$ []
      · iExactEq Hnc; first | rfl | rw [← Hgtr0, Htn]
      iapply boot_rnTrace γ γd rnv.raft' id si ps bootLog _ _ (HsFtr.trans Htn) R6 R3
        (by show sk.prevote = false; rw [HNpv]; exact Hsc.1)
        (by show domSet sk.progress \ γ.reCfg = ∅; exact Hdiff0)
        (by show (elements γ.reCfg).Perm ps; rw [R7]; exact (perm_elements_listToSet ps R3).symm)
        rfl rfl
        (by
          rw [Hsk, ← Hs3, ← Hs2, ← Hs1]
          exact ⟨rfl, rfl, Hrpd⟩)
        (fun e he => by
          rw [R8] at he
          obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
          exact Or.inl (HbEnt k e hk).2.2.1)
        HNt HNr HNv HNl
        (by show sk.logst.prev = _; rw [HNls]; exact Hp)
        (by show sk.logst.sents ++ sk.logst.uents = _; rw [HNls]; simp only [logAppend, Hse, Hue, List.nil_append])
        HbLen (by rw [← HbLen]; exact HbBnd)
        (by show sk.logst.committed = _; rw [HNls]; show ents.len = _; rw [Hlenw, HbLen])
        HNo ((BootLogOk.wf ⟨HbLen, HbBnd, HbEnt⟩ R3).wf)
        (fun e he => by
          obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
          exact (HbEnt k e hk).1)
        (by show sk.logst.storage = _; rw [HNls]; exact Hsg)
      iframe Hcq0 Hnc0 Hcap
  imod Hfin with ⟨#Hbd, Hrntr⟩
  ihave Hrntr : rnTrace (GF := GF) γ ({ rnv with prevHardSt' := es } : RawNode).raft' id
      (CfgM.simple γ.reCfg (domSet ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).progress \ γ.reCfg))
      [] ({ sk with gh := { sk.gh with tc := W64 1 } } : NState) $$ [Hrntr]
  · iExactEq Hrntr; rfl
  ihave #Hcomm0 := isCommitted_mono γ [] bootLog List.nil_prefix $$ Hcommitted
  try wp_auto
  -- (2026-10-17) the term ceiling at the term
  ihave Hphys := ownRaftPhys_raise_tc _ rnv.raft' id sk (W64 1)
    (by rw [HNgh]; show (0 : Int) ≤ _; decide) $$ Hphys
  -- (D19i part 1) the floor at most `applying`, which is `applied` (`0`)
  icases ownRaftPhys_log_at _ rnv.raft' id _ $$ Hphys with ⟨HL, %Hgh0, Hlogback⟩
  icases ownRaftLog_fl _ _ $$ HL with ⟨%Hflk, HL⟩
  ihave Hphys := Hlogback $$ %_ HL %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
    %(fun _ => logLast_le_of_fields rfl rfl rfl)
  have Haa : ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).logst.applied =
      ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).logst.applying := by
    simp only; rw [HNls]; simp only [logAppend, Hap0, Hapg0]
  have HrnflB : ∀ rs0 : RNState, rs0.steps = [] →
      RNFl rs0 { sk with gh := { sk.gh with tc := W64 1 } } := fun rs0 _ =>
    ⟨fun _ => by rw [Haa]; exact Hflk.1, fun h => absurd h (by rw [Haa]; exact Int.lt_irrefl _)⟩
  -- (raft-final phase 2) the node is outside the no-snapshot mode (`NsCap`: `NGhost.ns` off), and
  -- so is the cluster (the spec's premise): `NsLink`
  have Hns : γ.reNoSnap = false := Rns
  have Hdtk0 : s.logst.dtk = 0 := Hdtk0'
  have Hsn0 : s.gh.sn = s.logst.sn := by
    have h := Hgh0.1.2.2
    simp only at h
    rw [HNls, HNgh] at h
    simp only [logAppend] at h
    exact h.symm
  have Hnl0 : NsLink γ ({ sk with gh := { sk.gh with tc := W64 1 } } : NState) :=
    ⟨by show sk.gh.ns = γ.reNoSnap; rw [HNgh, Hns], by show sk.gh.tr = γ.reTrace; rw [HNgh]; exact Hgtr0,
      fun m hm => absurd hm (by show m ∉ sk.outbox; rw [HNo]; exact List.not_mem_nil)⟩
  have HpS : toPState ({ sk with gh := { sk.gh with tc := W64 1 } } : NState) = bootPState bootLog := HNrel.1
  have Hlead0 : (toPState ({ sk with gh := { sk.gh with tc := W64 1 } } : NState)).lead = W64 0 := by
    rw [HpS]; rfl
  ihave #Hlw : leadW (GF := GF) γ id (toPState ({ sk with gh := { sk.gh with tc := W64 1 } } : NState)) $$ []
  · iapply leadW_none; exact Hlead0
  ihave #Hxw : xfW (GF := GF) γ ({ sk with gh := { sk.gh with tc := W64 1 } } : NState) $$ []
  · iunfold xfW
    rw [show ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).gh.xw = ∅ by
      show sk.gh.xw = ∅; rw [HNgh]]
    iapply BigSepM.bigSepM_empty.2; iempintro
  ihave #Hcl' : certLink (GF := GF) γ ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).gh.sn $$ []
  · rw [show ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).gh.sn = s.gh.sn by
      show sk.gh.sn = s.gh.sn; rw [HNgh]]
    iexact Hcl
  -- (D22l) `prevHardSt` the zero record, `RNState.phs`'s default
  ihave #Hes' := prevHS_of_zero γ _ _ rfl $$ Hesz
  imodintro
  iapply HΦ
  isplitl []
  · ipureintro; rfl
  isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hrntr]
  · cases md with
    | static =>
      iunfold bootInit at Hghost
      ihave %Hst0 := ownRaftGhost_static γ id _ $$ Hghost
      ihave Hphys := ownRaftPhys_toC' $$ Hphys
      icases ownRaftPhysC_persistCut _ _ id _ $$ Hphys with ⟨%Hpcut, Hphys⟩
      -- (raft-final phase 2) the ghost part built here (`ownRawNode_intro_static` takes no leader
      -- witness): at no leader and no transfer record
      ihave Hghost : ownStepGhost γ
          (RNMode.toG .static ⟨0, cfgState (GMap.listToSet ps) ∅, [], ∅⟩)
          (CfgM.simple γ.reCfg (domSet ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).progress \ γ.reCfg))
          id ({ sk with gh := { sk.gh with tc := W64 1 } } : NState) $$ [Hghost]
      · simp only [RNMode.toG, ownStepGhost, ghostRest, ghostRestM, GMode.isDyn]
        iframe Hcl' Hlw Hxw
        isplitl [Hghost]
        · rw [HpS]; iexact Hghost
        ipureintro
        exact ⟨Hnl0, CfgStatic.simple γ _ Hst0,
          TrackedOk.of_sub Hsub (by rw [R7]; exact (GMap.elem_of_list_to_set _ _).2 R6)⟩
      iapply ownRawNode_intro_tr γ rn id
          { delivered := [], unpersisted := [], steps := [], term := W64 1,
            storage := interface.ok si, sn := s.gh.sn, mode := RNMode.static,
            cfg := cfgState (GMap.listToSet ps) ∅, tc := W64 1 }
          ({ sk with gh := { sk.gh with tc := W64 1 } } : NState) _ [] ({ rnv with prevHardSt' := es } : RawNode) sv
          (HardStateM.mk (W64 0) (W64 0) (W64 0)) [] HNrel.2
          (fun _ => by rw [R7]; exact (GMap.elem_of_list_to_set _ _).2 R6) Hasync
          (by rw [HNls]; simp only [logAppend, Hapg0]; rfl)
          (by rw [HNls]; simp only [logAppend, Hun])
          (fun _ => by rw [HNls]; simp only [logAppend, Hsn]) trivial
          (by simp only; rw [HNt]) (by simp only; rw [HNls]; simp only [logAppend, Hsg]; exact ⟨trivial, Hsn0⟩)
          ⟨fun h => (by cases h), rfl, by simp only; rw [HNt]; exact Int.le_refl _,
            fun h => (by simp only at h; rw [HNr] at h; cases h),
            fun h => (h (by rw [HNls]; simp only [logAppend, Hsn])).elim⟩
          (by simp only; rw [HNgh]) (by simp only; rw [HNgh]) (uint_Z_nonneg _) (HrnflB _ rfl)
          -- (D22 S-d3a) no snapshot lent
          ⟨by simp only; rw [HNgh]; rfl, fun _ => ⟨by simp only; rw [HNgh], fun _ _ _ _ h => (by cases h)⟩,
            fun l h => (by cases h),
            -- (2026-11-02, stage II (u)) the configuration index `0`, no snapshot (`CapOk`)
            ⟨by simp only [Int.natCast_zero]; exact uint_Z_nonneg _, fun l h => (by cases h),
              fun _ p hp => by rw [HNls] at hp; simp [logAppend, Hsn] at hp⟩⟩
          (SdtTie.of_none (by rw [HNls]; simp only [logAppend, Hsn]; exact Hdtk0))
        -- (durability stage II, G2) a fresh node's recorded role: `NewRawNode`'s follower
        (by exact Hsvr.1.symm)
        -- (2026-11-01, durability stage II (m)) `prevHardSt`'s record the zero hard state
        (PhsOk.zero rfl rfl (by rw [HNls]; simp only [logAppend, Hsn]) Hpcut)
        (by show sk.gh.tr = γ.reTrace; rw [HNgh]; exact Hgtr0)
        (by show sk.gh.lq = []; rw [HNgh])
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hes' Hsteps Hsteps_cap [] Hcomm0 [] [] [] [] Hrntr
      · iapply pendList_nil
      · iapply ackInv_none; intro _ _ _ _ h; cases h
      · ipureintro; trivial
      · first | (rw [HNls]; simp only [logAppend, Hsn]) | (simp only; rw [HNls]; simp only [logAppend, Hsn])
        iapply snapLocOk_none
      · -- (durability stage II, G2) a fresh node's durable state's tie (`durTie_fresh`)
        iapply durTie_fresh γ _ _ rfl
        · show sk.logst.prev = _; rw [HNls]; exact Hp
        · show sk.logst.stored = _; rw [HNls]; exact Hsd
    | dyn dec c0 h0 h1 =>
      -- (2026-10-25, T-M M2a) the dynamic mode: the ghost state at `rboot c0 bootLog`, the
      -- configuration index `0`, the configuration the peers' (`ownRaftPhysC` at it, as
      -- `RestartNode`'s dynamic case)
      iunfold bootInit at Hghost
      icases Hghost with ⟨%HD, Hgr⟩
      obtain ⟨HD, rfl⟩ := HD
      ihave Hphys := ownRaftPhys_toC' $$ Hphys
      icases ownRaftPhysC_persistCut _ _ id _ $$ Hphys with ⟨%Hpcut, Hphys⟩
      have Hro : rOf ({ sk with gh := { sk.gh with tc := W64 1 } } : NState) ⟨0, cfgState (GMap.listToSet ps) ∅, [], ∅⟩ =
          rboot (cfgState (GMap.listToSet ps) ∅) bootLog := by
        have HpS : toPState ({ sk with gh := { sk.gh with tc := W64 1 } } : NState) = bootPState bootLog := HNrel.1
        unfold rOf rboot pciR
        rw [HpS]
        simp only; rw [HNls]
        simp [logAppend, Hap0, Hsn, HNr]
      have Hdiff : domSet ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).progress \ γ.reCfg = ∅ := by
        apply GMap.set_eq; intro k
        rw [GMap.elem_of_difference]
        constructor
        · rintro ⟨h1, h2⟩; exact absurd ((GMap.elem_of_subseteq _ _).1 Hsub k h1) h2
        · intro h; exact absurd h (GMap.not_elem_of_empty _)
      ihave Hghost : ownStepGhost γ
          (RNMode.toG (.dyn dec (cfgState (GMap.listToSet ps) ∅) h0 h1)
            ⟨0, cfgState (GMap.listToSet ps) ∅, [], ∅⟩)
          (CfgM.simple γ.reCfg (domSet ({ sk with gh := { sk.gh with tc := W64 1 } } : NState).progress \ γ.reCfg)) id ({ sk with gh := { sk.gh with tc := W64 1 } } : NState) $$ [Hgr]
      · simp only [RNMode.toG]
        iapply (ownStepGhost_dyn γ dec _ h0 _ _ id ({ sk with gh := { sk.gh with tc := W64 1 } } : NState)).2
        rw [Hro, effDec_empty]
        iframe Hgr
        isplitr
        · ipureintro
          refine ⟨HD, ?_, Hnl0⟩
          rw [Hdiff, R7]; rfl
        isplitr; · iapply decLb_empty
        iframe Hcl' Hlw Hxw
      iapply ownRawNode_intro_tr γ rn id
          { delivered := [], unpersisted := [], steps := [], term := W64 1,
            storage := interface.ok si, sn := s.gh.sn, mode := .dyn dec (cfgState (GMap.listToSet ps) ∅) h0 h1,
            cfg := cfgState (GMap.listToSet ps) ∅, tc := W64 1 }
          ({ sk with gh := { sk.gh with tc := W64 1 } } : NState) _ [] ({ rnv with prevHardSt' := es } : RawNode) sv
          (HardStateM.mk (W64 0) (W64 0) (W64 0)) [] HNrel.2 (fun h => by cases h) Hasync
          (by rw [HNls]; simp only [logAppend, Hapg0]; rfl)
          (by rw [HNls]; simp only [logAppend, Hun])
          (fun _ => by rw [HNls]; simp only [logAppend, Hsn]) trivial
          (by simp only; rw [HNt]) (by simp only; rw [HNls]; simp only [logAppend, Hsg]; exact ⟨trivial, Hsn0⟩)
          ⟨fun _ _ h => (by simp only at h; rw [HNr] at h; cases h), rfl, by simp only; rw [HNt]; exact Int.le_refl _,
            fun h => (by simp only at h; rw [HNr] at h; cases h),
            fun h => (h (by rw [HNls]; simp only [logAppend, Hsn])).elim⟩
          (by simp only; rw [HNgh]) (by simp only; rw [HNgh]) (uint_Z_nonneg _) (HrnflB _ rfl)
          -- (D22 S-d3a) no snapshot lent
          ⟨by simp only; rw [HNgh]; rfl, fun _ => ⟨by simp only; rw [HNgh], fun _ _ _ _ h => (by cases h)⟩,
            fun l h => (by cases h),
            -- (2026-11-02, stage II (u)) the configuration index `0`, no snapshot (`CapOk`)
            ⟨by simp only [Int.natCast_zero]; exact uint_Z_nonneg _, fun l h => (by cases h),
              fun _ p hp => by rw [HNls] at hp; simp [logAppend, Hsn] at hp⟩⟩
          (SdtTie.of_none (by rw [HNls]; simp only [logAppend, Hsn]; exact Hdtk0))
        -- (durability stage II, G2) a fresh node's recorded role: `NewRawNode`'s follower
        (by exact Hsvr.1.symm)
        -- (2026-11-01, durability stage II (m)) `prevHardSt`'s record the zero hard state
        (PhsOk.zero rfl rfl (by rw [HNls]; simp only [logAppend, Hsn]) Hpcut)
        (by show sk.gh.tr = γ.reTrace; rw [HNgh]; exact Hgtr0)
        (by show sk.gh.lq = []; rw [HNgh])
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hes' Hsteps Hsteps_cap [] Hcomm0 [] [] [] [] Hrntr
      · iapply pendList_nil
      · iapply ackInv_none; intro _ _ _ _ h; cases h
      · ipureintro; trivial
      · first | (rw [HNls]; simp only [logAppend, Hsn]) | (simp only; rw [HNls]; simp only [logAppend, Hsn])
        iapply snapLocOk_none
      · -- (durability stage II, G2) a fresh node's durable state's tie (`durTie_fresh`)
        iapply durTie_fresh γ _ _ rfl
        · show sk.logst.prev = _; rw [HNls]; exact Hp
        · show sk.logst.stored = _; rw [HNls]; exact Hsd
  · iframe Hpeers Hbd

end proof

end EtcdGrove
end Perennial
