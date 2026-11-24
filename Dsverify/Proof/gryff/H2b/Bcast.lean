/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2b/Bcast.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2b: the broadcasts of the EPaxos normal path and the replies

`bcastPreAccept`, `bcastAccept`, `bcastCommit` (a message to each peer in `PreferredPeerOrder`'s
order, through the package global `pa` / `ea` / `ec`, owned by `epaxosRest`), the `reply*`
wrappers (`SendMsg` with the handler's rpc code), `fastPathQuorum`.

In a section with one `HeapGS` (H2-R0).
-/
module

public import Dsverify.Proof.gryff.H2.Env
public import Dsverify.Proof.gryff.Replica.Base
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2.h2b

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.replica2
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A broadcast from replica `k`: to `k + 1`, then `k + 2` (mod 3). (H3's `bcast_eq`.) -/
theorem bcast_eq' (s : RState) (k : Fin 3) (hid : s.id = rid32 k) (m : Msg) :
    model.bcast s m = some [.send (k + 1) m, .send (k + 2) m] := by
  have h0 : sint.Z (0 : w32) = 0 := rfl
  have h1 : sint.Z (1 : w32) = 1 := rfl
  have h2 : sint.Z (2 : w32) = 2 := rfl
  have hid' : s.id = BitVec.ofNat 32 k.val := by rw [hid]; rfl
  set_option linter.unusedSimpArgs false in
  rcases k with ⟨_ | _ | _ | n, hk⟩
  all_goals first | omega | (simp [model.bcast, model.peerOrder, model.sendPeer, model.sendTo,
    model.dstOf, hid', h0, h1, h2] <;> rfl)

/-- `PreferredPeerOrder[j]` (`[(k+1)%3, (k+2)%3, k]`, N-9) is peer `qf` (`j ≤ 1`). -/
theorem ppo_elem (k : Fin 3) (j : Nat) (hj : j ≤ 1) :
    ∃ qf : Fin 3, ([W32 (((k.val : Int) + 1) % 3), W32 (((k.val : Int) + 2) % 3), rid32 k] :
        List w32)[j]? =
        some (rid32 qf) ∧ qf ≠ k ∧ qf = k + (1 + ⟨j, by omega⟩) ∧
      sint.Z (rid32 qf) = qf.val := by
  refine ⟨k + (1 + ⟨j, by omega⟩), ?_, ?_, rfl, ?_⟩ <;>
  rcases k with ⟨_ | _ | _ | _, hk⟩ <;> (obtain rfl | rfl : j = 0 ∨ j = 1 := by omega) <;>
    first | omega | decide +revert

theorem fin3_add (k : Fin 3) :
    k + (1 + ⟨0, by omega⟩) = k + 1 ∧ k + (1 + ⟨1, by omega⟩) = k + 2 := by
  revert k; decide

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- What the broadcasts and replies read (persistent). -/
abbrev bcFixed (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) : IProp GF :=
  iprop(h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗ gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
    □ h2Fixed k gR h ∗ □ genericOk γ ρ k r gR h)

theorem cmdsRep_open (sl : GoSlice) (cs : List Cmd) :
    cmdsRep (GF := GF) sl cs ⊣⊢ ∃ gs : List src.state.Command, sl ↦*□ gs ∗
      ⌜gs.map cmdOf = cs ∧ model.cmdsOk cs⌝ := by
  unfold cmdsRep; exact .rfl

instance cmdsRep_persistent (sl : GoSlice) (cs : List Cmd) : Persistent (cmdsRep sl cs : IProp GF) := by
  unfold cmdsRep; infer_instance

/-- `epaxosRest`'s global `pa`, taken out. -/
theorem epaxosRest_pa (h : Loc) :
    epaxosRest (GF := GF) h ⊢ ∃ v : src.gryffproto.PreAccept, globalAddr src.gryff.pa ↦ v ∗
      (∀ v' : src.gryffproto.PreAccept, globalAddr src.gryff.pa ↦ v' -∗ epaxosRest h) := by
  unfold epaxosRest
  iintro ⟨%ms, %lcp, %lci, %cS, %cs, %mskR, %msk, H1, H2, H3, H4, H5, H6, H7, H8, ⟨%v, Hpa⟩, Hr⟩
  iexists v
  iframe Hpa
  iintro %v' Hpa
  iexists ms, lcp, lci, cS, cs, mskR, msk
  iframe

/-- `epaxosRest`'s global `ea`, taken out. -/
theorem epaxosRest_ea (h : Loc) :
    epaxosRest (GF := GF) h ⊢ ∃ v : src.gryffproto.EAccept, globalAddr src.gryff.ea ↦ v ∗
      (∀ v' : src.gryffproto.EAccept, globalAddr src.gryff.ea ↦ v' -∗ epaxosRest h) := by
  unfold epaxosRest
  iintro ⟨%ms, %lcp, %lci, %cS, %cs, %mskR, %msk, H1, H2, H3, H4, H5, H6, H7, H8, H9,
    ⟨%v, Hea⟩, Hr⟩
  iexists v
  iframe Hea
  iintro %v' Hea
  iexists ms, lcp, lci, cS, cs, mskR, msk
  iframe

/-- `epaxosRest`'s globals `ec` and `ecs`, taken out. -/
theorem epaxosRest_ec (h : Loc) :
    epaxosRest (GF := GF) h ⊢ ∃ (v : src.gryffproto.ECommit) (w : src.epaxosproto.CommitShort),
      globalAddr src.gryff.ec ↦ v ∗ globalAddr src.gryff.ecs ↦ w ∗
      (∀ (v' : src.gryffproto.ECommit) (w' : src.epaxosproto.CommitShort),
        globalAddr src.gryff.ec ↦ v' -∗ globalAddr src.gryff.ecs ↦ w' -∗ epaxosRest h) := by
  unfold epaxosRest
  iintro ⟨%ms, %lcp, %lci, %cS, %cs, %mskR, %msk, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10,
    ⟨%v, Hec⟩, ⟨%w, Hecs⟩, Hr⟩
  iexists v, w
  iframe Hec Hecs
  iintro %v' %w' Hec Hecs
  iexists ms, lcp, lci, cS, cs, mskR, msk
  iframe

theorem bcastPreAccept_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (s : RState) (q i b seq : w32) (sl : GoSlice) (cmds : List Cmd)
    (deps : GoArray w32 5) (base : src.gryffproto.ValTag) (outs rest : List Out)
    (hid : s.id = rid32 k)
    (hb : model.bcastPreAccept s q i b cmds seq (depsOf deps) (vtOf base) = some outs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ bcFixed γ ρ k r gR h ∗
        epaxosRest h ∗ cmdsRep sl cmds ∗ pendingOuts γ ρ k r t (outs ++ rest) }}
      (App (App (App (App (App (App (App (Val (h @!! go.GoType.PointerType
        src.gryff.EPaxosRMWHandler.ty @!! go!"bcastPreAccept")) (Val #q)) (Val #i)) (Val #b))
        (Val #sl)) (Val #seq)) (Val #deps)) (Val #base))
    {{ RET #(); epaxosRest h ∗ pendingOuts γ ρ k r t rest }} := by
  wp_start as ⟨⟨#HR, #HgR, #Hid, #HN, #Hfix, #Hok⟩, Hrest, #Hcmds, Hpend⟩
  iunfold h2Fixed at Hfix
  icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    #HThr, #HExec, #HPO, #HPOS, #HPAL, #HPALS, %HPAl, #HSt, #HStOk, #Hbo,
    #HcPA, #HcPAc, #Hrc⟩
  -- `Alive` (N1-3): the lock's network side
  icases pendingOuts_alive γ ρ k r gR t _ $$ [$HgR $Hpend] with ⟨Hpend, Hal⟩
  iunfold aliveAt at Hal
  icases Hal with ⟨%aS, #HAl, #HAlS⟩
  icases epaxosRest_pa h $$ Hrest with ⟨%v, Hpa, Hrestc⟩
  wp_apply wp_with_defer_recover
  iintro %defer %pnc Hdefer Hpnc
  wp_auto
  dsimp only
  -- the message, as `msgAt`
  icases (cmdsRep_open ..).1 $$ Hcmds with ⟨%gs, #Hgs, %Hgsc⟩
  obtain ⟨Hgsc, -⟩ := Hgsc
  have ho := bcast_eq' s k hid (.preAccept ⟨s.id, q, i, b, cmds, seq, depsOf deps, vtOf base⟩)
  simp only [model.bcastPreAccept] at hb
  rw [hb, Option.some.injEq] at ho
  subst ho
  generalize hM : (Msg.preAccept ⟨s.id, q, i, b, cmds, seq, depsOf deps, vtOf base⟩) = M
  ihave Hm : msgAt (globalAddr src.gryff.pa) M $$ [Hpa]
  · subst hM
    unfold msgAt
    iexists ⟨rid32 k, q, i, b, gs, seq, deps, base⟩, sl
    simp only [wire.gryffproto.PreAccept.goVal]
    iframe Hpa Hgs
    ipureintro; simp only [preAcceptOf, hid, Hgsc]
  ihave HI : (∃ j : Nat, "%Hj" ∷ ⌜j ≤ 1⌝ ∗ "sent" ∷ sent_ptr ↦ W64 (j : Int) ∗
      "q" ∷ q_ptr ↦ W64 (j : Int) ∗ "Hm" ∷ msgAt (globalAddr src.gryff.pa) M ∗
      "Hpend" ∷ pendingOuts γ ρ k r t
        (([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop j ++ rest) : IProp GF)
    $$ [sent q Hm Hpend]
  · iexists 0
    rw [List.drop_zero]
    iframe
    ipureintro; omega
  irename «instance» => Hinst
  wp_for HI
  wp_if_destruct
  · ihave %HPOl := ownSlice_len _ _ _ $$ HPOS
    ihave %HAll := ownSlice_len _ _ _ $$ HAlS
    ihave %HPALl := ownSlice_len _ _ _ $$ HPALS
    have hjw : sint.Z (W64 (j : Int)) = j := by word
    obtain ⟨qf, hqel, hqk, hqv⟩ := ppo_elem k j Hj
    have hPOl : sint.Z pS.len = 3 := by
      have h1 := HPOl.1; have h2 := HPOl.2
      simp only [List.length_cons, List.length_nil, sint.nat, sint.Z] at h1 h2 ⊢; omega
    have hAll : sint.Z aS.len = 3 := by
      have h1 := HAll.1; have h2 := HAll.2
      simp only [aliveList, List.length_cons, List.length_nil, sint.nat, sint.Z] at h1 h2 ⊢; omega
    have hPALl : sint.Z alS.len = 3 := by
      have h1 := HPALl.1; have h2 := HPALl.2
      simp only [HPAl, sint.nat, sint.Z] at h1 h2 ⊢; omega
    rw [hjw, ite_eq_left (show 0 ≤ (j : Int) ∧ (j : Int) < sint.Z pS.len by omega)]
    wp_apply wp_load_slice_index pS (j : Int) _ DFrac.discard _ (by omega) $$ [HPOS] as -
    · iframe HPOS; ipureintro; exact hqel
    have hqw : sint.Z (W64 (sint.Z (rid32 qf))) = (qf.val : Int) := by
      rw [hqv.2]; have := qf.isLt; word
    have hb1 : 0 ≤ (j : Int) ∧ (j : Int) < sint.Z pS.len := by omega
    have hb2 : 0 ≤ (qf.val : Int) ∧ (qf.val : Int) < sint.Z aS.len := by have := qf.isLt; omega
    have hb3 : 0 ≤ (qf.val : Int) ∧ (qf.val : Int) < sint.Z alS.len := by have := qf.isLt; omega
    simp only [hqw, ite_eq_left hb2]
    wp_apply wp_load_slice_index aS (qf.val : Int) _ DFrac.discard true (by omega) $$ [HAlS] as -
    · iframe HAlS; ipureintro; simpa [hqk] using aliveList_get k qf
    simp only [hjw, ite_eq_left hb1]
    wp_apply wp_load_slice_index pS (j : Int) _ DFrac.discard _ (by omega) $$ [HPOS] as -
    · iframe HPOS; ipureintro; exact hqel
    simp only [hjw, hqw, ite_eq_left hb1, ite_eq_left hb2, ite_eq_left hb3]
    wp_apply wp_load_slice_index pS (j : Int) _ DFrac.discard _ (by omega) $$ [HPOS] as -
    · iframe HPOS; ipureintro; exact hqel
    simp only [hjw, hqw, ite_eq_left hb1, ite_eq_left hb2, ite_eq_left hb3]
    obtain ⟨ad, had⟩ : ∃ ad, addrs[qf.val]? = some ad :=
      ⟨_, List.getElem?_eq_getElem (by rw [HPAl]; exact qf.isLt)⟩
    wp_apply wp_load_slice_index alS (qf.val : Int) _ DFrac.discard ad (by omega) $$ [HPALS] as -
    · iframe HPALS; ipureintro; simpa using had
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    ihave #Hdlog : globalAddr gryff.src.dlog.DLOG ↦□ false $$ []
    · iapply replica.dlog_init_access; iPkgInit
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    simp only [hjw, hqw, ite_eq_left hb1, ite_eq_left hb2, ite_eq_left hb3]
    wp_apply wp_load_slice_index pS (j : Int) _ DFrac.discard _ (by omega) $$ [HPOS] as -
    · iframe HPOS; ipureintro; exact hqel
    have hdrop : ([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop j =
        kahn.Out.send qf M :: ([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop (j + 1) := by
      rw [hqv.1]
      obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · rw [(fin3_add k).1]; rfl
      · rw [(fin3_add k).2]; rfl
    rw [hdrop, List.cons_append]
    wp_method_call; wp_call
    wp_auto
    have hspec := Replica.SendMsg.wp γ ρ k qf r gR h t M (globalAddr src.gryff.pa) cPA
      (([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop (j + 1) ++ rest) hqk
    have hMty : msgTy M = go.GoType.PointerType src.gryffproto.PreAccept.ty := by subst hM; rfl
    have hMk : msgKind M = "preAccept" := by subst hM; rfl
    simp only [genM, hMty, hMk] at hspec
    wp_apply hspec $$ [Hm Hpend] as ⟨Hm, Hpend⟩
    · iframe Hm Hpend Hok HgR HcPAc
    wp_if_destruct
    · -- `sent >= n`: the second peer, the loop ends
      obtain rfl : j = 1 := by word
      wp_for_post
      wp_apply wp_recoverPanic $$ [Hpnc] as Hpnc
      · iexact Hpnc
      simp only [List.drop_succ_cons, List.drop_nil, List.nil_append]
      wp_auto
      iapply HΦ
      iframe Hpend
      subst hM
      unfold msgAt
      icases Hm with ⟨%g', %sl', Hpa, -, -⟩
      iapply Hrestc $$ Hpa
    · wp_for_post
      iframe
      iexists (j + 1)
      iframe Hm Hpend
      isplitr
      · ipureintro; word
      isplitl [sent]
      · rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact sent
      rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact q
  · exfalso; apply Hif; word

theorem bcastAccept_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (s : RState) (q i b seq : w32) (sl : GoSlice) (cmds : List Cmd)
    (deps : GoArray w32 5) (base : src.gryffproto.ValTag) (outs rest : List Out)
    (hid : s.id = rid32 k)
    (hb : model.bcastAccept s q i b cmds seq (depsOf deps) (vtOf base) = some outs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ bcFixed γ ρ k r gR h ∗
        epaxosRest h ∗ cmdsRep sl cmds ∗ pendingOuts γ ρ k r t (outs ++ rest) }}
      (App (App (App (App (App (App (App (Val (h @!! go.GoType.PointerType
        src.gryff.EPaxosRMWHandler.ty @!! go!"bcastAccept")) (Val #q)) (Val #i)) (Val #b))
        (Val #sl)) (Val #seq)) (Val #deps)) (Val #base))
    {{ RET #(); epaxosRest h ∗ pendingOuts γ ρ k r t rest }} := by
  wp_start as ⟨⟨#HR, #HgR, #Hid, #HN, #Hfix, #Hok⟩, Hrest, #Hcmds, Hpend⟩
  iunfold h2Fixed at Hfix
  icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    #HThr, #HExec, #HPO, #HPOS, #HPAL, #HPALS, %HPAl, #HSt, #HStOk, #Hbo,
    #HcPA, #HcPAc, #HcA, #HcAc, #Hrc⟩
  -- `Alive` (N1-3): the lock's network side
  icases pendingOuts_alive γ ρ k r gR t _ $$ [$HgR $Hpend] with ⟨Hpend, Hal⟩
  iunfold aliveAt at Hal
  icases Hal with ⟨%aS, #HAl, #HAlS⟩
  icases epaxosRest_ea h $$ Hrest with ⟨%v, Hea, Hrestc⟩
  wp_apply wp_with_defer_recover
  iintro %defer %pnc Hdefer Hpnc
  wp_auto
  dsimp only
  icases (cmdsRep_open ..).1 $$ Hcmds with ⟨%gs, #Hgs, %Hgsc⟩
  obtain ⟨Hgsc, -⟩ := Hgsc
  have ho := bcast_eq' s k hid (.accept ⟨s.id, q, i, b, seq, depsOf deps, cmds, vtOf base⟩)
  simp only [model.bcastAccept] at hb
  rw [hb, Option.some.injEq] at ho
  subst ho
  generalize hM : (Msg.accept ⟨s.id, q, i, b, seq, depsOf deps, cmds, vtOf base⟩) = M
  ihave Hm : msgAt (globalAddr src.gryff.ea) M $$ [Hea]
  · subst hM
    unfold msgAt
    iexists ⟨rid32 k, q, i, b, W32 (sint.Z sl.len), seq, deps, gs, base⟩, sl
    simp only [wire.gryffproto.EAccept.goVal]
    iframe Hea Hgs
    ipureintro; simp only [acceptOf, hid, Hgsc]
  ihave HI : (∃ j : Nat, "%Hj" ∷ ⌜j ≤ 1⌝ ∗ "sent" ∷ sent_ptr ↦ W64 (j : Int) ∗
      "q" ∷ q_ptr ↦ W64 (j : Int) ∗ "Hm" ∷ msgAt (globalAddr src.gryff.ea) M ∗
      "Hpend" ∷ pendingOuts γ ρ k r t
        (([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop j ++ rest) : IProp GF)
    $$ [sent q Hm Hpend]
  · iexists 0
    rw [List.drop_zero]
    iframe
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · ihave %HPOl := ownSlice_len _ _ _ $$ HPOS
    ihave %HAll := ownSlice_len _ _ _ $$ HAlS
    have hjw : sint.Z (W64 (j : Int)) = j := by word
    obtain ⟨qf, hqel, hqk, hqv⟩ := ppo_elem k j Hj
    have hPOl : sint.Z pS.len = 3 := by
      have h1 := HPOl.1; have h2 := HPOl.2
      simp only [List.length_cons, List.length_nil, sint.nat, sint.Z] at h1 h2 ⊢; omega
    have hAll : sint.Z aS.len = 3 := by
      have h1 := HAll.1; have h2 := HAll.2
      simp only [aliveList, List.length_cons, List.length_nil, sint.nat, sint.Z] at h1 h2 ⊢; omega
    have hqw : sint.Z (W64 (sint.Z (rid32 qf))) = (qf.val : Int) := by
      rw [hqv.2]; have := qf.isLt; word
    have hb1 : 0 ≤ (j : Int) ∧ (j : Int) < sint.Z pS.len := by omega
    have hb2 : 0 ≤ (qf.val : Int) ∧ (qf.val : Int) < sint.Z aS.len := by have := qf.isLt; omega
    simp only [hjw, ite_eq_left hb1]
    wp_apply wp_load_slice_index pS (j : Int) _ DFrac.discard _ (by omega) $$ [HPOS] as -
    · iframe HPOS; ipureintro; exact hqel
    simp only [hqw, ite_eq_left hb2]
    wp_apply wp_load_slice_index aS (qf.val : Int) _ DFrac.discard true (by omega) $$ [HAlS] as -
    · iframe HAlS; ipureintro; simpa [hqk] using aliveList_get k qf
    simp only [hjw, ite_eq_left hb1]
    wp_apply wp_load_slice_index pS (j : Int) _ DFrac.discard _ (by omega) $$ [HPOS] as -
    · iframe HPOS; ipureintro; exact hqel
    have hdrop : ([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop j =
        kahn.Out.send qf M :: ([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop (j + 1) := by
      rw [hqv.1]
      obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · rw [(fin3_add k).1]; rfl
      · rw [(fin3_add k).2]; rfl
    rw [hdrop, List.cons_append]
    wp_method_call; wp_call
    wp_auto
    have hspec := Replica.SendMsg.wp γ ρ k qf r gR h t M (globalAddr src.gryff.ea) cA
      (([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop (j + 1) ++ rest) hqk
    have hMty : msgTy M = go.GoType.PointerType src.gryffproto.EAccept.ty := by subst hM; rfl
    have hMk : msgKind M = "accept" := by subst hM; rfl
    simp only [genM, hMty, hMk] at hspec
    wp_apply hspec $$ [Hm Hpend] as ⟨Hm, Hpend⟩
    · iframe Hm Hpend Hok HgR HcAc
    wp_if_destruct
    · obtain rfl : j = 1 := by word
      wp_for_post
      wp_apply wp_recoverPanic $$ [Hpnc] as Hpnc
      · iexact Hpnc
      simp only [List.drop_succ_cons, List.drop_nil, List.nil_append]
      wp_auto
      iapply HΦ
      iframe Hpend
      subst hM
      unfold msgAt
      icases Hm with ⟨%g', %sl', Hea, -, -⟩
      iapply Hrestc $$ Hea
    · wp_for_post
      iframe
      iexists (j + 1)
      iframe Hm Hpend
      isplitr
      · ipureintro; word
      isplitl [sent]
      · rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact sent
      rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact q
  · exfalso; apply Hif; word

theorem bcastCommit_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (s : RState) (q i seq : w32) (sl : GoSlice) (cmds : List Cmd)
    (deps : GoArray w32 5) (base : src.gryffproto.ValTag) (outs rest : List Out)
    (hid : s.id = rid32 k)
    (hb : model.bcastCommit s q i cmds seq (depsOf deps) (vtOf base) = some outs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ bcFixed γ ρ k r gR h ∗
        epaxosRest h ∗ cmdsRep sl cmds ∗ pendingOuts γ ρ k r t (outs ++ rest) }}
      (App (App (App (App (App (App (Val (h @!! go.GoType.PointerType
        src.gryff.EPaxosRMWHandler.ty @!! go!"bcastCommit")) (Val #q)) (Val #i))
        (Val #sl)) (Val #seq)) (Val #deps)) (Val #base))
    {{ RET #(); epaxosRest h ∗ pendingOuts γ ρ k r t rest }} := by
  wp_start as ⟨⟨#HR, #HgR, #Hid, #HN, #Hfix, #Hok⟩, Hrest, #Hcmds, Hpend⟩
  iunfold h2Fixed at Hfix
  icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    #HThr, #HExec, #HPO, #HPOS, #HPAL, #HPALS, %HPAl, #HSt, #HStOk, #Hbo,
    #HcPA, #HcPAc, #HcA, #HcAc, #HcC, #HcCc, #Hrc⟩
  -- `Alive` (N1-3): the lock's network side
  icases pendingOuts_alive γ ρ k r gR t _ $$ [$HgR $Hpend] with ⟨Hpend, Hal⟩
  iunfold aliveAt at Hal
  icases Hal with ⟨%aS, #HAl, #HAlS⟩
  icases epaxosRest_ec h $$ Hrest with ⟨%v, %w, Hec, Hecs, Hrestc⟩
  wp_apply wp_with_defer_recover
  iintro %defer %pnc Hdefer Hpnc
  wp_auto
  dsimp only
  icases (cmdsRep_open ..).1 $$ Hcmds with ⟨%gs, #Hgs, %Hgsc⟩
  obtain ⟨Hgsc, -⟩ := Hgsc
  have ho := bcast_eq' s k hid (.commit ⟨q, i, cmds, seq, depsOf deps, vtOf base⟩)
  simp only [model.bcastCommit] at hb
  rw [hb, Option.some.injEq] at ho
  subst ho
  generalize hM : (Msg.commit ⟨q, i, cmds, seq, depsOf deps, vtOf base⟩) = M
  ihave Hm : msgAt (globalAddr src.gryff.ec) M $$ [Hec]
  · subst hM
    unfold msgAt
    iexists ⟨rid32 k, q, i, gs, seq, deps, base⟩, sl
    simp only [wire.gryffproto.ECommit.goVal]
    iframe Hec Hgs
    ipureintro; simp only [commitOf, Hgsc]
  ihave HI : (∃ j : Nat, "%Hj" ∷ ⌜j ≤ 2⌝ ∗
      "q" ∷ q_ptr ↦ W64 (j : Int) ∗ "Hm" ∷ msgAt (globalAddr src.gryff.ec) M ∗
      "Hpend" ∷ pendingOuts γ ρ k r t
        (([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop j ++ rest) : IProp GF)
    $$ [q Hm Hpend]
  · iexists 0
    rw [List.drop_zero]
    iframe
    ipureintro; omega
  irename «instance» => Hinst
  wp_for HI
  wp_if_destruct
  · have Hj1 : j ≤ 1 := by word
    ihave %HPOl := ownSlice_len _ _ _ $$ HPOS
    ihave %HAll := ownSlice_len _ _ _ $$ HAlS
    ihave %HPALl := ownSlice_len _ _ _ $$ HPALS
    have hjw : sint.Z (W64 (j : Int)) = j := by word
    obtain ⟨qf, hqel, hqk, hqv⟩ := ppo_elem k j Hj1
    have hPOl : sint.Z pS.len = 3 := by
      have h1 := HPOl.1; have h2 := HPOl.2
      simp only [List.length_cons, List.length_nil, sint.nat, sint.Z] at h1 h2 ⊢; omega
    have hAll : sint.Z aS.len = 3 := by
      have h1 := HAll.1; have h2 := HAll.2
      simp only [aliveList, List.length_cons, List.length_nil, sint.nat, sint.Z] at h1 h2 ⊢; omega
    have hPALl : sint.Z alS.len = 3 := by
      have h1 := HPALl.1; have h2 := HPALl.2
      simp only [HPAl, sint.nat, sint.Z] at h1 h2 ⊢; omega
    have hqw : sint.Z (W64 (sint.Z (rid32 qf))) = (qf.val : Int) := by
      rw [hqv.2]; have := qf.isLt; word
    have hb1 : 0 ≤ (j : Int) ∧ (j : Int) < sint.Z pS.len := by omega
    have hb2 : 0 ≤ (qf.val : Int) ∧ (qf.val : Int) < sint.Z aS.len := by have := qf.isLt; omega
    have hb3 : 0 ≤ (qf.val : Int) ∧ (qf.val : Int) < sint.Z alS.len := by have := qf.isLt; omega
    simp only [hjw, ite_eq_left hb1]
    wp_apply wp_load_slice_index pS (j : Int) _ DFrac.discard _ (by omega) $$ [HPOS] as -
    · iframe HPOS; ipureintro; exact hqel
    simp only [hqw, ite_eq_left hb2]
    wp_apply wp_load_slice_index aS (qf.val : Int) _ DFrac.discard true (by omega) $$ [HAlS] as -
    · iframe HAlS; ipureintro; simpa [hqk] using aliveList_get k qf
    simp only [hjw, ite_eq_left hb1]
    wp_apply wp_load_slice_index pS (j : Int) _ DFrac.discard _ (by omega) $$ [HPOS] as -
    · iframe HPOS; ipureintro; exact hqel
    simp only [hjw, hqw, ite_eq_left hb1, ite_eq_left hb2, ite_eq_left hb3]
    wp_apply wp_load_slice_index pS (j : Int) _ DFrac.discard _ (by omega) $$ [HPOS] as -
    · iframe HPOS; ipureintro; exact hqel
    simp only [hjw, hqw, ite_eq_left hb1, ite_eq_left hb2, ite_eq_left hb3]
    obtain ⟨ad, had⟩ : ∃ ad, addrs[qf.val]? = some ad :=
      ⟨_, List.getElem?_eq_getElem (by rw [HPAl]; exact qf.isLt)⟩
    wp_apply wp_load_slice_index alS (qf.val : Int) _ DFrac.discard ad (by omega) $$ [HPALS] as -
    · iframe HPALS; ipureintro; simpa using had
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    ihave #Hdlog : globalAddr gryff.src.dlog.DLOG ↦□ false $$ []
    · iapply replica.dlog_init_access; iPkgInit
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    simp only [hjw, hqw, ite_eq_left hb1, ite_eq_left hb2, ite_eq_left hb3]
    wp_apply wp_load_slice_index pS (j : Int) _ DFrac.discard _ (by omega) $$ [HPOS] as -
    · iframe HPOS; ipureintro; exact hqel
    have hdrop : ([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop j =
        kahn.Out.send qf M :: ([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop (j + 1) := by
      rw [hqv.1]
      obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · rw [(fin3_add k).1]; rfl
      · rw [(fin3_add k).2]; rfl
    rw [hdrop, List.cons_append]
    wp_method_call; wp_call
    wp_auto
    have hspec := Replica.SendMsg.wp γ ρ k qf r gR h t M (globalAddr src.gryff.ec) cC
      (([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop (j + 1) ++ rest) hqk
    have hMty : msgTy M = go.GoType.PointerType src.gryffproto.ECommit.ty := by subst hM; rfl
    have hMk : msgKind M = "commit" := by subst hM; rfl
    simp only [genM, hMty, hMk] at hspec
    wp_apply hspec $$ [Hm Hpend] as ⟨Hm, Hpend⟩
    · iframe Hm Hpend Hok HgR HcCc
    wp_for_post
    iframe
    iexists (j + 1)
    iframe Hm Hpend
    isplitr
    · ipureintro; word
    rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact q
  · obtain rfl : j = 2 := by word
    wp_apply wp_recoverPanic $$ [Hpnc] as Hpnc
    · iexact Hpnc
    simp only [List.drop_succ_cons, List.drop_nil, List.nil_append]
    wp_auto
    iapply HΦ
    iframe Hpend
    subst hM
    unfold msgAt
    icases Hm with ⟨%g', %sl', Hec, -, -⟩
    iapply Hrestc $$ Hec Hecs

/-- `fastPathQuorum()`: `2 * (N / 2)` (not thrifty), the model's `FPQ`. -/
theorem fastPathQuorum_wp (r gR h : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
        gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
        gR.[src.genericsmr.Replica, go!"Thrifty"] ↦□ false }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! go!"fastPathQuorum"))
        (Val #()))
    {{ RET #model.FPQ; True }} := by
  wp_start as ⟨#HR, #HgR, #HN, #HThr⟩
  wp_auto
  rw [show (W64 2 * BitVec.sdiv (W64 3) (W64 2) : w64) = model.FPQ by rfl]
  wp_end

/-- `replyPreAccept(q, reply)`: the reply to peer `q`. -/
theorem replyPreAccept_wp (γ : GryffNames GF) (ρ : Repl2Names) (k q : Fin 3) (r gR h : Loc)
    (t : List Ev) (pr : Loc) (rm : model.PreAcceptReplyM) (rest : List Out) (hq : q ≠ k)
    (x : w32) (hx : x = rid32 q) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ bcFixed γ ρ k r gR h ∗
        msgAt pr (.preAcceptReply rm) ∗
        pendingOuts γ ρ k r t (.send q (.preAcceptReply rm) :: rest) }}
      (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"replyPreAccept")) (Val #x)) (Val #pr))
    {{ RET #(); msgAt pr (.preAcceptReply rm) ∗ pendingOuts γ ρ k r t rest }} := by
  subst hx
  wp_start as ⟨⟨#HR, #HgR, #Hid, #HN, #Hfix, #Hok⟩, Hm, Hpend⟩
  iunfold h2Fixed at Hfix
  icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HcPAR, #HcPARc, -⟩
  wp_auto
  wp_method_call
  wp_auto
  have hspec := Replica.SendMsg.wp γ ρ k q r gR h t (.preAcceptReply rm) pr cPAR rest hq
  simp only [genM, msgTy, msgKind] at hspec
  wp_apply hspec $$ [Hm Hpend] as ⟨Hm, Hpend⟩
  · iframe Hm Hpend Hok HgR HcPARc
  iapply HΦ; iframe

/-- `replyAccept(q, reply)`: the reply to peer `q`. -/
theorem replyAccept_wp (γ : GryffNames GF) (ρ : Repl2Names) (k q : Fin 3) (r gR h : Loc)
    (t : List Ev) (pr : Loc) (rm : model.AcceptReplyM) (rest : List Out) (hq : q ≠ k)
    (x : w32) (hx : x = rid32 q) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ bcFixed γ ρ k r gR h ∗
        msgAt pr (.acceptReply rm) ∗
        pendingOuts γ ρ k r t (.send q (.acceptReply rm) :: rest) }}
      (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"replyAccept")) (Val #x)) (Val #pr))
    {{ RET #(); msgAt pr (.acceptReply rm) ∗ pendingOuts γ ρ k r t rest }} := by
  subst hx
  wp_start as ⟨⟨#HR, #HgR, #Hid, #HN, #Hfix, #Hok⟩, Hm, Hpend⟩
  iunfold h2Fixed at Hfix
  icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HcAR, #HcARc, -⟩
  wp_auto
  wp_method_call
  wp_auto
  have hspec := Replica.SendMsg.wp γ ρ k q r gR h t (.acceptReply rm) pr cAR rest hq
  simp only [genM, msgTy, msgKind] at hspec
  wp_apply hspec $$ [Hm Hpend] as ⟨Hm, Hpend⟩
  · iframe Hm Hpend Hok HgR HcARc
  iapply HΦ; iframe

/-- `replyExecuted(q, reply)`: the reply to peer `q`. -/
theorem replyExecuted_wp (γ : GryffNames GF) (ρ : Repl2Names) (k q : Fin 3) (r gR h : Loc)
    (t : List Ev) (pr : Loc) (rm : model.ExecutedM) (rest : List Out) (hq : q ≠ k)
    (x : w32) (hx : x = rid32 q) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ bcFixed γ ρ k r gR h ∗
        msgAt pr (.executed rm) ∗
        pendingOuts γ ρ k r t (.send q (.executed rm) :: rest) }}
      (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"replyExecuted")) (Val #x)) (Val #pr))
    {{ RET #(); msgAt pr (.executed rm) ∗ pendingOuts γ ρ k r t rest }} := by
  subst hx
  wp_start as ⟨⟨#HR, #HgR, #Hid, #HN, #Hfix, #Hok⟩, Hm, Hpend⟩
  iunfold h2Fixed at Hfix
  icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HcEx, #HcExc, -⟩
  wp_auto
  wp_method_call
  wp_auto
  have hspec := Replica.SendMsg.wp γ ρ k q r gR h t (.executed rm) pr cEx rest hq
  simp only [genM, msgTy, msgKind] at hspec
  wp_apply hspec $$ [Hm Hpend] as ⟨Hm, Hpend⟩
  · iframe Hm Hpend Hok HgR HcExc
  iapply HΦ; iframe

end

end Perennial.gryff.replica2.h2b
