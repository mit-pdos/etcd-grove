/-
`waitForPeerConnections` (the listener goroutine of `ConnectToPeers`): listens on the replica's
address, accepts as many connections as there are higher ids (each installed by
`serveConn(conn, false)` if a higher peer's), and hands its cells, `Listener` and the listener
back on `done`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.WaitClients
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.LibDeps
public import Net.Proof.net.AtAddr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Dial
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.WaitClients

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS] [io.Assumptions]

theorem wp_rFatal (hP : dlog.Logger.Fatal.spec (GF := GF)) (γ : EpNames) (r : Loc) (id : Nat)
    (L : List GoString) (p : FwPtrs) (v : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.dlog ∗
        fwRO γ r id L p }}
      (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"Fatal")) (Val #v))
    {{ RET #(); True }} := by
  wp_start as #Hro
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, -⟩
  rw [dlog_zero_logger] at *
  wp_auto
  wp_apply (hP p.logger null _) $$ [$HLogv]
  wp_end

/-- What `waitForPeerConnections` sends on `done`: its cells and the listener. -/
def wfDone (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) : IProp GF :=
  iprop(wfOwnX γ id L p ∗ fwListening γ r id L)

/-- `r.waitForPeerConnections(done)`. -/
def replica.Replica.waitForPeerConnections.specX : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (done : GoChan) (γc : ChanNames),
  {{ pkgInit_replica ∗ fwRun0 γ r id L p Rext ∗
      fld r go!"Listener" ↦ (interface.nil : GoInterface) ∗ wfOwnX γ id L p ∗
      isChanBag (V := Bool) γc done (fun _ => wfDone γ r id L p) }}
    (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"waitForPeerConnections"))
      (Val #done))
  {{ RET #(); True }}

variable [EpNetDeps GF] [EpReplicaDeps GF]

theorem replica.Replica.waitForPeerConnections.spec_holds (hSC : replica.Replica.serveConnDial.specX (GF := GF))
    (hPrintln : dlog.Logger.Println.spec (GF := GF)) (hFatal : dlog.Logger.Fatal.spec (GF := GF)) :
    replica.Replica.waitForPeerConnections.specX (GF := GF) := by
  intro γ r id L p Rext done γc
  wp_start as ⟨#Hrun, Hlis, Hwf, #Hdone⟩
  ihave ⟨%eof, %ed, #Heof, #Hed⟩ := replica_net_errs $$ Hpkg
  ihave #Hrun' : fwRO γ r id L p ∗ sync.isMutex (fld r go!"M") (fwLockInv γ id L p Rext) $$ [Hrun]
  · unfold fwRun0; iexact Hrun
  icases Hrun' with ⟨#Hro, #Hmu⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, #HPAL, #HL0, #HPeers, #HReaders, #HWriters, -, -, -, -,
    #HAlive, -, #HRPC, -, -, -, #HShut, -, -, -, -, -, -, #HEwma, #HLat, #HDt, %HL, #HLf,
    #HCI, -, -⟩
  ihave %Hal := ownSlice_len _ _ _ $$ HL0
  have hN : L.length = 5 := HL.1
  have hid5 : id < 5 := by have := HL.2; omega
  have hidz : sint.Z (W64 (sint.Z (W32 (id : Int)))) = (id : Int) := by word
  have hal : sint.Z p.addrs.len = 5 := by have h1 := Hal.1; have h2 := Hal.2; rw [hN] at h1; word
  have hgl : L[id]? = some (L.getD id []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  ihave #Hap := fwRO_addrProto γ L id HL.2 $$ HLf HCI
  ihave %Hok := addrTok_ok _ $$ [Hap]
  · iapply addrProto_tok $$ Hap
  wp_auto
  rw [hidz, if_pos (show 0 ≤ (id : Int) ∧ (id : Int) < sint.Z p.addrs.len by omega)]
  wp_apply wp_load_slice_index p.addrs (id : Int) L DFrac.discard (L.getD id []) (by omega)
    $$ [HL0] as -
  · iframe #; ipureintro; simpa using hgl
  wp_apply (net.Listen.spec_addrOk EpNetDeps.listen) go!"tcp" net.tcpNet_tcp (L.getD id [])
    as %lv %err Hres
  · iframe %Hok
    iapply listen_au $$ Hap
  -- retry until listening
  ihave HI : (∃ (lv' e : GoInterface), "l" ∷ l_ptr ↦ lv' ∗ "err" ∷ err_ptr ↦ e ∗
      "Hres" ∷ (⌜e ≠ interface.nil⌝ ∨ (⌜e = interface.nil⌝ ∗ ∃ l : w64,
        net.isListener lv' l ∗ netLis (extLocalGS netExt (L := hG.goose_localGS)) l (L.getD id []) true ∗
        netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l (L.getD id [])))) $$ [l err Hres]
  · iexists lv, err
    iframe
    icases Hres with (⟨%He, %l, #Hl, Hnl, #Hla⟩ | ⟨%x, -, #HE⟩)
    · iright; isplitr; · ipureintro; exact He
      iexists l; iframe; iframe #
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      ileft; ipureintro; simp
  wp_for HI
  icases Hres with (%He | ⟨%He, %l, #Hl, Hnl, #Hla⟩)
  · cases e with
    | nil => exact absurd rfl He
    | ok ei =>
    wp_auto
    wp_if_destruct
    rotate_left
    · exfalso; simp only [goose_wp_simp_extra, goose_wp_simp] at Hif
    rw [hidz, if_pos (show 0 ≤ (id : Int) ∧ (id : Int) < sint.Z p.addrs.len by omega)]
    wp_apply wp_load_slice_index p.addrs (id : Int) L DFrac.discard (L.getD id []) (by omega)
      $$ [HL0] as -
    · iframe #; ipureintro; simpa using hgl
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.any)
    wp_auto
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨-, -⟩
    wp_auto
    wp_apply wp_rFatal hFatal γ r id L p $$ [$Hro]
    wp_apply time.Sleep.wp_proof
    rw [hidz, if_pos (show 0 ≤ (id : Int) ∧ (id : Int) < sint.Z p.addrs.len by omega)]
    wp_apply wp_load_slice_index p.addrs (id : Int) L DFrac.discard (L.getD id []) (by omega)
      $$ [HL0] as -
    · iframe #; ipureintro; simpa using hgl
    wp_apply (net.Listen.spec_addrOk EpNetDeps.listen) go!"tcp" net.tcpNet_tcp (L.getD id [])
      as %lv2 %err2 Hres
    · iframe %Hok
      iapply listen_au $$ Hap
    wp_for_post
    iframe
    iexists lv2, err2
    iframe
    icases Hres with (⟨%He, %l, #Hl, Hnl, #Hla⟩ | ⟨%x, -, #HE⟩)
    · iright; isplitr; · ipureintro; exact He
      iexists l; iframe; iframe #
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      ileft; ipureintro; simp
  subst He
  ihave #Hl' := Hl
  iunfold net.isListener at Hl'
  icases Hl' with ⟨%tl, %x, %Ht, #Hlt⟩
  subst Ht
  wp_auto
  wp_if_destruct
  · exfalso; simp only [goose_wp_simp_extra, goose_wp_simp] at Hif
  ipersist Hlis
  ihave HJ : (∃ k : Nat, "i" ∷ i_ptr ↦ W32 (k : Int) ∗ "%Hk" ∷ ⌜id + 1 ≤ k ∧ k ≤ 5⌝ ∗
      "Hwf" ∷ wfOwnX γ id L p ∗ "Hnl" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l (L.getD id []) true) $$ [i Hwf Hnl]
  · iexists id + 1
    rw [show W32 (id : Int) + W32 1 = W32 ((id + 1 : Nat) : Int) by word]
    iframe
    ipureintro; omega
  wp_for HJ
  rw [hN]
  wp_if_destruct
  · -- one more accept
    wp_apply (net.Listener.Accept.spec_addrOk EpNetDeps.accept) tl l x (L.getD id [])
        (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l (L.getD id []) true)
        (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l (L.getD id []) true ∗
          connEnd (Gg := hG.goose_globalGS) cn true (repAccP γ (L.getD id [])) (repDialP γ (L.getD id []))
            [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn true))
        $$ [Hnl]
      as %cv %err (⟨%Herr, %cid, #Hc, Hnl, Hend, Hfresh⟩ | ⟨%ke, Hnl, #Herr⟩)
    · iframe Hlt Hla
      iapply accept_au (L.getD id []) (repDialP γ (L.getD id [])) (repAccP γ (L.getD id [])) _ l true
        $$ Hap Hnl
    · subst Herr
      iunfold connEnd at Hend
      icases Hend with ⟨Hsend, Hrecv⟩
      wp_auto
      ihave #Hc' := Hc
      iunfold net.isConn at Hc'
      icases Hc' with ⟨%tc, %la, %ra, %Hcv, #Hca⟩
      wp_apply hSC γ r id L p Rext _ cid $$ [Hwf Hsend Hrecv Hfresh] as Hwf
      · iframe #
        unfold accEnd connIn
        iframe; iframe #
        ipureintro; rw [Hcv]; rfl
      wp_for_post
      iframe
      iexists k + 1
      rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by word]
      iframe
      ipureintro
      have : k < 5 := by
        revert Hif; word
      omega
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
      obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.any)
      wp_auto
      isplitr
      · ipureintro; rfl
      iintro %sl_ptr ⟨-, -⟩
      wp_auto
      wp_apply wp_rPrintln hPrintln γ r id L p $$ [$Hro]
      wp_for_post
      iframe
      iexists k + 1
      rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by word]
      iframe
      ipureintro
      have : k < 5 := by
        revert Hif; word
      omega
  · -- done: the cells and the listener go back to `ConnectToPeers`
    wp_apply (wp_bag_send γc done true (fun _ => wfDone γ r id L p)) $$ [Hwf Hnl]
    · iframe #
      unfold wfDone
      iframe
      rw [fwListening_unseal]
      unfold fwListeningDef
      iexists _, l
      iframe #
      iframe
    iapply HΦ; itrivial

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
