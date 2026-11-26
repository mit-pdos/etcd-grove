/-
`WaitForClientConnections`: accepts connections on the replica's address forever, each served by
its own `serveConn(conn, true)`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Pkg
public import Net.Proof.net.AtAddr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.LibDeps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Log

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [EpNetDeps GF]

theorem replica.Replica.WaitForClientConnections.spec_holds (hSC : replica.Replica.serveConn.spec (GF := GF))
    (hPrintln : dlog.Logger.Println.spec (GF := GF)) : replica.Replica.WaitForClientConnections.spec (GF := GF) := by
  intro γ r id L p Rext
  wp_start as ⟨#Hfw, Hlis⟩
  ihave ⟨%eof, %ed, #Heof, #Hed⟩ := replica_net_errs $$ Hpkg
  ihave #Hfw' := isReplicaFw_def $$ Hfw
  iunfold isReplicaFwDef at Hfw'
  icases Hfw' with ⟨#Hro, #Hfz, #Hmu, #Hph1, #Hph2⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, -, -, #HPeers, #HReaders, #HWriters, -, -, -, -,
    #HAlive, -, #HRPC, -, -, -, #HShut, -, -, -, -, -, -, #HEwma, #HLat, #HDt, %HL, #HLf,
    #HCI, -, -⟩
  ihave Hlis := fwListening_def $$ Hlis
  iunfold fwListeningDef at Hlis
  icases Hlis with ⟨%li, %l, #Hli, #Hisl, Hnl, #Hla⟩
  iunfold net.isListener at Hisl
  icases Hisl with ⟨%tl, %x, %Ht, #Hlt⟩
  subst Ht
  ihave #Hap := fwRO_addrProto γ L id HL.2 $$ HLf HCI
  unfold fwMethod
  wp_method_call
  wp_call
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
  ihave HI : ("Hnl" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l (L.getD id []) true :
    IProp GF) $$ [Hnl]
  · iframe Hnl
  wp_for HI
  wp_apply (net.Listener.Accept.spec_addrOk EpNetDeps.accept) tl l x (L.getD id [])
      (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l (L.getD id []) true)
      (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l (L.getD id []) true ∗
        connEnd (Gg := hG.goose_globalGS) cn true (repAccP γ (L.getD id [])) (repDialP γ (L.getD id []))
          [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn true))
      $$ [Hnl]
    as %cv %err (⟨%Herr, %cid, #Hc, Hnl, Hend, Hfresh⟩ | ⟨%k, Hnl, #Herr⟩)
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
    wp_apply wp_fork $$ [Hsend Hrecv Hfresh]
    · wp_apply hSC γ r id L p Rext _ cid $$ [Hsend Hrecv Hfresh]
      · unfold accEnd connIn
        iframe; iframe #
        ipureintro; rw [Hcv]; rfl
      itrivial
    wp_for_post
    iframe
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

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
