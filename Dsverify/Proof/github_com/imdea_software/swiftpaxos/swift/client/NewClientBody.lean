/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/NewClientBody.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`swift.NewClient(b, N)`'s proof (swift/client.go:37) over its callees' specs: the struct, the
table and channels (`initCs`), the readers (`RegisterRPCTable`), the quorums, the handler
(`handleMsgs`, forked), and the client's part (`client.ready`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.NewClientParts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.NewClient
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

open swift.rd

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions] [net.Assumptions] [net.FieldAssumptions]
  [rpc.Assumptions] [replica.defs.Assumptions]

set_option goose.wp.extras true

theorem NewClient.wp_proofI (facts : ClientPkgFacts)
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (wp_initCs : initCs.specI (hG := hG))
    (wp_reg : RegisterRPCTable.specI (hG := hG))
    (wp_hm : handleMsgs.specI (hG := hG))
    (wp_maj : replica.quorum.NewMajorityOf.specI (hG := hG))
    (wp_tq : replica.quorum.NewThreeQuartersOf.specI (hG := hG)) :
    swift.NewClient.spec (hG := hG) := by
  intro b γ γc γm γl cid N
  wp_start as ⟨Hconn, #Hinv, Hseq, #Hgok, #Hreg, #Hpool⟩
  icases (client.connected_unfold _ _ _ _ _ _).1 $$ Hconn with ⟨%bv, %v, %l, %fr, %srvs, %rds, %wrs,
    #Hb, Hv, #Hq, #Hcfg, Hl, Hsrvs, Hrds, Hwrs, %Hpure, Hends, %γch, #Hch, Hoch⟩
  haveI := cmdId_intoValInj (sem := sem)
  ihave ⟨%cf, #Hcf, %Hcfn⟩ := sp.cfg_confIs _ _ _ $$ Hcfg
  ihave %Hvalid := confIs_valid _ _ $$ Hcf
  have hN : N = 3 ∨ N = 5 := by rw [← Hcfn.1]; exact Hvalid.1
  have hN62 : N < 2 ^ 62 := by omega
  wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := GoMap)) as %mreps Hmreps
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %rch %rγ ⟨#Hrch, %Hrcap, Hroch⟩
  · ipureintro; decide
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %mdel Hmdel
  wp_apply wp_maj N hN62
  wp_apply wp_tq as %tq -
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Loc)) as %mslow Hmslow
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Loc)) as %mfast Hmfast
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %malready Hmalready
  iStructNamed «$r0»
  wp_apply rpc.wp_NewTableId (W8 9) as %t Ht
  wp_apply wp_initCs _ t _ $$ [$cs $Ht] as ⟨%vcs, %M, %idn, Hcs, Ht, HfR, HfFAC, HfLSA, HfA, HfFA,
    HfAk, HfOA, %HM⟩
  obtain ⟨hcl, hseqb, hcid, hseqn, hfast, hll, hdt, hsl, hrl, hwl⟩ := Hpure
  -- the configuration's membership has `N` addresses
  ihave %HlN : ⌜l.length = N⌝ $$ [Hcfg]
  · unfold sp.cfg; icases Hcfg with ⟨%c0, -, -, %Hc0⟩; ipureintro; exact Hc0.2.2
  -- the client's id (HUB-REQUEST 10)
  ihave Hpos := clientSeq_pos γ γc γm γl ⊤ (by simp) cid 0 $$ [$Hinv $Hseq]
  iapply fupd_wp
  imod Hpos with ⟨%Hcid, Hseq⟩
  imodintro
  -- the handler's ghost state: delivery tokens, reply records
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat) (V := Unit) with ⟨%γd, Hγd⟩
  imod mono_list_own_alloc (GF := netDistGF) (A := sp.CmdId × w32) [] with ⟨%γr, Hγr, -⟩
  -- the package-level facts (change log C6)
  ihave ⟨#Hhook, %ov, #Hov, %Hovn⟩ := facts.pkgFacts $$ Hpkg
  -- the reply channel's protocol
  imod start_bag (client.replyP γ cid γd) (ChanState.Buffered []) bv.Reply' γch (by trivial) $$
    Hch Hoch with #HbReply
  let H : HC := ⟨γ, γc, γm, γl, γd, γr, cid, N, fr, l, «$r0_ptr», b, bv, γch, v.Logger'⟩
  -- the handler's channels
  unfold freshChan
  icases HfR with ⟨%gR, #HcR, HoR⟩
  icases HfFAC with ⟨%gF, #HcF, HoF⟩
  icases HfLSA with ⟨%gL, #HcL, HoL⟩
  icases HfA with ⟨%gA, #HcA, HoA⟩
  icases HfFA with ⟨%gFA, #HcFA, HoFA⟩
  icases HfAk with ⟨%gAk, #HcAk, HoAk⟩
  icases HfOA with ⟨%gO, #HcO, HoO⟩
  imod start_bag (repP H) (ChanState.Buffered []) _ gR (by trivial) $$ HcR HoR with #HbR
  imod start_bag (facP H) (ChanState.Buffered []) _ gF (by trivial) $$ HcF HoF with #HbF
  imod start_bag (lsP H) (ChanState.Buffered []) _ gL (by trivial) $$ HcL HoL with #HbL
  imod start_bag (fun _ : GoInterface => iprop(False)) (ChanState.Buffered []) _ gA (by trivial) $$
    HcA HoA with #HbA
  imod start_bag (fun _ : GoInterface => iprop(False)) (ChanState.Buffered []) _ gFA (by trivial) $$
    HcFA HoFA with #HbFA
  imod start_bag (fun _ : GoInterface => iprop(False)) (ChanState.Buffered []) _ gAk (by trivial) $$
    HcAk HoAk with #HbAk
  imod start_bag (fun _ : GoInterface => iprop(False)) (ChanState.Buffered []) _ gO (by trivial) $$
    HcO HoO with #HbO
  -- the table, read-only from now on
  imod rpc.tblOwn_persist $$ Ht with #Ht
  ihave #Htbl : tblOk H t $$ []
  · unfold tblOk
    obtain ⟨⟨o1, h1⟩, ⟨o2, h2⟩, ⟨o3, h3⟩⟩ := HM
    iexists M, o1, o2, o3, _, _, _, gF, gL, gR
    iframe Ht HbF HbL HbR
    ipureintro; exact ⟨h1, h2, h3⟩
  -- the client struct's fields
  iStructNamed Hv
  ihave #Hnet : (isPkgInit (PROP := IProp netDistGF) pkg_id.net) $$ []
  · solve_pkg_init
  ihave #Hrep : (isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.replica) $$ []
  · solve_pkg_init
  icases ends_split H srvs rds wrs (by omega) (by omega) $$ [$Hnet $Hends] with ⟨Hrdends, Hwrends⟩
  ipersist readers
  ipersist replicas
  ipersist dt
  ipersist Hrds
  ipersist Hl
  rw [hdt]
  ihave #Hbf := Hb
  iStructNamed Hbf
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_reg H bv.Client' t v.readers' v.replicas' rds l ov $$
    [$readers $Hrds $replicas $Hl $dt $Hov $Htbl $Hrdends]
  · ipureintro; exact ⟨Hovn, by omega⟩
  wp_apply wp_maj N hN62
  ipersist Logger
  -- `c.Println("SQ:", c.SQ)`, `c.Println("FQ:", c.FQ)`
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨-, -⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_Println $$ Hq
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨-, -⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_Println $$ Hq
  -- the handler's context and state
  ipersist BufferClient
  ipersist n
  ipersist SQ
  ipersist FQ
  iStructNamed Hcs
  ipersist replyChan
  ipersist fastAckClientChan
  ipersist lightSlowAckChan
  ipersist acceptChan
  ipersist fastAckChan
  ipersist acksChan
  ipersist optAcksChan
  ihave #Hctx : ctxOk H $$ []
  · unfold ctxOk
    iframe Hinv Hcfg Hb HbReply BufferClient Logger Hq n Hhook Hpool
    ipureintro; simp only [H]; omega
  ihave #Hquo : quorumsOk H $$ []
  · unfold quorumsOk
    iframe SQ
    iExactEq FQ; rfl
  ihave Hcsok : csOk H $$ []
  · unfold csOk
    iexists _, _, _, _, _, _, _, gR, gF, gL, gA, gFA, gAk, gO
    iframe replyChan HbR fastAckClientChan HbF lightSlowAckChan HbL acceptChan HbA fastAckChan HbFA
      acksChan HbAk optAcksChan HbO
  ihave Hst : hst H $$ [delivered Hmdel reps Hmreps slowPaths alreadySlow Hmalready Hγd Hγr
      fastPathH Hmfast slowPathH Hmslow ballot]
  · unfold hst core pathsOwn
    isplitl [delivered Hmdel reps Hmreps slowPaths alreadySlow Hmalready Hγd Hγr]
    · iexists mdel, mreps, malready, ∅, ∅, ∅, [], ∅, W64 0
      iframe
      isplitr
      · iapply BigSepM.bigSepM_empty.2; iempintro
      ipureintro
      refine ⟨fun x hx => by simp at hx, fun k => by simp, fun x b hx => by simp at hx⟩
    isplitl [fastPathH Hmfast]
    · iexists mfast, ∅
      iframe
      isplitr
      · iapply BigSepM.bigSepM_empty.2; iempintro
      ipureintro; trivial
    isplitl [slowPathH Hmslow]
    · iexists mslow, ∅
      iframe
      isplitr
      · iapply BigSepM.bigSepM_empty.2; iempintro
      ipureintro; trivial
    iexists _
    iexact ballot
  ihave %Hsl := ownSlice_len $$ Hsrvs
  ipersist ClientId
  ipersist Fast
  ipersist Leaderless
  ipersist LeaderId
  ipersist servers
  ipersist writers
  ipersist Hwrs
  wp_apply wp_fork $$ [Hst Hcsok]
  · wp_apply wp_hm H $$ [$Hpkg $Hrep $Hctx $Hquo $Hst $Hcsok]
    ipureintro; simp
  -- the client's part
  iapply HΦ
  iapply (client.ready_unfold _ _ _ _ _ _ _).2
  iexists bv, bv.Client', N, γch, γd
  iframe Hb Hinv Hseq HbReply
  isplitr
  · ipureintro; exact ⟨rfl, hcl, Hcid⟩
  isplitl [seqnum]
  · iExactEq seqnum; rw [hseqn]; rfl
  isplitl [Hwrends]
  · unfold client.sendSt
    iexists v.Logger', v.LeaderId', v.servers', v.writers', wrs
    rw [hcid, hfast, hll] at *
    iframe ClientId Fast Leaderless Logger Hq LeaderId servers writers Hwrs Hwrends
    ipureintro
    obtain ⟨h1, h2⟩ := Hsl
    refine ⟨by omega, h2, hwl⟩
  isplitr
  · unfold client.toks
    simp only [List.range_zero, BigSepL.bigSepL_nil]
    iempintro
  iframe Hreg
  iunfold client.nodeGhostOk at Hgok
  iexact Hgok

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
