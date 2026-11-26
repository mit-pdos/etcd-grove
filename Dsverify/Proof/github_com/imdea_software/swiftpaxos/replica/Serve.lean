/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Serve.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.WaitForClientConnections()`: a `clientListener` per pending client, then per accepted
connection; proved over its callees' specs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ServeSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnDefs
@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [io.Assumptions] [net.rpc.Assumptions]
  [errors.Assumptions] [dlog.Assumptions] [time.Assumptions]
  [strings.Assumptions] [encoding.binary.Assumptions]

set_option goose.wp.extras true

theorem replica.Replica.WaitForClientConnections.wp_proof
    (wp_cl : replica.Replica.clientListener.spec (hG := hG))
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.WaitForClientConnections.spec (hG := hG) := by
  intro r γ γc γm γw N me a
  wp_start as ⟨#Hrep, Hsv⟩
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  unfold replica.serveSt
  icases Hsv with ⟨%lv, %pcsl, %pcs, %al, HLis, #Hlok, #Hap, Hpc, Hpcs, Hpok, #HAlias⟩
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨-, -⟩
  try wp_auto
  wp_apply replica.wp_Println wp_Println $$ [$Hlg $Hquiet]
  try wp_auto
  ihave %Hpl := ownSlice_len _ _ _ $$ Hpcs
  ihave HL : (∃ (j : w64) (cv : replica.pendingClient),
      "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ cv ∗ "Hpcs" ∷ pcsl ↦* pcs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ pcs.length⌝ ∗
      "Hpok" ∷ ([∗list] p ∈ pcs.drop (sint.Z j).toNat, replica.pendingOk γ γc γm p) : IProp netDistGF)
    $$ [i c Hpcs Hpok]
  · iexists _, _; iframe; isplitr
    · ipureintro; simp
    · simp; iexact Hpok
  wp_for HL
  wp_if_destruct
  · have hjl : (sint.Z j).toNat < pcs.length := by
      have e1 : sint.nat pcsl.len = (sint.Z pcsl.len).toNat := rfl
      omega
    obtain ⟨p, hp⟩ : ∃ p, pcs[(sint.Z j).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem hjl⟩
    rw [if_pos ⟨Hj.1, Hif⟩]
    try wp_auto
    wp_apply wp_load_slice_index _ _ _ _ p (by omega) $$ [Hpcs] as Hpcs
    · iframe Hpcs; ipureintro; exact hp
    rw [List.drop_eq_getElem_cons hjl, (List.getElem?_eq_some_iff.1 hp).2]
    icases Hpok with ⟨Hp, Hpok⟩
    try wp_auto
    wp_apply wp_fork $$ [Hp]
    · unfold replica.pendingOk
      icases Hp with ⟨%cid, #Hci, Hrd, #Hpp, %Hf, Hsend⟩
      wp_apply wp_cl r γ γc γm γw N me al p.conn' cid p.reader' p.first' true $$ [Hrd $Hsend]
      · isplitr; · iexact Hrep
        isplitr; · iexact HAlias
        isplitr; · iexact Hci
        isplitl [Hrd]
        · simp only [↓reduceIte]; iexact Hrd
        isplitr
        · simp only [↓reduceIte]; iexact Hpp
        ipureintro; intro _; exact Hf
      ipureintro; exact isPanic_intoVal ()
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    have hj1 : sint.Z (j + W64 1) = sint.Z j + 1 := by word
    rw [hj1]
    have e : (sint.Z j + 1).toNat = (sint.Z j).toNat + 1 := by omega
    rw [e]
    iframe
    ipureintro; omega
  · -- the accept loop
    iclear Hpcs Hpok Hpc
    ihave #Hlok2 := Hlok
    iunfold replica.listenerOk at Hlok2
    icases Hlok2 with ⟨%ll, %lid, %Hlv, #Hlis⟩
    subst Hlv
    ihave HL2 : (∃ u : Unit, "HLis" ∷ replica.fld r go!"Listener" ↦
        interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #ll ∗ "%Hu" ∷ ⌜u = ()⌝ :
        IProp netDistGF) $$ [HLis]
    · iexists (); iframe; ipureintro; rfl
    wp_for HL2
    try rw [if_pos (decide_eq_true rfl)]
    try wp_auto
    wp_apply net.TCPListener.Accept.labProof ll lid (replica.wildOf a) (sp.inP γ γc γm)
      (sp.outQ γ γc γm) $$ [$Hlis $Hap] as %cv %er Hres
    unfold net.newConnResult
    icases Hres with (⟨%c, %cid, ⟨%Hcv, %Her⟩, #Hown, Hend, -⟩ | ⟨%i, %Her, %Herr⟩)
    · subst Hcv Her
      iunfold connEnd at Hend
      icases Hend with ⟨Hsend, Hrecv⟩
      wp_auto
      ihave #Hci : net.rpc.connIface (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)
        cid true $$ []
      · ihave #Hown' := Hown
        iunfold net.ownTCPConn at Hown'
        icases Hown' with ⟨%a0, %la0, %ra0, #Hat0, #Hcs0⟩
        unfold net.rpc.connIface; iexists c, a0, la0, ra0; iframe Hat0 Hcs0; ipureintro; rfl
      ihave #Hrdok := bufio.readerOk_conn _ cid true (sp.inP γ γc γm) $$ [$Hpkg3 $Hci]
      ihave Hrecv := recvTok_L _ _ _ _ $$ Hrecv
      wp_apply bufio.wp_NewReader _ _ [] $$ [$Hrdok $Hrecv] as %br Hrd
      try wp_auto
      wp_apply wp_fork $$ [Hrd Hsend]
      · wp_apply wp_cl r γ γc γm γw N me al _ cid br (W8 0) false $$ [Hrd $Hsend]
        · isplitr; · iexact Hrep
          isplitr; · iexact HAlias
          isplitr; · iexact Hci
          isplitl [Hrd]
          · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hrd
          isplitr
          · simp only [Bool.false_eq_true, ↓reduceIte]; unfold protoPrefix; ileft; ipureintro; rfl
          ipureintro; intro h; cases h
        ipureintro; exact isPanic_intoVal ()
      try wp_auto
      wp_for_post
      iframe
      iexists (); iframe
    · subst Her
      wp_auto
      wp_apply wp_slice_literal (V := GoInterface)
      isplitr
      · ipureintro; rfl
      iintro %s2 ⟨-, -⟩
      try wp_auto
      wp_apply replica.wp_Println wp_Println $$ [$Hlg $Hquiet]
      wp_for_post
      iframe
      iexists (); iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos
