/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Sender.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`replica/sender.go`, proved over `SendMsg`'s and `SendClientMsg`'s specs (Writers.lean): the
loops over the peers (`sendToAll`, `sendToAllExcept`, `sendToQuorum`, `sendExcept`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WriterSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

set_option goose.wp.extras true
set_option linter.unusedSectionVars false

set_option hygiene false in
/-- The loop's next index. -/
local macro "nextp" : tactic => `(tactic| (
  wp_for_post
  iframe
  iexists _
  iframe
  ipureintro
  have e1 : sint.Z pv = pv.toInt := rfl
  have hpv : (pv + W32 1).toInt = pv.toInt + 1 := by
    have : sint.Z pv < 2 ^ 31 - 1 := by omega
    have e2 : sint.Z (pv + W32 1) = (pv + W32 1).toInt := rfl
    rw [← e1, ← e2]; word
  exact ⟨by omega, by omega⟩))

set_option hygiene false in
/-- Lock; if `Alive[p]` (unlock, `SendMsg(p, ...)`, lock); unlock. -/
local macro "peerstep" : tactic => `(tactic| (
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  iunfold replica.lockInv at HR
  icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
  ihave %Hall := ownSlice_len _ _ _ $$ Hal
  try wp_auto
  have hi : sint.Z (W64 (sint.Z pv)) = pv.toInt := by
    have : sint.Z pv = pv.toInt := rfl
    rw [this]; word
  have hlen : sint.Z alsl.len = N := by
    obtain ⟨h1, h2⟩ := Hall; rw [Hl.1] at h1
    have e1 : sint.nat alsl.len = (sint.Z alsl.len).toNat := rfl
    omega
  rw [hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨Hp.1, by
    have : sint.Z pv = pv.toInt := rfl; omega⟩)]
  obtain ⟨av, hav⟩ : ∃ av, alive[pv.toInt.toNat]? = some av :=
    ⟨_, List.getElem?_eq_getElem (by have : sint.Z pv = pv.toInt := rfl; omega)⟩
  wp_apply wp_load_slice_index _ _ _ _ av Hp.1 $$ [Hal] as Hal
  · iframe Hal; ipureintro; exact hav
  wp_if_destruct
  · try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
    · iframe Hmu Hlocked
      try inext
      try unfold replica.lockInv
      iexists alive, lats
      iframe
      ipureintro; exact Hl
    try wp_auto
    nextp
  · try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
    · iframe Hmu Hlocked
      try inext
      try unfold replica.lockInv
      iexists alive, lats
      iframe
      ipureintro; exact Hl
    try wp_auto
    wp_apply wp_SendMsg r γ γc γm γw N me pv rpc msg m $$ [HP] as HP
    · isplitl []
      · iexact Hrep
      isplitl []
      · iexact Hmar
      isplitl [HP]
      · iexact HP
      isplitl []
      · iexact Hm
      ipureintro
      exact ⟨Hmm.1, Hmm.2, Hp.1, by have : sint.Z pv = pv.toInt := rfl; omega⟩
    try wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
    · iexact Hmu
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [Hlocked HR]
    · iframe Hmu Hlocked; inext; iexact HR
    try wp_auto
    nextp))

theorem replica.sendToAll.wp_proof
    (wp_SendMsg : replica.Replica.SendMsgP.spec (hG := hG)) :
    replica.sendToAll.spec (hG := hG) := by
  intro r γ γc γm γw N me msg m rpc Pm
  wp_start as ⟨#Hrep, Hsend⟩
  iunfold sp.peerSend at Hsend
  icases Hsend with ⟨#Hmar, HP, #Hm, %Hmm⟩
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_auto
  ihave HL : (∃ pv : w32, "p" ∷ p_ptr ↦ pv ∗ "HP" ∷ Pm ∗
      "%Hp" ∷ ⌜0 ≤ pv.toInt ∧ pv.toInt ≤ N⌝ : IProp netDistGF) $$ [p HP]
  · iexists _; iframe; ipureintro; simp
  have h7 := Hlens.2.2.2
  have hN : sint.Z (W32 (sint.Z (W64 (N : Int)))) = N := by
    match N, h7 with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
    | 6, _ => rfl | 7, _ => rfl
  wp_for HL
  try wp_auto
  rw [hN]
  by_cases hlt : sint.Z pv < N
  · rw [if_pos (by simp [hlt])]
    try wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
    · iexact Hmu
    iunfold replica.lockInv at HR
    icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
    ihave %Hall := ownSlice_len _ _ _ $$ Hal
    try wp_auto
    have hi : sint.Z (W64 (sint.Z pv)) = pv.toInt := by
      have : sint.Z pv = pv.toInt := rfl
      rw [this]; word
    have hlen : sint.Z alsl.len = N := by
      obtain ⟨h1, h2⟩ := Hall; rw [Hl.1] at h1
      have e1 : sint.nat alsl.len = (sint.Z alsl.len).toNat := rfl
      omega
    rw [hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨Hp.1, by
      have : sint.Z pv = pv.toInt := rfl; omega⟩)]
    obtain ⟨av, hav⟩ : ∃ av, alive[pv.toInt.toNat]? = some av :=
      ⟨_, List.getElem?_eq_getElem (by have : sint.Z pv = pv.toInt := rfl; omega)⟩
    wp_apply wp_load_slice_index _ _ _ _ av Hp.1 $$ [Hal] as Hal
    · iframe Hal; ipureintro; exact hav
    wp_if_destruct
    · try wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
      · iframe Hmu Hlocked
        try inext
        try unfold replica.lockInv
        iexists alive, lats
        iframe
        ipureintro; exact Hl
      try wp_auto
      nextp
    · try wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
      · iframe Hmu Hlocked
        try inext
        try unfold replica.lockInv
        iexists alive, lats
        iframe
        ipureintro; exact Hl
      try wp_auto
      wp_apply wp_SendMsg r γ γc γm γw N me pv rpc msg m $$ [HP] as HP
      · isplitl []
        · iexact Hrep
        isplitl []
        · iexact Hmar
        isplitl [HP]
        · iexact HP
        isplitl []
        · iexact Hm
        ipureintro
        exact ⟨Hmm.1, Hmm.2, Hp.1, by have : sint.Z pv = pv.toInt := rfl; omega⟩
      try wp_auto
      wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
      · iexact Hmu
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [Hlocked HR]
      · iframe Hmu Hlocked; inext; iexact HR
      try wp_auto
      nextp
  · rw [if_neg (by simp [hlt])]
    try wp_auto
    rw [if_neg (by simp [hlt])]
    try wp_auto
    iapply HΦ; iexact HP

theorem replica.sendToAllExcept.wp_proof
    (wp_SendMsg : replica.Replica.SendMsgP.spec (hG := hG)) :
    replica.sendToAllExcept.spec (hG := hG) := by
  intro r γ γc γm γw N me ex msg m rpc Pm
  wp_start as ⟨#Hrep, Hsend⟩
  iunfold sp.peerSend at Hsend
  icases Hsend with ⟨#Hmar, HP, #Hm, %Hmm⟩
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_auto
  ihave HL : (∃ pv : w32, "p" ∷ p_ptr ↦ pv ∗ "HP" ∷ Pm ∗
      "%Hp" ∷ ⌜0 ≤ pv.toInt ∧ pv.toInt ≤ N⌝ : IProp netDistGF) $$ [p HP]
  · iexists _; iframe; ipureintro; simp
  have h7 := Hlens.2.2.2
  have hN : sint.Z (W32 (sint.Z (W64 (N : Int)))) = N := by
    match N, h7 with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
    | 6, _ => rfl | 7, _ => rfl
  wp_for HL
  try wp_auto
  rw [hN]
  by_cases hlt : sint.Z pv < N
  · rw [if_pos (by simp [hlt])]
    try wp_auto
    wp_if_destruct
    · try wp_auto
      nextp
    · peerstep
  · rw [if_neg (by simp [hlt])]
    try wp_auto
    rw [if_neg (by simp [hlt])]
    try wp_auto
    iapply HΦ; iexact HP

theorem replica.sendToQuorum.wp_proof
    (wp_SendMsg : replica.Replica.SendMsgP.spec (hG := hG))
    (wp_Contains : replica.Quorum.Contains.spec (hG := hG)) :
    replica.sendToQuorum.spec (hG := hG) := by
  intro r γ γc γm γw N me q dq qs msg m rpc Pm
  wp_start as ⟨#Hrep, Hq, Hsend⟩
  iunfold sp.peerSend at Hsend
  icases Hsend with ⟨#Hmar, HP, #Hm, %Hmm⟩
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_auto
  ihave HL : (∃ pv : w32, "p" ∷ p_ptr ↦ pv ∗ "HP" ∷ Pm ∗
      "Hq" ∷ replica.quorum.qOwn q dq qs ∗
      "%Hp" ∷ ⌜0 ≤ pv.toInt ∧ pv.toInt ≤ N⌝ : IProp netDistGF) $$ [p HP Hq]
  · iexists _; iframe; ipureintro; simp
  have h7 := Hlens.2.2.2
  have hN : sint.Z (W32 (sint.Z (W64 (N : Int)))) = N := by
    match N, h7 with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
    | 6, _ => rfl | 7, _ => rfl
  wp_for HL
  try wp_auto
  rw [hN]
  by_cases hlt : sint.Z pv < N
  · rw [if_pos (by simp [hlt])]
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    wp_apply wp_Contains q dq qs pv $$ [$Hq] as Hq
    try wp_auto
    wp_if_destruct
    all_goals first | (try wp_auto); nextp | peerstep
  · rw [if_neg (by simp [hlt])]
    try wp_auto
    rw [if_neg (by simp [hlt])]
    try wp_auto
    iapply HΦ; iframe

theorem replica.sendExcept.wp_proof
    (wp_SendMsg : replica.Replica.SendMsgP.spec (hG := hG))
    (wp_Contains : replica.Quorum.Contains.spec (hG := hG)) :
    replica.sendExcept.spec (hG := hG) := by
  intro r γ γc γm γw N me q dq qs msg m rpc Pm
  wp_start as ⟨#Hrep, Hq, Hsend⟩
  iunfold sp.peerSend at Hsend
  icases Hsend with ⟨#Hmar, HP, #Hm, %Hmm⟩
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  wp_auto
  ihave HL : (∃ pv : w32, "p" ∷ p_ptr ↦ pv ∗ "HP" ∷ Pm ∗
      "Hq" ∷ replica.quorum.qOwn q dq qs ∗
      "%Hp" ∷ ⌜0 ≤ pv.toInt ∧ pv.toInt ≤ N⌝ : IProp netDistGF) $$ [p HP Hq]
  · iexists _; iframe; ipureintro; simp
  have h7 := Hlens.2.2.2
  have hN : sint.Z (W32 (sint.Z (W64 (N : Int)))) = N := by
    match N, h7 with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
    | 6, _ => rfl | 7, _ => rfl
  wp_for HL
  try wp_auto
  rw [hN]
  by_cases hlt : sint.Z pv < N
  · rw [if_pos (by simp [hlt])]
    try wp_auto
    wp_method_call
    wp_call
    try wp_auto
    wp_apply wp_Contains q dq qs pv $$ [$Hq] as Hq
    try wp_auto
    wp_if_destruct
    all_goals first | (try wp_auto); nextp | peerstep
  · rw [if_neg (by simp [hlt])]
    try wp_auto
    rw [if_neg (by simp [hlt])]
    try wp_auto
    iapply HΦ; iframe

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

set_option hygiene false in
/-- After the send: `free` (if any) with the message's resources, then the next round. -/
local macro "freepost" : tactic => `(tactic| (
  try wp_auto
  wp_if_destruct
  · try wp_auto
    wp_for_post
    itrivial
  · iunfold replica.freeOk at Hfree
    icases Hfree with (%Hn | #Hf)
    · exact absurd Hn Hif
    try wp_auto
    wp_bind (App (Val #a.free') (Val #()))
    iapply Hf $$ HP
    inext
    try wp_auto
    wp_for_post
    itrivial))

section proofs2
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

set_option goose.wp.extras true
set_option linter.unusedSectionVars false

theorem replica.NewSender.wp_proof
    (wp_SendMsg : replica.Replica.SendMsgP.spec (hG := hG))
    (wp_SendClientMsg : replica.Replica.SendClientMsgP.spec (hG := hG))
    (wp_sendToAll : replica.sendToAll.spec (hG := hG))
    (wp_sendToAllExcept : replica.sendToAllExcept.spec (hG := hG))
    (wp_sendToQuorum : replica.sendToQuorum.spec (hG := hG))
    (wp_sendExcept : replica.sendExcept.spec (hG := hG)) :
    replica.NewSender.spec (hG := hG) := by
  intro r γ γc γm N
  wp_start as #HSd
  wp_auto
  iapply wp_fupd
  wp_apply chan.wp_make2 (V := replica.SendArg) $$ [] as %sch %γs ⟨#His, %Hcap, Hown⟩
  · ipureintro; decide
  imod start_bag (replica.sendArgP r γ γc γm N) _ sch γs (by simp) $$ His Hown with #Hch
  try wp_auto
  ipersist r
  ipersist s
  wp_apply wp_fork $$ []
  · -- the sender's loop
    wp_auto
    wp_for
    try wp_auto
    wp_apply (wp_bag_receive (V := replica.SendArg)) $$ [$Hch] as %a Ha
    iunfold replica.sendArgP at Ha
    icases Ha with ⟨⟨%γw, %me, #Hrep⟩, %m, %P, #Hmar, HP, #Hm, #Hfree, %Hmw, Hcase⟩
    try wp_auto
    icases Hcase with (%Hc | ⟨%Hc, %dq, %qs, Hq⟩ | %Hc | %Hc)
    · obtain ⟨hst | hst, hpeer⟩ := Hc
      · rw [hst]
        wp_auto
        wp_apply wp_sendToAll r γ γc γm γw N me a.msg' m a.rpc' $$ [HP] as HP
        · isplitl []
          · iexact Hrep
          iunfold sp.peerSend
          isplitl []
          · iexact Hmar
          isplitl [HP]
          · iexact HP
          iframe Hm; ipureintro
          exact ⟨Hmw.1, fun x hx => ⟨hpeer x hx, (Hmw.2 x hx).1, (Hmw.2 x hx).2⟩⟩
        freepost
      · rw [hst]
        wp_auto
        wp_apply wp_sendToAllExcept r γ γc γm γw N me a.id' a.msg' m a.rpc' $$ [HP] as HP
        · isplitl []
          · iexact Hrep
          iunfold sp.peerSend
          isplitl []
          · iexact Hmar
          isplitl [HP]
          · iexact HP
          iframe Hm; ipureintro
          exact ⟨Hmw.1, fun x hx => ⟨hpeer x hx, (Hmw.2 x hx).1, (Hmw.2 x hx).2⟩⟩
        freepost
    · obtain ⟨hst | hst, hpeer⟩ := Hc
      · rw [hst]
        wp_auto
        wp_apply wp_sendToQuorum r γ γc γm γw N me a.quorum' dq qs a.msg' m a.rpc' $$ [HP Hq]
          as ⟨Hq, HP⟩
        · isplitl []
          · iexact Hrep
          iframe Hq
          iunfold sp.peerSend
          isplitl []
          · iexact Hmar
          isplitl [HP]
          · iexact HP
          iframe Hm; ipureintro
          exact ⟨Hmw.1, fun x hx => ⟨hpeer x hx, (Hmw.2 x hx).1, (Hmw.2 x hx).2⟩⟩
        freepost
      · rw [hst]
        wp_auto
        wp_apply wp_sendExcept r γ γc γm γw N me a.quorum' dq qs a.msg' m a.rpc' $$ [HP Hq]
          as ⟨Hq, HP⟩
        · isplitl []
          · iexact Hrep
          iframe Hq
          iunfold sp.peerSend
          isplitl []
          · iexact Hmar
          isplitl [HP]
          · iexact HP
          iframe Hm; ipureintro
          exact ⟨Hmw.1, fun x hx => ⟨hpeer x hx, (Hmw.2 x hx).1, (Hmw.2 x hx).2⟩⟩
        freepost
    · obtain ⟨hst, hpeer, hid0, hidN⟩ := Hc
      rw [hst]
      wp_auto
      wp_apply wp_SendMsg r γ γc γm γw N me a.id' a.rpc' a.msg' m $$ [HP] as HP
      · isplitl []
        · iexact Hrep
        isplitl []
        · iexact Hmar
        isplitl [HP]
        · iexact HP
        iframe Hm; ipureintro
        exact ⟨Hmw.1, fun x hx => ⟨hpeer x hx, (Hmw.2 x hx).1, (Hmw.2 x hx).2⟩, hid0, hidN⟩
      freepost
    · obtain ⟨hst, hcl⟩ := Hc
      rw [hst]
      wp_auto
      wp_apply wp_SendClientMsg r γ γc γm γw N me a.id' a.rpc' a.msg' m $$ [HP] as HP
      · isplitl []
        · iexact Hrep
        isplitl []
        · iexact Hmar
        isplitl [HP]
        · iexact HP
        iframe Hm; ipureintro
        exact ⟨Hmw.1, fun x hx => ⟨hcl x hx, (Hmw.2 x hx).1, (Hmw.2 x hx).2⟩⟩
      freepost
  try wp_auto
  imodintro
  iapply HΦ
  iexists γs; iexact Hch

theorem replica.Sender.SendToAllAndFree.wp_proof : replica.Sender.SendToAllAndFree.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s msg m rpc P f
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk⟩
  ihave Hts := replica.toSend_P γ γc γm msg m rpc P f $$ Hts
  iunfold replica.toSendP at Hts
  icases Hts with ⟨#Hmar, HP, #Hm, #Hf, %Hw⟩
  wp_auto
  wp_apply (wp_bag_send (V := replica.SendArg)) $$ [HP]
  · iframe Hch
    iunfold replica.sendArgP
    isplitr
    · iexists γw, me; iexact Hrep
    iexists (· = m), P
    simp only
    iframe Hmar HP Hm Hf
    isplitr
    · ipureintro; exact Hw
    ileft; ipureintro; exact ⟨by simp, fun x hx => hx ▸ Hk⟩
  try wp_auto
  iapply HΦ; itrivial

theorem replica.Sender.SendToAllAndFreeP.wp_proof :
    replica.Sender.SendToAllAndFreeP.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s msg Pm rpc P f
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk⟩
  iunfold replica.toSendP at Hts
  icases Hts with ⟨#Hmar, HP, #Hm, #Hf, %Hw⟩
  wp_auto
  wp_apply (wp_bag_send (V := replica.SendArg)) $$ [HP]
  · iframe Hch
    iunfold replica.sendArgP
    isplitr
    · iexists γw, me; iexact Hrep
    iexists Pm, P
    simp only
    iframe Hmar HP Hm Hf
    isplitr
    · ipureintro; exact Hw
    ileft; ipureintro; exact ⟨by simp, Hk⟩
  try wp_auto
  iapply HΦ; itrivial

theorem replica.Sender.SendToAllExecptAndFree.wp_proof : replica.Sender.SendToAllExecptAndFree.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s ex msg m rpc P f
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk⟩
  ihave Hts := replica.toSend_P γ γc γm msg m rpc P f $$ Hts
  iunfold replica.toSendP at Hts
  icases Hts with ⟨#Hmar, HP, #Hm, #Hf, %Hw⟩
  wp_auto
  wp_apply (wp_bag_send (V := replica.SendArg)) $$ [HP]
  · iframe Hch
    iunfold replica.sendArgP
    isplitr
    · iexists γw, me; iexact Hrep
    iexists (· = m), P
    simp only
    iframe Hmar HP Hm Hf
    isplitr
    · ipureintro; exact Hw
    ileft; ipureintro; exact ⟨by simp, fun x hx => hx ▸ Hk⟩
  try wp_auto
  iapply HΦ; itrivial

theorem replica.Sender.SendToQuorumAndFree.wp_proof : replica.Sender.SendToQuorumAndFree.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s q dq qs msg m rpc P f
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk, Hq⟩
  ihave Hts := replica.toSend_P γ γc γm msg m rpc P f $$ Hts
  iunfold replica.toSendP at Hts
  icases Hts with ⟨#Hmar, HP, #Hm, #Hf, %Hw⟩
  wp_auto
  wp_apply (wp_bag_send (V := replica.SendArg)) $$ [HP Hq]
  · iframe Hch
    iunfold replica.sendArgP
    isplitr
    · iexists γw, me; iexact Hrep
    iexists (· = m), P
    simp only
    iframe Hmar HP Hm Hf
    isplitr
    · ipureintro; exact Hw
    iright; ileft; iframe; ipureintro; exact ⟨by simp, fun x hx => hx ▸ Hk⟩
  try wp_auto
  iapply HΦ; itrivial

theorem replica.Sender.SendExceptAndFree.wp_proof : replica.Sender.SendExceptAndFree.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s q dq qs msg m rpc P f
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk, Hq⟩
  ihave Hts := replica.toSend_P γ γc γm msg m rpc P f $$ Hts
  iunfold replica.toSendP at Hts
  icases Hts with ⟨#Hmar, HP, #Hm, #Hf, %Hw⟩
  wp_auto
  wp_apply (wp_bag_send (V := replica.SendArg)) $$ [HP Hq]
  · iframe Hch
    iunfold replica.sendArgP
    isplitr
    · iexists γw, me; iexact Hrep
    iexists (· = m), P
    simp only
    iframe Hmar HP Hm Hf
    isplitr
    · ipureintro; exact Hw
    iright; ileft; iframe; ipureintro; exact ⟨by simp, fun x hx => hx ▸ Hk⟩
  try wp_auto
  iapply HΦ; itrivial

theorem replica.Sender.SendToClientAndFree.wp_proof : replica.Sender.SendToClientAndFree.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s cid msg m rpc P f
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk⟩
  ihave Hts := replica.toSend_P γ γc γm msg m rpc P f $$ Hts
  iunfold replica.toSendP at Hts
  icases Hts with ⟨#Hmar, HP, #Hm, #Hf, %Hw⟩
  wp_auto
  wp_apply (wp_bag_send (V := replica.SendArg)) $$ [HP]
  · iframe Hch
    iunfold replica.sendArgP
    isplitr
    · iexists γw, me; iexact Hrep
    iexists (· = m), P
    simp only
    iframe Hmar HP Hm Hf
    isplitr
    · ipureintro; exact Hw
    iright; iright; iright; ipureintro; exact ⟨by simp, fun x hx => hx ▸ Hk⟩
  try wp_auto
  iapply HΦ; itrivial

theorem replica.Sender.SendToAndFree.wp_proof : replica.Sender.SendToAndFree.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s id msg m rpc P f
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk⟩
  ihave Hts := replica.toSend_P γ γc γm msg m rpc P f $$ Hts
  iunfold replica.toSendP at Hts
  icases Hts with ⟨#Hmar, HP, #Hm, #Hf, %Hw⟩
  wp_auto
  wp_apply (wp_bag_send (V := replica.SendArg)) $$ [HP]
  · iframe Hch
    iunfold replica.sendArgP
    isplitr
    · iexists γw, me; iexact Hrep
    iexists (· = m), P
    simp only
    iframe Hmar HP Hm Hf
    isplitr
    · ipureintro; exact Hw
    iright; iright; ileft; ipureintro; exact ⟨by simp, fun x hx => hx ▸ Hk.1, Hk.2.1, Hk.2.2⟩
  try wp_auto
  iapply HΦ; itrivial

theorem replica.Sender.SendToAll.wp_proof
    (wp_AndFree : replica.Sender.SendToAllAndFree.spec (hG := hG)) :
    replica.Sender.SendToAll.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s  msg m rpc P
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk⟩
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply wp_AndFree r γ γc γm γw N me γs s  msg m rpc $$ [Hts]
  · iframe Hrep Hch
    iframe
    ipureintro; exact Hk
  iapply HΦ; itrivial

theorem replica.Sender.SendToAllP.wp_proof
    (wp_AndFree : replica.Sender.SendToAllAndFreeP.spec (hG := hG)) :
    replica.Sender.SendToAllP.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s msg Pm rpc P
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk⟩
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply wp_AndFree r γ γc γm γw N me γs s msg Pm rpc $$ [Hts]
  · iframe Hrep Hch
    iframe
    ipureintro; exact Hk
  iapply HΦ; itrivial

theorem replica.Sender.SendToAllExecpt.wp_proof
    (wp_AndFree : replica.Sender.SendToAllExecptAndFree.spec (hG := hG)) :
    replica.Sender.SendToAllExecpt.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s ex msg m rpc P
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk⟩
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply wp_AndFree r γ γc γm γw N me γs s ex msg m rpc $$ [Hts]
  · iframe Hrep Hch
    iframe
    ipureintro; exact Hk
  iapply HΦ; itrivial

theorem replica.Sender.SendToQuorum.wp_proof
    (wp_AndFree : replica.Sender.SendToQuorumAndFree.spec (hG := hG)) :
    replica.Sender.SendToQuorum.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s q dq qs msg m rpc P
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk, Hq⟩
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply wp_AndFree r γ γc γm γw N me γs s q dq qs msg m rpc $$ [Hts Hq]
  · iframe Hrep Hch
    iframe
    ipureintro; exact Hk
  iapply HΦ; itrivial

theorem replica.Sender.SendExcept.wp_proof
    (wp_AndFree : replica.Sender.SendExceptAndFree.spec (hG := hG)) :
    replica.Sender.SendExcept.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s q dq qs msg m rpc P
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk, Hq⟩
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply wp_AndFree r γ γc γm γw N me γs s q dq qs msg m rpc $$ [Hts Hq]
  · iframe Hrep Hch
    iframe
    ipureintro; exact Hk
  iapply HΦ; itrivial

theorem replica.Sender.SendToClient.wp_proof
    (wp_AndFree : replica.Sender.SendToClientAndFree.spec (hG := hG)) :
    replica.Sender.SendToClient.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s cid msg m rpc P
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk⟩
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply wp_AndFree r γ γc γm γw N me γs s cid msg m rpc $$ [Hts]
  · iframe Hrep Hch
    iframe
    ipureintro; exact Hk
  iapply HΦ; itrivial

theorem replica.Sender.SendTo.wp_proof
    (wp_AndFree : replica.Sender.SendToAndFree.spec (hG := hG)) :
    replica.Sender.SendTo.spec (hG := hG) := by
  intro r γ γc γm γw N me γs s id msg m rpc P
  wp_start as ⟨#Hrep, #Hch, Hts, %Hk⟩
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply wp_AndFree r γ γc γm γw N me γs s id msg m rpc $$ [Hts]
  · iframe Hrep Hch
    iframe
    ipureintro; exact Hk
  iapply HΦ; itrivial

end proofs2

end Perennial.github_com.imdea_software.swiftpaxos
