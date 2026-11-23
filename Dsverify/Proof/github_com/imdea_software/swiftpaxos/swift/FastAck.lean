/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/FastAck.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `r.fastAckFromLeader(msg, desc)` (spec: Proof/swift/AcksSpecs.lean; round 10,
notes/prove-swift.md §16): `desc.afterPropagate.Call(closure)` with the condition's state
`proposeHalf`; the closure's spec (`closureOk`), and at the leader with a false condition its
no-op spec (the ack is of an earlier ballot: its witness of the current ballot would make the
row pre-accepted, `swift.preacc_row`, hence `propose ≠ nil`, `rowAcc`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepEqualsPerm
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

set_option hygiene false in
/-- `descDone` back from its unpacked parts (the names of the closure's retired case). -/
macro "repackDone" : tactic => `(tactic| (
  ihave Hsh := Hshb $$ Hst HFQ HrdR Hpin
  iunfold swift.descDone
  iunfold swift.descGone
  iframe Hex Hret
  isplitr
  · ipureintro; exact Hsq
  iexists qe, bw, stp, rcp; iframe Hsh; iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe
  ipureintro; exact Hbw))

set_option hygiene false in
/-- `ocfRes0` back from its unpacked parts (the closure's owner case, round 33). -/
macro "packO0" : tactic => `(tactic| (
  ihave Hocf0 : swift.ocfRes0 d $$ [Hoapf Hoocf HPc Hosb]
  · iunfold swift.ocfRes0; iexists cf0, cond0; iframe Hcond0; iunfold swift.ocfRes
    iframe Hoapf Hoocf HPc Hosb))

set_option hygiene false in
/-- L2 (item 4): `ghostAccept(msg.Ballot, msg.CmdId)` with the acceptance's update `Hacc` (a
`swift.ghostUpd` at `b`, `x`), giving back its result's parts. -/
macro "ghostAcc" : tactic => `(tactic| (
  ihave #Hng := swift.DC.ctx_ng c $$ Hctx
  ihave #Hcpkg : isPkgInit (PROP := IProp netDistGF)
    pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
  · iPkgInit
  try wp_auto
  wp_bind (App (App (Val (@! swift.ghostAccept)) (Val _)) (Val _))
  iapply (swift.wp_ghostAccept c.γ c.k fa.Ballot' fa.CmdId' _) $$ [Hacc]
  · iframe #
    isplitr
    · ipureintro; rw [← hbb]; exact Hbw.2
    rw [show sp.bal fa.Ballot' = b by rw [← hbb]; exact Hbw.1, Hx]
    iexact Hacc
  inext
  iintro ⟨Het, %rv', Htok, %Hrv', #Hacc⟩
  try wp_auto))

section repPreAdopt
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable [swift.Assumptions]

/-- `repPre` when a follower adopts the leader's dependencies (round 47, `fastAckFromLeader`'s
acceptance): the new `D` only needs `replyPre`'s bound; the leader's clauses are their left
disjuncts. -/
theorem swift.repPre_adopt (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv dv' : swift.DescV)
    (h1 : dv'.propose = dv.propose) (h2 : dv'.c = dv.c) (h3 : dv'.Hs = dv.Hs)
    (hr : r ≠ sp.leaderOf N b) (hD : dv'.D.length < 2 ^ 62) :
    swift.repPre γ N r b x dv ⊢ swift.repPre γ N r b x dv' := by
  iintro H
  iunfold swift.repPre at H
  iunfold swift.repPre
  icases H with (%Hn | ⟨Hrp, %Hwf, -, #HpI⟩)
  · ileft; ipureintro; rw [h1]; exact Hn
  iright
  iunfold swift.replyPre at Hrp
  icases Hrp with ⟨%Hs, %p, %w, %mu, %addr, #Hp, #Hcl, %Hpure, -⟩
  isplitl [Hp Hcl]
  · iunfold swift.replyPre
    iexists Hs, p, w, mu, addr
    rw [h1]
    iframe Hp Hcl
    isplitr
    · ipureintro; exact ⟨by rw [h3]; exact Hpure.1, Hpure.2.1, Hpure.2.2.1, hD⟩
    ileft; ipureintro; exact hr
  isplitr
  · ipureintro; rw [h2]; exact Hwf
  isplitr
  · iunfold swift.ldrPrefix; ileft; ipureintro; exact hr
  rw [h1, h2]; iexact HpI

end repPreAdopt

set_option hygiene false in
/-- `descOwn` back from its unpacked parts (the names of the closure's owner case). -/
macro "repackOwnF" : tactic => `(tactic| (
  try (ihave Hsh := Hshb $$ Hst HFQ HrdR Hpin)
  try (ihave Htok := swift.rowTokO_of2 c b x dv rv $$ Htok Hslt)
  iunfold swift.descOwn
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS
  iunfold swift.setR
  iunfold swift.descSt
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh HRC Hd Htok Hcom Hra HrP HsF HfF HdF Hcore HDo Hpw Hdw HsB
  isplitl [Hbal HStf Hrcf Het Hxe]
  · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp))

set_option hygiene false in
/-- The accepted owner state's lent part (`setR … true`) from its unpacked parts (the
acceptance path's names; `dv'` the descriptor's values after `phase := ACCEPT` and the
dependencies' adoption, `rv'` the accepted row). -/
macro "packAccR" dv':term : tactic => `(tactic| (
  iunfold swift.setR
  iunfold swift.descSt
  iexists qe, bw, stp, rcp, $dv', rv'
  ihave Htok := swift.rowTokO_of2 c b x $dv' rv' $$ Htok Hslt
  iframe Hsh HRC Htok HsF HfF HdF HDo
  isplitl [Hbal HStf Hrcf Het Hxe]
  · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
  isplitl [Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs]
  · iunfold swift.descF; iframe Hph' Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs HD HHs Hmb HsL
    ipureintro; exact Hop
  isplitl [Hcom]
  · rw [Hrv'.2.1]; iexact Hcom
  isplitr
  · isplitr
    · iunfold swift.rowAcc; isplitr
      · iright; iexact Hacc
      isplitr
      · ipureintro; intro _; exact Hpn
      iexact Hpp
    -- round 47 (46-2): the new values' `repPre` (`HrPa`, made by the caller)
    iexact HrPa
  isplitr
  · ipureintro; intro h; simp [swift.phCOMMIT] at h
  isplitr
  · iapply swift.phaseWhy_ne1; show (W64 2 : w64) ≠ W64 1; decide
  isplitr
  · iexact Hdw'
  isplitr
  · ipureintro; exact ⟨swift.rowPhaseOk_acc c.N c.r b _ rv' Hpn rfl Hrv'.2.2.2, Hrp.2⟩
  iframe HsB
  iunfold swift.descCore; iexists null, sl; iframe Hwa Hsl
  ileft; ipureintro; rfl))

set_option hygiene false in
/-- `r.delivered.Has(msgCmdId.String())` with any result (the names of the closure). -/
macro "hasAny" : tactic => `(tactic| (
  wp_apply (wp_String c) $$ [msgCmdId] as msgCmdId
  · iexact msgCmdId
  ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ∗
      (github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ={⊤}=∗ swift.ownRdr c.rp c.γdl)) $$ [HrdR]
  · iapply swift.ownRdr_take; iframe Hdm HrdR
  iapply fupd_wp
  imod Hb with ⟨Hrdr, HbackR⟩
  imodintro
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType github_com.orcaman.concurrent_map.ConcurrentMap.ty)
    (m := go!"Has")]
  try wp_auto
  wp_apply (wp_HasV dm c.γdl _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
      (fun _ => iprop(True))) $$ [Hrdr] as %dl ⟨Hrdr, -⟩
  · iframe Hrdr
    imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
      swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
    iunfold swift.delivInv at Hi
    icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
    imodintro
    iexists M
    iframe HV
    iintro HV
    imod Hclose $$ [HV HXi HXeD HMx HXx] with -
    · inext; iunfold swift.delivInv; iexists M, bX', X', Mx, rm; iframe; ipureintro; exact HM
    imodintro
    itrivial
  iapply fupd_wp
  imod HbackR $$ Hrdr with HrdR
  imodintro))

set_option hygiene false in
/-- `hasAny` with the owner's pin `Hpin` at `q` (round 55, 53-3'): a hit is an execution of `x`
in `b` (`Hdlx`: `swift.delivFz_exIn`, `str` injective). -/
macro "hasDl" q:term : tactic => `(tactic| (
  wp_apply (wp_String c) $$ [msgCmdId] as msgCmdId
  · iexact msgCmdId
  ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ∗
      (github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ={⊤}=∗ swift.ownRdr c.rp c.γdl)) $$ [HrdR]
  · iapply swift.ownRdr_take; iframe Hdm HrdR
  iapply fupd_wp
  imod Hb with ⟨Hrdr, HbackR⟩
  imodintro
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType github_com.orcaman.concurrent_map.ConcurrentMap.ty)
    (m := go!"Has")]
  try wp_auto
  wp_apply (wp_HasV dm c.γdl _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
      (fun ok => iprop(swift.epochPinQ c.γxp $q b ∗ (⌜ok = false⌝ ∨ swift.exIn c.γxm b x))))
      $$ [Hrdr Hpin] as %dl ⟨Hrdr, Hpin, #Hdlx⟩
  · iframe Hrdr
    imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
      swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
    iunfold swift.delivInv at Hi
    icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
    ihave ⟨Hpin, HXeD, %Hag⟩ := swift.epochPinQ_agree c.γxp $q b bX' rm $$ [Hpin HXeD]
    · iframe Hpin HXeD
    obtain ⟨rfl, rfl⟩ := Hag
    icases HXx with ⟨HXx, HFz⟩
    ihave ⟨HFz, #Hdlx⟩ : iprop(swift.delivFz c.γx c.γxp c.γxm bX' X' Mx ∗
        (⌜(M.lookup (c.str fa.CmdId')).isSome = false⌝ ∨ swift.exIn c.γxm bX' x)) $$ [HFz]
    · cases hs : (M.lookup (c.str fa.CmdId')).isSome
      · iframe HFz; ileft; ipureintro; rfl
      · have hs' : (M.lookup (c.str x)).isSome := by rw [← Hx]; exact hs
        ihave ⟨HFz, #Hex⟩ := swift.delivFz_exIn c.str hinjc c.γx c.γxp c.γxm M bX' X' Mx false HM x
          hs' $$ HFz
        iframe HFz; iright; iexact Hex
    imodintro
    iexists M
    iframe HV
    iintro HV
    imod Hclose $$ [HV HXi HXeD HMx HXx HFz] with -
    · inext; iunfold swift.delivInv; iexists M, bX', X', Mx, false; iframe; ipureintro; exact HM
    imodintro
    iframe Hpin Hdlx
  iapply fupd_wp
  imod HbackR $$ Hrdr with HrdR
  imodintro))

set_option hygiene false in
/-- `r.delivered.Has(msgCmdId.String())` is true when `x` was executed in the epoch (`Hex`,
the caller's pin `Hpin`, at the fraction `q`: round 43, table §3R11b). -/
macro "hasGone" q:term : tactic => `(tactic| (
  wp_apply (wp_String c) $$ [msgCmdId] as msgCmdId
  · iexact msgCmdId
  ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ∗
      (github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ={⊤}=∗ swift.ownRdr c.rp c.γdl)) $$ [HrdR]
  · iapply swift.ownRdr_take; iframe Hdm HrdR
  iapply fupd_wp
  imod Hb with ⟨Hrdr, HbackR⟩
  imodintro
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType github_com.orcaman.concurrent_map.ConcurrentMap.ty)
    (m := go!"Has")]
  try wp_auto
  wp_apply (wp_HasV dm c.γdl _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
      (fun ok => iprop(⌜ok = true⌝ ∗ swift.epochPinQ c.γxp $q b))) $$ [Hrdr Hpin] as %dl ⟨Hrdr, %Hdl, Hpin⟩
  · iframe Hrdr
    imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
      swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
    iunfold swift.delivInv at Hi
    icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
    ihave ⟨Hpin, HXeD, %Hag⟩ := swift.epochPinQ_agree c.γxp $q b bX' rm $$ [Hpin HXeD]
    · iframe Hpin HXeD
    obtain ⟨rfl, rfl⟩ := Hag
    ihave %Hin := swift.exIn_delivered c.str c.γxm bX' x M X' Mx HM $$ [Hex HMx]
    · iframe Hex HMx
    imodintro
    iexists M
    iframe HV
    iintro HV
    imod Hclose $$ [HV HXi HXeD HMx HXx] with -
    · inext; iunfold swift.delivInv; iexists M, bX', X', Mx, false; iframe; ipureintro; exact HM
    imodintro
    isplitr
    · ipureintro; rw [Hx]; exact Hin
    iexact Hpin
  iapply fupd_wp
  imod HbackR $$ Hrdr with HrdR
  imodintro
  subst Hdl))

set_option hygiene false in
/-- `hasAny` with the reader of the lent state `HR` (round 25, SW4). -/
macro "hasAnyHR" : tactic => `(tactic| (
  ihave ⟨HrdR, HrdBk⟩ := swift.setR_rdr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $$ HR
  hasAny
  ihave HR := HrdBk $$ HrdR))

set_option hygiene false in
/-- `hasGone` with the reader of the retired state's epoch part `Hgrd` (round 25, SW4). -/
macro "hasGoneGrd" : tactic => `(tactic| (
  ihave ⟨%qp, HrdR, Hpin, HrdBk⟩ := swift.grd_rdrP _ _ _ $$ Hgrd
  hasGone qp
  ihave Hgrd := HrdBk $$ HrdR Hpin))

set_option hygiene false in
/-- At the leader, the deferred closure (`r.leader() == r.Id`: returns) and the deferred
`markAccepted` (the ballot's share `Hbal` of value `bw'`). -/
macro "leaderDefers" : tactic => `(tactic| (
  have hL' : BitVec.srem bw' (W32 (sint.Z (W64 (c.N : Int)))) = me :=
    Classical.byContradiction fun h =>
      swift.rid_ne_leader me bw' c.N b hN Hbw'.1 Hbw'.2 Hids.2.1 (fun e => h e.symm)
        (by rw [Hids.1]; exact hLr hL)
  wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw' _ c.N hN) $$ [Hbal] as Hbal
  · iframe Hbal Hrr HN
  try wp_auto
  rw [decide_eq_true hL']
  try wp_auto
  wp_apply (wp_mark c b fa.CmdId') $$ [Hpin] as Hpin
  · iframe Hctx Hpin; rw [Hx]; iexact Hacc
  try wp_auto))

set_option hygiene false in
/-- The end at the leader from the owner state (the slow set lent: `HR`, `HdS`). -/
macro "leaderEndOwn" : tactic => `(tactic| (
  ihave ⟨%qe', %bw', Hbal, HsF, HfF, %Hbw', HrdL, Hpin, HRb⟩ := swift.setR_openR $$ HR
  leaderDefers
  ihave HR := HRb $$ Hbal HsF HfF HrdL Hpin
  iapply HΨ; ileft; iframe Hocf0
  iunfold swift.descOwn
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS HR))

set_option hygiene false in
/-- The end at the leader from a retired descriptor (`Hex`, `Hgrd`). -/
macro "leaderEndGone" : tactic => `(tactic| (
  icases Hgrd with ⟨%qe', %bw', %stp', %rcp', Hrd', Hsh'⟩
  iunfold swift.epochRd at Hrd'
  icases Hrd' with ⟨Hbal, HStf', Hrcf', Het', Hxe', %Hbw'⟩
  ihave ⟨Hpin, Hshp⟩ := swift.shOwnR_pin c d b qe' $$ Hsh'
  leaderDefers
  ihave Hsh' := Hshp $$ Hpin
  iapply HΨ; iright
  iunfold swift.descDone
  iunfold swift.descGone
  iframe Hex Hret
  isplitr
  · ipureintro; exact Hsq
  iexists qe', bw', stp', rcp'; iframe Hsh'; iunfold swift.epochRd
  iframe Hbal HStf' Hrcf' Het' Hxe'
  ipureintro; exact Hbw'))

set_option hygiene false in
/-- The owner state from the slow set's lent state `HR` and data `HdS`. -/
macro "packOwn" : tactic => `(tactic| (
  ihave Hown : swift.descOwn c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) $$ [HdS HR]
  · iunfold swift.descOwn
    iexists s, f, qS, qF, szS, szF, memS, memF, hd
    iframe HhS HhF HdS HR))

set_option hygiene false in
/-- The retired state from `Hex`, `Hgrd`, `Hst`. -/
macro "packDone" : tactic => `(tactic| (
  ihave Hdone : swift.descDone c b x d $$ [Hgrd Hret]
  · iunfold swift.descDone; iunfold swift.descGone; iframe Hex Hgrd Hret; ipureintro; exact Hsq))

set_option hygiene false in
/-- At a follower, the deferred closure on a retired descriptor (`Hdone`: `delivered.Has` is
true, it returns) and the deferred `markAccepted`. -/
macro "follDefersGone" : tactic => `(tactic| (
  iunfold swift.descDone at Hdone
  icases Hdone with Hgone
  iunfold swift.descGone at Hgone
  icases Hgone with ⟨%Hsq, #Hex, Hret, %qe', %bw', %stp', %rcp', Hrd', Hsh'⟩
  iunfold swift.epochRd at Hrd'
  icases Hrd' with ⟨Hbal, HStf', Hrcf', Het', Hxe', %Hbw'⟩
  have hL' : ¬ (BitVec.srem bw' (W32 (sint.Z (W64 (c.N : Int)))) = me) := fun h =>
    hnL (by rw [← Hids.1, ← h]; exact swift.rid_leader bw' c.N b hN Hbw'.1 Hbw'.2)
  wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw' _ c.N hN) $$ [Hbal] as Hbal
  · iframe Hbal Hrr HN
  try wp_auto
  rw [decide_eq_false hL']
  try wp_auto
  ihave ⟨HrdR, Hpin, Hshr⟩ := swift.shOwnR_rdrP c d b qe' $$ Hsh'
  hasGone qe'
  try wp_auto
  wp_apply (wp_mark c b fa.CmdId') $$ [Hpin] as Hpin
  · iframe Hctx Hpin; rw [Hx]; iexact Hacc
  ihave Hsh' := Hshr $$ HrdR Hpin
  try wp_auto
  iapply HΨ; iright
  iunfold swift.descDone; iunfold swift.descGone; iframe Hex Hret
  isplitr
  · ipureintro; exact Hsq
  iexists qe', bw', stp', rcp'; iframe Hsh'; iunfold swift.epochRd
  iframe Hbal HStf' Hrcf' Het' Hxe'
  ipureintro; exact Hbw'))

set_option hygiene false in
/-- The deferred `markAccepted` and the end from the owner state (`Hback`, `Hbal`). -/
macro "follMarkOwn" : tactic => `(tactic| (
  wp_apply (wp_mark c b fa.CmdId') $$ [Hpin] as Hpin
  · iframe Hctx Hpin; rw [Hx]; iexact Hacc
  try wp_auto
  iapply HΨ; ileft; iframe Hocf0
  iapply Hback $$ Hbal HrdR Hpin))

set_option hygiene false in
/-- At a follower, the deferred closure from the owner state (`Hown`) with `sendSlowAck` true
(it returns or does nothing), and the deferred `markAccepted`. -/
macro "follDefersOwnT" : tactic => `(tactic| (
  ihave ⟨%qe', %bw', Hbal, %Hbw', HrdR, Hpin, Hback⟩ := swift.descOwn_ballotR $$ Hown
  have hL' : ¬ (BitVec.srem bw' (W32 (sint.Z (W64 (c.N : Int)))) = me) := fun h =>
    hnL (by rw [← Hids.1, ← h]; exact swift.rid_leader bw' c.N b hN Hbw'.1 Hbw'.2)
  wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw' _ c.N hN) $$ [Hbal] as Hbal
  · iframe Hbal Hrr HN
  try wp_auto
  rw [decide_eq_false hL']
  try wp_auto
  hasAny
  cases dl <;> (try wp_auto) <;> follMarkOwn))

set_option hygiene false in
/-- At a follower, the deferred closure from the owner state (`Hown`) with `sendSlowAck` false:
with `optExec` and different checksums, the light slow ack to the client; then the deferred
`markAccepted`. -/
macro "follDefersOwnF" : tactic => `(tactic| (
  ihave ⟨%qe', %bw', Hbal, %Hbw', HrdR, Hpin, Hback⟩ := swift.descOwn_ballotR $$ Hown
  have hL' : ¬ (BitVec.srem bw' (W32 (sint.Z (W64 (c.N : Int)))) = me) := fun h =>
    hnL (by rw [← Hids.1, ← h]; exact swift.rid_leader bw' c.N b hN Hbw'.1 Hbw'.2)
  wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw' _ c.N hN) $$ [Hbal] as Hbal
  · iframe Hbal Hrr HN
  try wp_auto
  rw [decide_eq_false hL']
  try wp_auto
  hasAny
  cases dl
  · try wp_auto
    cases oe
    · try wp_auto
      follMarkOwn
    · try wp_auto
      icases HCs with ⟨%hsl, #HCs'⟩
      wp_apply (wp_SHA dv.hs fa.Checksum' dv.Hs hsl) as %bb -
      · iframe HHs HCs'
      cases bb
      · try wp_auto
        ihave #Hcs2 := Hcs
        iStructNamedPrefix Hcs2 "CS"
        try wp_auto
        rw [MethodUnfold.method_unfold (t := go.GoType.PointerType replica.Sender.ty)
          (m := go!"SendToClient")]
        try wp_auto
        have hnl' : sp.rid me ≠ sp.leaderOf c.N (sp.bal bw') := by rw [Hids.1, Hbw'.1]; exact hnL
        wp_apply (wp_sendc c.rr c.γ c.γc c.γm c.γw c.N me γs sn fa.CmdId'.ClientId'
            (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #«$r0_ptr»)
            (.lightSlowAck ⟨me, bw', toCmdId x⟩) csv.lightSlowAckRPC'
            iprop(«$r0_ptr» ↦ swift.MLightSlowAck.mk me bw' fa.CmdId')) $$ [«$r0»]
        · iframe Hrep Hsb
          unfold replica.toSend
          isplitl
          · isplitr
            · iapply (hms «$r0_ptr» (swift.MLightSlowAck.mk me bw' fa.CmdId') ⟨me, bw', toCmdId x⟩
                ⟨rfl, rfl, by rw [Hx]⟩)
            isplitl [«$r0»]
            · iframe
            isplitr
            · iapply (swift.lightSlowAckOk_intro c.γ c.γc c.γm c.N fr lg me bw' (toCmdId x)
                ⟨Hids.2.1, Hbw'.2⟩ hnl')
              iframe Hcfg; rw [Hids.1, Hbw'.1]; iexact Hacc
            isplitr
            · unfold replica.freeOk; ileft; ipureintro; rfl
            ipureintro; refine ⟨trivial, ?_⟩; rw [Hcodes.2.2.2.1]; rfl
          ipureintro; simp only [sp.Msg.isToClient]; rw [← Hx]; rfl
        try wp_auto
        follMarkOwn
      · try wp_auto
        follMarkOwn
  · try wp_auto
    follMarkOwn))

set_option hygiene false in
/-- The batcher's operation of the light slow ack at `«$r0_ptr»` (read-only, `#«$r0»`). -/
macro "slowOp" : tactic => `(tactic| (
  iunfold swift.slowOpP
  iexists c.N, me, (swift.MLightSlowAck.mk me bw' fa.CmdId'), (⟨me, bw', toCmdId x⟩ : sp.SlowAck)
  iframe «$r0»
  isplitr
  · iunfold swift.sendCtxN; iexists c.rr, sn, c.γw, γs, csv; iframe Hrr Hrep Hsn Hsb Hcs
    ipureintro; exact Hcodes
  isplitr
  · ipureintro; exact ⟨⟨rfl, rfl, by rw [Hx]⟩, rfl⟩
  iapply (swift.lightSlowAckOk_intro c.γ c.γc c.γm c.N fr lg me bw' (toCmdId x)
    ⟨Hids.2.1, Hbw'.2⟩ (by rw [Hids.1, Hbw'.1]; exact hnL))
  iframe Hcfg; rw [Hids.1, Hbw'.1]; iexact Hacc))

set_option hygiene false in
/-- The light slow ack (allocated: `«$r0»`) to the batcher (`optExec`: its client variant). -/
macro "batchSend" : tactic => `(tactic| (
  ipersist «$r0»
  cases oe <;> (try wp_auto) <;> (first
    | (wp_apply (wp_SLA c.γ c.γc c.γm c.rp bt «$r0_ptr») $$ []
       · iframe HbH; slowOp)
    | (wp_apply (wp_SLAC c.γ c.γc c.γm c.rp bt «$r0_ptr» fa.CmdId'.ClientId') $$ []
       · iframe HbH; slowOp))))

set_option hygiene false in
/-- `sendSlowAck`, owner, not delivered: `slowPath`, the light slow ack to the batcher and to
`handleLightSlowAck`, then the deferred functions. -/
macro "tailTnd" : tactic => `(tactic| (
  ihave ⟨%sl0, Hsl, HRb⟩ := swift.setR_slowPath $$ HR
  try wp_auto
  ihave HR := HRb $$ %true Hsl
  ihave ⟨%qe', %bw', Hbal, HsF, HfF, %Hbw', HRb⟩ := swift.setR_open $$ HR
  try wp_auto
  ihave HR := HRb $$ Hbal HsF HfF
  batchSend
  all_goals (
    try wp_auto
    packOwn
    iunfold swift.ocfRes0 at Hocf0
    icases Hocf0 with ⟨%cf1, %cond1, Hocfr1, #Hcond1⟩
    wp_apply (wp_lsa c γd d x b iprop(swift.descCore c d x b ∗ Do) «$r0_ptr»
      (swift.MLightSlowAck.mk me bw' fa.CmdId') cf1 cond1 [] true) $$ [Hown Hocfr1]
      as Hres
    · ihave #Hufp := swift.ackCtx_ufp c $$ Hack
      iframe Hctx Hufp Hown Hocfr1 «$r0»
      isplitr
      · ipureintro; exact Hx
      iunfold swift.ackWhy; iright; ipureintro; rw [Hids.1]; exact hnL
    try wp_auto
    icases Hres with (⟨Hown, Hocfr1⟩ | Hdone)
    · ihave Hocf0 : swift.ocfRes0 d $$ [Hocfr1]
      · iunfold swift.ocfRes0; iexists cf1, cond1; iframe Hocfr1 Hcond1
      follDefersOwnT
    · follDefersGone)))

set_option hygiene false in
/-- `sendSlowAck`, owner, delivered: the light slow ack to the batcher, then the deferred
functions. -/
macro "tailTd" : tactic => `(tactic| (
  ihave ⟨%qe', %bw', Hbal, HsF, HfF, %Hbw', HRb⟩ := swift.setR_open $$ HR
  try wp_auto
  ihave HR := HRb $$ Hbal HsF HfF
  batchSend
  all_goals (
    try wp_auto
    packOwn
    follDefersOwnT)))

set_option hygiene false in
/-- `sendSlowAck`, retired: the light slow ack to the batcher, then the deferred functions. -/
macro "tailTgone" : tactic => `(tactic| (
  icases Hgrd with ⟨%qe', %bw', %stp', %rcp', Hrd', Hsh'⟩
  iunfold swift.epochRd at Hrd'
  icases Hrd' with ⟨Hbal, HStf', Hrcf', Het', Hxe', %Hbw'⟩
  try wp_auto
  batchSend
  all_goals (
    try wp_auto
    ihave Hgrd : iprop(∃ (q : Qp) (bw : w32) (stp rcp : Loc),
        swift.epochRd c.γe c.γxe c.rp c.rr q b bw stp rcp ∗
        swift.shOwnR c d b q) $$ [Hbal HStf' Hrcf' Het' Hxe' Hsh']
    · iexists qe', bw', stp', rcp'; iframe Hsh'; iunfold swift.epochRd
      iframe Hbal HStf' Hrcf' Het' Hxe'
      ipureintro; exact Hbw'
    packDone
    follDefersGone)))

set_option hygiene false in
/-- At a follower, the two `Add`s of the leader's ack (after the acceptance; `dv'` the
descriptor's values) and the `delivered` checks; then `tOwnV` (owner, `delivered` any),
`tOwnD` (owner, delivered) or `tGone` (retired). -/
macro "follAdds" dv':term "own" tOwnV:tactic "ownd" tOwnD:tactic "gone" tGone:tactic : tactic => `(tactic| (
  try (ihave Hsh := Hshb $$ Hst HFQ HrdR Hpin)
  packO0
  ihave HR : swift.setR c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) s f qF szF memF
      hd true $$ [Hsh HRC Hcmd Hdep Hhs Hprop Hseq Hmsgs Hph' Htok Hslt Hcom HsF HfF HdF HDo Hbal HStf
      Hrcf Het Hxe Hwa Hsl]
  · -- round 47 (46-2): `repPre` at the new values (`dep` adopted only here, at a follower)
    ihave #HrPa : swift.repPre c.γ c.N c.r b x $dv' $$ []
    · first
        | (iapply (swift.repPre_congr c.γ c.N c.r b x dv $dv' rfl rfl rfl rfl); iexact HrP)
        | (iapply (swift.repPre_adopt c.γ c.N c.r b x dv $dv' rfl rfl rfl hnL hDl); iexact HrP)
    packAccR $dv'
  ihave HR := swift.setR_give $$ [HR Hocf0]
  · iframe HR Hocf0
  ihave #HhSq := swift.descOwn_hdS c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do)
    iprop(iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) s f qS qF szS szF memS memF hd
    (swift.ocf0Dc_ok d _) $$ [HhS HhF]
  · iframe HhS HhF
  ihave #HhFq := swift.descOwn_hdF c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do)
    iprop(iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) s f qS qF szS szF memS memF hd
    (swift.ocf0Dc_ok d _) $$ [HhS HhF]
  · iframe HhS HhF
  wp_apply (wp_Add s qS szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True)
      (swift.setR c RC MP γd d x b iprop(iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) s f
        qF szF memF hd true)
      (swift.descGone c b x d) hd fa.Replica' true
      (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)) $$ [HdS HR]
    as %added ⟨-, Hres⟩
  · iframe HdS HR HhSq
    isplitr
    · imodintro; iintro HR; isplitl []; · itrivial
      iintro -; iexact HR
    simp only [↓reduceIte]
    isplitr
    · ipureintro; intro h; cases h
    iunfold swift.leadAckP; iexists l, fa; iframe Hl
    isplitr
    · ipureintro; exact ⟨rfl, Hx, by rw [← hbb]; exact Hbw.1, by rw [← hbb]; exact Hbw.2⟩
    isplitr
    · iexists _; iexact HDep
    iexact Hacc
  icases Hres with (⟨HdS, HR⟩ | Hgone)
  · hasAnyHR
    cases dl
    · wp_auto
      ihave ⟨HR, HdF⟩ := swift.setR_swap $$ [HR HdS]
      · iframe HR HdS
      ihave ⟨%qe', %bw', Hbal, HsF, HfF, %Hbw', HRb⟩ := swift.setR_open $$ HR
      wp_auto
      ihave HR := HRb $$ Hbal HsF HfF
      wp_apply (wp_Add f qF szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x)
          iprop(True) (swift.setR c RC MP γd d x b
            iprop(iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) s f qS
            szS memS hd false) (swift.descGone c b x d) hd fa.Replica' true
          (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)) $$ [HdF HR]
        as %added2 ⟨-, Hres⟩
      · iframe HdF HR HhFq
        isplitr
        · imodintro; iintro HR; isplitl []; · itrivial
          iintro -; iexact HR
        simp only [↓reduceIte]
        isplitr
        · ipureintro; intro h; cases h
        iunfold swift.leadAckP; iexists l, fa; iframe Hl
        isplitr
        · ipureintro; exact ⟨rfl, Hx, by rw [← hbb]; exact Hbw.1, by rw [← hbb]; exact Hbw.2⟩
        isplitr
        · iexists _; iexact HDep
        iexact Hacc
      icases Hres with (⟨HdF, HR⟩ | Hgone)
      · hasAnyHR
        try wp_auto
        ihave ⟨HR, HdS⟩ := swift.setR_swap' $$ [HR HdF]
        · iframe HR HdF
        ihave ⟨HR, Hocf0⟩ := swift.setR_take $$ HR
        $tOwnV
      · iunfold swift.descGone at Hgone
        icases Hgone with ⟨%Hsq, #Hex, Hret, Hgrd⟩
        hasGoneGrd
        try wp_auto
        $tGone
    · wp_auto
      ihave ⟨HR, Hocf0⟩ := swift.setR_take $$ HR
      $tOwnD
  · iunfold swift.descGone at Hgone
    icases Hgone with ⟨%Hsq, #Hex, Hret, Hgrd⟩
    hasGoneGrd
    try wp_auto
    $tGone))

set_option hygiene false in
/-- `sendSlowAck` with different dependencies: the adoption `desc.dep = dep` unless delivered,
then the `Add`s and the tails. -/
macro "adoptAdds" : tactic => `(tactic| (
  hasDl qe
  cases dl
  · try wp_auto
    irename HD => HD0
    ihave #HD := HDep
    -- round 54 (D74 (3)): the adopted `dep` is the leader's, with its prefix (`locDeps`)
    ihave #Hdw' : swift.depWhy c.γ c.γxm c.N c.r b x
        ({ dv with phase := W64 2, dep := fa.Dep', D := fw.dep.map ofCmdId } : swift.DescV) $$ []
    · iapply (swift.depWhy_foll c.γ c.γxm c.N c.r b x
        ({ dv with phase := W64 2, dep := fa.Dep', D := fw.dep.map ofCmdId } : swift.DescV) fw.dep hnL
        (by simp [List.map_map, Function.comp_def]))
      iexact HlD
    follAdds ({ dv with phase := W64 2, dep := fa.Dep', D := fw.dep.map ofCmdId } : swift.DescV)
      own (cases dl
           · tailTnd
           · tailTd)
      ownd (tailTd) gone (tailTgone)
  · try wp_auto
    -- round 55 (53-3', D77 (1)): delivered between the two checks, `dep` not adopted
    -- (swift.go:643): `x` was executed in `b` (`Hdlx`)
    ihave #Hdw' : swift.depWhy c.γ c.γxm c.N c.r b x ({ dv with phase := W64 2 } : swift.DescV) $$ []
    · icases Hdlx with (%Hf | #Hex)
      · cases Hf
      iapply (swift.depWhy_dlvd c.γ c.γxm c.N c.r b x _ hnL)
      iexact Hex
    follAdds ({ dv with phase := W64 2 } : swift.DescV)
      own (cases dl
           · tailTnd
           · tailTd)
      ownd (tailTd) gone (tailTgone)))

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [sync.Assumptions] [hook.Assumptions]
  [github_com.orcaman.concurrent_map.Assumptions]


set_option maxHeartbeats 2000000 in
theorem swift.Replica.fastAckFromLeader.wp_proof (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF)
    (wp_Call : hook.ocf.OptCondF.Call.specI)
    (wp_Leader : replica.Leader.spec)
    (str : swift.CommandId → GoString)
    (wp_String0 : swift.CommandId.String.specS str) (hinj : Function.Injective str)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_deps0 : ∀ c : swift.DC, c.str = str → swift.Replica.depsAccepted.specIc c)
    (wp_EqA : swift.Dep.Equals.specAny)
    (wp_EqP : swift.Dep.Equals.specPerm)
    (wp_SHA : swift.SHashesEq.specAny)
    (wp_Add : replica.mset.MsgSet.Add.specQ)
    (wp_mark : swift.Replica.markAccepted.specI)
    (wp_SLA : swift.Batcher.SendLightSlowAck.specI)
    (wp_SLAC : swift.Batcher.SendLightSlowAckClient.specI)
    (wp_lsa0 : ∀ c : swift.DC, c.str = str → swift.Replica.handleLightSlowAck.specIc RC MP c)
    (wp_sendc : replica.Sender.SendToClient.spec)
    (hms : swift.MLightSlowAck.marshalH) :
    ∀ c : swift.DC, c.str = str → swift.Replica.fastAckFromLeader.specIc RC MP swift.ackCtx c := by
  intro c hc γd d x b Do l fa
  have wp_String : ∀ _c : swift.DC, swift.CommandId.String.specS c.str := fun _ => hc ▸ wp_String0
  have hinjc : Function.Injective c.str := hc ▸ hinj
  have wp_deps : ∀ _c : swift.DC, swift.Replica.depsAccepted.specIc c := fun _ => wp_deps0 c hc
  have wp_lsa : ∀ _c : swift.DC, swift.Replica.handleLightSlowAck.specIc RC MP c :=
    fun _ => wp_lsa0 c hc
  wp_start as ⟨#Hctx, #Hack, Hown, #Hl, #HfDep, %Hx, %Hlead, #Hwit⟩
  iunfold swift.descOwnF at Hown
  icases Hown with ⟨Hown, Hocf⟩
  iunfold swift.descOcf at Hocf
  icases Hocf with ⟨%cf, %cond, %fs, %v, Hocfr, #Hcond, #Hvf, #Hfs⟩
  iunfold swift.ocfRes at Hocfr
  icases Hocfr with ⟨Hapf, Hocf, HPc, %sb, %bs, Hsb, Hbs, Hbsc, %Hb⟩
  iapply fupd_wp
  imod (swift.leader_cond c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) v l fa Hx)
    $$ [Hown HPc] with ⟨Hown, HPc, #Hstale⟩
  · iframe Hctx Hown HPc Hwit
  imodintro
  wp_auto
  ipersist r
  ipersist desc
  ipersist msg
  iunfold swift.proposeHalf at HPc
  icases HPc with ⟨%p, Hp, %Hpv⟩
  wp_auto
  -- P3 (fork 14aee3e): before the proposal, at most one stored ack per ballot
  ihave #Hfa0 := Hl
  iStructNamedPrefix Hfa0 "M"
  wp_bind (If (Val _) _ _)
  iapply (wp_wand (Φ := fun rv => iprop(
      typedPointsto (swift.dfld d go!"propose") p (DFrac.own (1 : Qp).half) ∗
      ∃ (sb' : GoSlice) (bs' : List w32), swift.dfld d go!"storedBallots" ↦ sb' ∗ sb' ↦* bs' ∗
        ownSliceCap w32 sb' (DFrac.own 1) ∗ ⌜bs'.Nodup ∧ fs.length ≤ bs'.length⌝ ∗
        (⌜rv = executeVal ∧ (v = false → fs.length + 1 ≤ bs'.length)⌝ ∨ ⌜rv = returnVal #()⌝))))
    $$ [Hp Hsb Hbs Hbsc]
  · by_cases hp : p = null
    · rw [decide_eq_true hp]
      have hv : v = false := by rw [← Hpv]; simp [hp]
      wp_auto
      ihave %Hbl := ownSlice_len $$ Hbs
      ihave HI : (∃ (i : w64) (bv : w32), "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bv ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sb.len ∧
            ∀ j y, j < sint.nat i → bs[j]? = some y → y ≠ fa.Ballot'⌝ : IProp netDistGF) $$ [i b]
      · iexists _, _; iframe; ipureintro; refine ⟨by word, by word, ?_⟩; intro j y hj; word
      wp_for HI
      wp_if_destruct
      · have hil : sint.nat i < bs.length := by word
        obtain ⟨y, hy⟩ : ∃ y, bs[sint.nat i]? = some y := ⟨_, List.getElem?_eq_getElem hil⟩
        rw [if_pos (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sb.len by word)]
        wp_apply (wp_load_slice_index (V := w32) sb (sint.Z i) bs _ y Hi.1) $$ [Hbs] as Hbs
        · iframe; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word, hy]
        try wp_auto
        wp_if_destruct
        · wp_for_post
          iframe
          isplitr
          · ipureintro; exact Hb
          iright; ipureintro; rfl
        · wp_for_post
          iframe
          iexists _, _; iframe; ipureintro
          refine ⟨by word, by word, ?_⟩
          intro j z hj hjz
          rcases Nat.lt_or_ge j (sint.nat i) with hlt | hge
          · exact Hi.2.2 j z hlt hjz
          · have : j = sint.nat i := by
              have : sint.nat (i + W64 1) = sint.nat i + 1 := by word
              omega
            subst this
            rw [hy] at hjz; cases hjz
            exact Hif
      · -- not stored: append the ballot
        have hnot : fa.Ballot' ∉ bs := by
          intro hm
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
          have : j < bs.length := by
            rcases Nat.lt_or_ge j bs.length with h' | h'
            · exact h'
            · rw [List.getElem?_eq_none_iff.mpr h'] at hj; cases hj
          exact Hi.2.2 j _ (by word) hj rfl
        try wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral
          (go.GoType.SliceType go.int32)))) (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := w32) (t := go.int32) [_]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %lsl ⟨Hlsl, -⟩
        wp_auto
        wp_apply wp_slice_append $$ [Hbs Hbsc Hlsl] as %nsl ⟨Hbs, Hbsc, -⟩
        · iframe
        try wp_auto
        iframe
        isplitr
        · ipureintro
          refine ⟨List.nodup_append.mpr ⟨Hb.1, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩, ?_⟩
          · intro a ha c hc; simp at hc; subst hc; exact fun e => hnot (e ▸ ha)
          · simp; have := Hb.2; omega
        ileft; ipureintro; refine ⟨rfl, ?_⟩
        intro _; simp; have := Hb.2; omega
    · rw [decide_eq_false hp]
      have hv : v = true := by rw [← Hpv]; simp [hp]
      wp_auto
      iframe
      isplitr
      · ipureintro; exact Hb
      ileft; ipureintro; exact ⟨rfl, fun h => by simp [hv] at h⟩
  iintro %rv ⟨Hp, %sb, %bs, Hsb, Hbs, Hbsc, %Hb, %Hrv⟩
  ihave HPc : swift.proposeHalf d v $$ [Hp]
  · iunfold swift.proposeHalf; iexists p; iframe Hp; ipureintro; exact Hpv
  rcases Hrv with ⟨rfl, Hbv⟩ | rfl
  rotate_left
  · -- an ack of a stored ballot: nothing to do
    wp_auto
    iapply HΦ
    ileft
    iunfold swift.descOwnF
    iframe Hown
    iunfold swift.descOcf
    iexists cf, cond, fs, v
    iframe Hcond Hfs Hvf
    iunfold swift.ocfRes
    iframe Hapf Hocf HPc
    iexists sb, bs; iframe; ipureintro; exact Hb
  wp_auto
  wp_apply (swift.fastAck_call c RC MP γd d x b Do cf cond fs v _ sb bs ⟨Hb.1, Hb.2, Hbv⟩ wp_Call)
    $$ [Hown Hapf Hocf HPc Hsb Hbs Hbsc] as %bb Hres
  · iframe Hown Hapf Hocf Hcond HPc Hfs Hvf Hsb Hbs Hbsc
    isplitr
    · -- the closure's spec
      imodintro
      iunfold swift.closureOk
      iintro %Ψ
      imodintro
      iintro Hst0 HΨ
      ihave #Hfa := Hl
      iStructNamed Hfa
      ihave #Hctx2 := Hctx
      iunfold swift.DC.ctx at Hctx2
      iunfold swift.descCtxE at Hctx2
      icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #Hrr, #Hrep, %Hids,
        -, -, #Hoe, #Hinv, #Hcfg, #Hninv, #Hdm, #Hcm, #HdI, -⟩
      ihave #HN := Hrep
      iunfold replica.isReplica at HN
      icases HN with ⟨%lg', %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
        %cwm, -, -, #HN, #Hid, -⟩
      have hN : 1 ≤ c.N ∧ c.N ≤ 7 := ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩
      icases Hst0 with (⟨Hown, Hocf0⟩ | ⟨Hdone, %HrL⟩)
      rotate_left
      · -- retired at a follower: the checks, then `delivered.Has(x)` is true (SWB-8's guard)
        iunfold swift.descDone at Hdone
        icases Hdone with Hgone
        iunfold swift.descGone at Hgone
        icases Hgone with ⟨%Hsq, #Hex, Hret, %qe, %bw, %stp, %rcp, Hrd, Hsh⟩
        ihave ⟨%st, %fq, %szF', %memF', Hst, HFQ, #HqF, %HAQ, HrdR, Hpin, Hshb⟩ := swift.shOwnR_openR c d b qe $$ Hsh
        iunfold swift.epochRd at Hrd
        icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
        wp_apply wp_with_defer as %defer Hdefer
        try wp_auto
        by_cases hst : st = W64 0
        rotate_left
        · rw [decide_eq_false hst]
          wp_auto
          iapply HΨ; iright; repackDone
        rw [decide_eq_true hst]
        wp_auto
        by_cases hbb : bw = fa.Ballot'
        rotate_left
        · rw [decide_eq_false hbb]
          wp_auto
          iapply HΨ; iright; repackDone
        rw [decide_eq_true hbb]
        wp_auto
        wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw _ c.N hN) $$ [$Hbal $Hrr $HN]
          as Hbal
        try wp_auto
        have hne : ¬ (BitVec.srem bw (W32 (sint.Z (W64 (c.N : Int)))) = me) := by
          intro h; apply HrL
          rw [← Hids.1, ← h]; exact swift.rid_leader bw c.N b hN Hbw.1 Hbw.2
        rw [decide_eq_false hne]
        wp_auto
        wp_apply (wp_String c) $$ [$CmdId] as -
        ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ∗
            (github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ={⊤}=∗ swift.ownRdr c.rp c.γdl)) $$ [HrdR]
        · iapply swift.ownRdr_take; iframe Hdm HrdR
        iapply fupd_wp
        imod Hb with ⟨Hrdr, HbackR⟩
        imodintro
        wp_method_call
        wp_auto
        wp_apply (wp_HasV dm c.γdl _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
            (fun ok => iprop(⌜ok = true⌝ ∗ swift.epochPinQ c.γxp qe b))) $$ [$Hrdr Hpin] as %dl ⟨Hrdr, %Hdl, Hpin⟩
        · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
            swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
          iunfold swift.delivInv at Hi
          icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
          ihave ⟨Hpin, HXeD, %Hag⟩ := swift.epochPinQ_agree c.γxp qe b bX' rm $$ [Hpin HXeD]
          · iframe Hpin HXeD
          obtain ⟨rfl, rfl⟩ := Hag
          ihave %Hin := swift.exIn_delivered c.str c.γxm bX' x M X' Mx HM $$ [Hex HMx]
          · iframe Hex HMx
          imodintro
          iexists M
          iframe HV
          iintro HV
          imod Hclose $$ [HV HXi HXeD HMx HXx] with -
          · inext; iunfold swift.delivInv; iexists M, bX', X', Mx, false; iframe; ipureintro; exact HM
          imodintro
          isplitr
          · ipureintro; rw [Hx]; exact Hin
          iexact Hpin
        iapply fupd_wp
        imod HbackR $$ Hrdr with HrdR
        imodintro
        subst Hdl
        wp_auto
        iapply HΨ; iright; repackDone
      -- the owner state
      iunfold swift.descOwn at Hown
      icases Hown with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF,
        HdS, HR⟩
      iunfold swift.setR at HR
      iunfold swift.descSt at HR
      icases HR with ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, ⟨#Hra, #HrP⟩, %Hph,
        #Hpw, #Hdw, %Hrp, #HsB, ⟨HsF, HfF, HdF, Hcore, HDo⟩⟩
      iunfold swift.ocfRes0 at Hocf0
      icases Hocf0 with ⟨%cf0, %cond0, Hocfr0, #Hcond0⟩
      iunfold swift.ocfRes at Hocfr0
      icases Hocfr0 with ⟨Hoapf, Hoocf, HPc, Hosb⟩
      iunfold swift.epochRd at Hrd
      icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
      ihave ⟨%st, %fq, %szF', %memF', Hst, HFQ, #HqF, %HAQ, HrdR, Hpin, Hshb⟩ := swift.shOwn_openR c d b qe $$ Hsh
      wp_apply wp_with_defer as %defer Hdefer
      try wp_auto
      by_cases hst : st = W64 0
      rotate_left
      · rw [decide_eq_false hst]
        wp_auto
        iapply HΨ; ileft; packO0; iframe Hocf0; repackOwnF
      rw [decide_eq_true hst]
      wp_auto
      by_cases hbb : bw = fa.Ballot'
      rotate_left
      · rw [decide_eq_false hbb]
        wp_auto
        iapply HΨ; ileft; packO0; iframe Hocf0; repackOwnF
      rw [decide_eq_true hbb]
      wp_auto
      wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw _ c.N hN) $$ [$Hbal $Hrr $HN]
        as Hbal
      try wp_auto
      have hLr : BitVec.srem bw (W32 (sint.Z (W64 (c.N : Int)))) = me → c.r = sp.leaderOf c.N b := by
        intro h; rw [← Hids.1, ← h]; exact swift.rid_leader bw c.N b hN Hbw.1 Hbw.2
      by_cases hL : BitVec.srem bw (W32 (sint.Z (W64 (c.N : Int)))) = me
      · rw [decide_eq_true hL]
        wp_auto
        wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw _ c.N hN) $$ [$Hbal $Hrr $HN]
          as Hbal
        try wp_auto
        rw [decide_eq_true hL]
        wp_auto
        -- the acceptance path at the leader
        iunfold swift.leadWitB at Hwit
        icases Hwit with (%hne | #Hwit)
        · exfalso; exact hne (by rw [← hbb]; exact Hbw.1)
        iunfold swift.leadWit at Hwit
        icases Hwit with ⟨%fw, -, ⟨%h1, %h2, %h3⟩, #HDep, #Hok, #HCs⟩
        iunfold sp.fastAckOk at Hok
        icases Hok with ⟨-, #Hpre, -⟩
        ihave #Hpre' : sp.preacc c.γ (sp.leaderOf c.N b) b (toCmdId x) fw.dep $$ [Hpre]
        · have e1 : sp.rid fw.rep = sp.leaderOf c.N b := by rw [← h1]; exact Hlead
          have e2 : sp.bal fw.bal = b := by rw [← h2, ← hbb]; exact Hbw.1
          have e3 : fw.id = toCmdId x := by rw [← h3, Hx]
          rw [← e1, ← e2, ← e3]; iexact Hpre
        ihave Htp := swift.rowTokO_tokP c b x d γd MP dv rv $$ [Hd HPc Htok]
        · iframe Hd HPc Htok
        icases Htp with ⟨Hd, HPc, ⟨Htok, Hslt⟩, %Hpn⟩
        iunfold swift.rowAcc at Hra
        icases Hra with ⟨#Hra1, %Hra2, #Hpp⟩
        -- L2 (item 4, D91): the acceptance at `ghostAccept`'s resolution, after
        -- `desc.phase = ACCEPT`; a row already accepted is accepted again (`reaccept_dstep`)
        ihave Hacc : swift.ghostUpd c.γ c.k (sp.PEv.accept b (toCmdId x))
            iprop(swift.epochTok c.γe qe (b, b) ∗ ∃ rv' : swift.RowV,
            swift.rowTok c.γo b (toCmdId x) rv' ∗
            ⌜rv'.1 = rv.1 ∧ rv'.2.2.2 = rv.2.2.2 ∧ rv'.2.1 = rv.2.1 ∧ rv'.2.2.1 = true⌝ ∗
            sp.accepted c.γ c.r b (toCmdId x)) $$ [Het Htok]
        · iunfold swift.ghostUpd
          iintro %W' Hpp
          cases hra : rv.2.2.1
          · imod (swift.accept_dstep_pre c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
              (toCmdId x) fw.dep rv Hids.2.2.1 Hids.2.2.2.2.2 hra W') $$ [Het Htok Hpp]
              with ⟨Het, Htok, Hpost, #Ha⟩
            · iframe Hinv Hcfg Hninv Het Htok Hpre' Hpp; ileft; ipureintro; exact hLr hL
            imodintro; iframe Het Hpost; iexists _; iframe Htok Ha; ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
          · icases Hra1 with (%Hf | #Ha)
            · first | cases Hf | (rw [hra] at Hf; cases Hf)
            imod (swift.reaccept_dstep c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
              (toCmdId x) rv Hids.2.2.1 Hids.2.2.2.2.2 hra W') $$ [Het Htok Hpp]
              with ⟨Het, Htok, Hpost⟩
            · iframe Hinv Hcfg Hninv Het Htok Hpp
            imodintro; iframe Het Hpost; iexists _; iframe Htok Ha; ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
        iunfold swift.descCore at Hcore
        icases Hcore with ⟨%wa, %sl, Hwa, Hsl, -⟩
        iunfold swift.descF at Hd
        icases Hd with ⟨Hph', Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop, Hseq, Hmsgs, #Hmb, #HsL, %Hop⟩
        wp_auto
        ghostAcc
        ihave #Hack2 := Hack
        iunfold swift.ackCtx at Hack2
        icases Hack2 with ⟨%sq, %szS', %memS', %bt, %sn, %γs, %csv, #HSQ, #HqS, %HmS, #Hbt, #HbH, #Hsn,
          #Hsb, #Hcs, %Hcodes, -⟩
        wp_apply (wp_EqA (swift.dfld d go!"dep") dv.dep fa.Dep' (DFrac.own 1) DFrac.discard
          DFrac.discard dv.D (fw.dep.map ofCmdId)) $$ [Hdep] as %neq ⟨Hdep, -, -⟩
        · iframe Hdep HD HDep
        ihave %Hfq := replica.mset.quorumIs_ok $$ HqF
        obtain ⟨iF, rfl⟩ := Hfq
        ihave %Hsq := replica.mset.quorumIs_ok $$ HqS
        obtain ⟨iS, rfl⟩ := Hsq
        wp_auto
        wp_apply (replica.mset.wp_qContains iF szF' memF' me) $$ [$HqF] as %fast -
        try wp_auto
        wp_apply (replica.mset.wp_qContains iS szS' memS' me) $$ [$HqS] as %slow -
        try wp_auto
        wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw _ c.N hN) $$ [$Hbal $Hrr $HN]
          as Hbal
        try wp_auto
        rw [decide_eq_true hL]
        wp_auto
        ihave Hsh := Hshb $$ Hst HFQ HrdR Hpin
        packO0
        -- round 56 (D79 (2)): the sync disjunct (a base command) is refuted by the leader's own
        -- pre-acceptance of `x` (`sp.preacc_notBase`)
        iapply fupd_wp
        imod (swift.depWhy_phase c.γ c.γxm c.N c.r b x dv rv (W64 2) Hrp.1
          (fun hl _ _ => absurd (hLr hL) hl)) $$ [Hdw] with #Hdw'
        · isplitr
          · iintro %_ #HsI
            iunfold swift.syncIn at HsI
            icases HsI with ⟨%M, #HM, %hyM⟩
            ihave Hno := sp.preacc_notBase (γ := c.γ) (γc := c.γc) (γm := c.γm) (γl := c.γl)
              (sp.leaderOf c.N b) b (toCmdId x) fw.dep M $$ [Hinv Hpre' HM]
            · iframe Hinv Hpre' HM
            imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hno with %hno
            exfalso; exact hno hyM
          iexact Hdw
        imodintro
        ihave HR : swift.setR c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) s f qF szF memF
            hd true $$ [Hsh HRC Hcmd Hdep Hhs Hprop Hseq Hmsgs Hph' Htok Hslt Hcom HsF HfF HdF HDo Hbal HStf
            Hrcf Het Hxe Hwa Hsl]
        · ihave #HrPa := swift.repPre_congr c.γ c.N c.r b x dv ({ dv with phase := W64 2 } : swift.DescV)
            rfl rfl rfl rfl $$ HrP
          packAccR ({ dv with phase := W64 2 } : swift.DescV)
        ihave HR := swift.setR_give $$ [HR Hocf0]
        · iframe HR Hocf0
        ihave #HhSq := swift.descOwn_hdS c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do)
          iprop(iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) s f qS qF szS szF memS memF hd
          (swift.ocf0Dc_ok d _) $$ [HhS HhF]
        · iframe HhS HhF
        ihave #HhFq := swift.descOwn_hdF c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do)
          iprop(iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) s f qS qF szS szF memS memF hd
          (swift.ocf0Dc_ok d _) $$ [HhS HhF]
        · iframe HhS HhF
        wp_apply (wp_Add s qS szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True)
            (swift.setR c RC MP γd d x b iprop(iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d)
              s f qF szF memF hd true)
            (swift.descGone c b x d) hd fa.Replica' true
            (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)) $$ [HdS HR]
          as %added ⟨-, Hres⟩
        · iframe HdS HR HhSq
          isplitr
          · imodintro; iintro HR; isplitl []; · itrivial
            iintro -; iexact HR
          simp only [↓reduceIte]
          isplitr
          · ipureintro; intro h; cases h
          iunfold swift.leadAckP; iexists l, fa; iframe Hl
          isplitr
          · ipureintro; exact ⟨rfl, Hx, by rw [← hbb]; exact Hbw.1, by rw [← hbb]; exact Hbw.2⟩
          isplitr
          · iexists _; iexact HDep
          iexact Hacc
        icases Hres with (⟨HdS, HR⟩ | Hgone)
        · hasAnyHR
          cases dl
          · wp_auto
            ihave ⟨HR, HdF⟩ := swift.setR_swap $$ [HR HdS]
            · iframe HR HdS
            ihave ⟨%qe', %bw', Hbal, HsF, HfF, %Hbw', HRb⟩ := swift.setR_open $$ HR
            wp_auto
            ihave HR := HRb $$ Hbal HsF HfF
            wp_apply (wp_Add f qF szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x)
                iprop(True) (swift.setR c RC MP γd d x b
                  iprop(iprop(swift.descCore c d x b ∗ Do) ∗ swift.ocfRes0 d) s f qS
                  szS memS hd false) (swift.descGone c b x d) hd fa.Replica' true
                (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)) $$ [HdF HR]
              as %added2 ⟨-, Hres⟩
            · iframe HdF HR HhFq
              isplitr
              · imodintro; iintro HR; isplitl []; · itrivial
                iintro -; iexact HR
              simp only [↓reduceIte]
              isplitr
              · ipureintro; intro h; cases h
              iunfold swift.leadAckP; iexists l, fa; iframe Hl
              isplitr
              · ipureintro; exact ⟨rfl, Hx, by rw [← hbb]; exact Hbw.1, by rw [← hbb]; exact Hbw.2⟩
              isplitr
              · iexists _; iexact HDep
              iexact Hacc
            icases Hres with (⟨HdF, HR⟩ | Hgone)
            · hasAnyHR
              try wp_auto
              ihave ⟨HR, HdS⟩ := swift.setR_swap' $$ [HR HdF]
              · iframe HR HdF
              ihave ⟨HR, Hocf0⟩ := swift.setR_take $$ HR
              leaderEndOwn
            · iunfold swift.descGone at Hgone
              icases Hgone with ⟨%Hsq, #Hex, Hret, Hgrd⟩
              hasGoneGrd
              try wp_auto
              leaderEndGone
          · wp_auto
            ihave ⟨HR, Hocf0⟩ := swift.setR_take $$ HR
            leaderEndOwn
        · iunfold swift.descGone at Hgone
          icases Hgone with ⟨%Hsq, #Hex, Hret, Hgrd⟩
          hasGoneGrd
          try wp_auto
          leaderEndGone
      have hnL : c.r ≠ sp.leaderOf c.N b := by
        rw [← Hids.1]
        exact swift.rid_ne_leader me bw c.N b hN Hbw.1 Hbw.2 Hids.2.1 (fun h => hL h.symm)
      rw [decide_eq_false hL]
      wp_auto
      wp_apply (wp_String c) $$ [$CmdId] as -
      ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ∗
          (github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ={⊤}=∗ swift.ownRdr c.rp c.γdl)) $$ [HrdR]
      · iapply swift.ownRdr_take; iframe Hdm HrdR
      iapply fupd_wp
      imod Hb with ⟨Hrdr, HbackR⟩
      imodintro
      wp_method_call
      wp_auto
      wp_apply (wp_HasV dm c.γdl _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
          (fun _ => iprop(True))) $$ [$Hrdr] as %dl ⟨Hrdr, -⟩
      · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
          swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
        iunfold swift.delivInv at Hi
        icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
        imodintro
        iexists M
        iframe HV
        iintro HV
        imod Hclose $$ [HV HXi HXeD HMx HXx] with -
        · inext; iunfold swift.delivInv; iexists M, bX', X', Mx, rm; iframe; ipureintro; exact HM
        imodintro
        itrivial
      iapply fupd_wp
      imod HbackR $$ Hrdr with HrdR
      imodintro
      cases dl
      rotate_left
      · wp_auto
        iapply HΨ; ileft; packO0; iframe Hocf0; repackOwnF
      wp_auto
      wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw _ c.N hN) $$ [$Hbal $Hrr $HN]
        as Hbal
      try wp_auto
      rw [decide_eq_false hL]
      wp_auto
      iunfold swift.leadWitB at Hwit
      icases Hwit with (%hne | #Hwit)
      · exfalso; exact hne (by rw [← hbb]; exact Hbw.1)
      iunfold swift.leadWit at Hwit
      icases Hwit with ⟨%fw, -, ⟨%h1, %h2, %h3⟩, #HDep, #Hok, #HCs⟩
      wp_apply (wp_deps c b fa.Dep' (fw.dep.map ofCmdId) fa.CmdId') $$ [Hpin HrdR] as %ok ⟨Hpin, HrdR, Hdok⟩
      · iframe Hctx Hpin HrdR HDep; ipureintro; exact hnL
      cases ok
      · -- a dependency not accepted yet: the ack waits (`"recheck"`)
        wp_auto
        iunfold swift.descCore at Hcore
        icases Hcore with ⟨%wa, %sl, Hwa, Hsl, -⟩
        wp_auto
        iapply HΨ; ileft; packO0; iframe Hocf0
        ihave Hcore : swift.descCore c d x b $$ [Hwa Hsl]
        · iunfold swift.descCore
          iexists l, sl
          iframe Hwa Hsl
          iright; iexists fa
          isplitr
          · ipureintro; exact ⟨Hx, Hlead⟩
          iunfold swift.leadWit; iexists fw; iframe Hl HDep Hok HCs
          ipureintro; exact ⟨h1, h2, h3⟩
        repackOwnF
      icases Hdok with (%Hf | #Hdok)
      · cases Hf
      wp_auto
      -- the acceptance path at a follower
      iunfold sp.fastAckOk at Hok
      icases Hok with ⟨-, #Hpre, %P0, -, -, -, #HlD0⟩
      have e1 : sp.rid fw.rep = sp.leaderOf c.N b := by rw [← h1]; exact Hlead
      have e2 : sp.bal fw.bal = b := by rw [← h2, ← hbb]; exact Hbw.1
      have e3 : fw.id = toCmdId x := by rw [← h3, Hx]
      ihave #Hpre' : sp.preacc c.γ (sp.leaderOf c.N b) b (toCmdId x) fw.dep $$ [Hpre]
      · rw [← e1, ← e2, ← e3]; iexact Hpre
      -- round 54 (D74 (3), 52-1): the leader's prefix (its ack's `locDeps`), its `dep` without
      -- duplicates (53-2's `Dep.Equals`)
      ihave #HlD : sp.locDeps c.γ (sp.leaderOf c.N b) b (toCmdId x) fw.dep $$ [HlD0]
      · rw [← e1, ← e2, ← e3]; iexact HlD0
      iapply fupd_wp
      imod (sp.locDeps_nodup (γc := c.γc) (γm := c.γm) (γl := c.γl) ⊤ (by simp)
        (sp.leaderOf c.N b) b (toCmdId x) fw.dep) $$ [Hinv HlD] with %HDnd
      · iframe Hinv HlD
      imodintro
      have hDnd : (fw.dep.map ofCmdId).Nodup :=
        List.Pairwise.map ofCmdId (fun a b hab h => hab (by
          have := congrArg toCmdId h; simpa [toCmdId_ofCmdId] using this)) HDnd
      ihave Htp := swift.rowTokO_tokP c b x d γd MP dv rv $$ [Hd HPc Htok]
      · iframe Hd HPc Htok
      icases Htp with ⟨Hd, HPc, ⟨Htok, Hslt⟩, %Hpn⟩
      iapply fupd_wp
      imod (swift.preacc_notSelf_row c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
        (toCmdId x) rv (sp.leaderOf c.N b) b (toCmdId x) fw.dep Hids.2.2.1 Hids.2.2.2.2.2)
        $$ [Het Htok] with ⟨Het, Htok, %Hnot⟩
      · iframe Hinv Hcfg Hninv Het Htok Hpre'
      imodintro
      ihave #HN2 := swift.depsOk_N2 c b fw.dep fa.CmdId' (by rw [Hx]; exact Hnot) $$ Hdok
      iunfold swift.rowAcc at Hra
      icases Hra with ⟨#Hra1, %Hra2, #Hpp⟩
      -- L2 (item 4, D91): the acceptance at `ghostAccept`'s resolution, after
      -- `desc.phase = ACCEPT`; a row already accepted is accepted again (`reaccept_dstep`)
      ihave Hacc : swift.ghostUpd c.γ c.k (sp.PEv.accept b (toCmdId x))
          iprop(swift.epochTok c.γe qe (b, b) ∗ ∃ rv' : swift.RowV,
          swift.rowTok c.γo b (toCmdId x) rv' ∗
            ⌜rv'.1 = rv.1 ∧ rv'.2.2.2 = rv.2.2.2 ∧ rv'.2.1 = rv.2.1 ∧ rv'.2.2.1 = true⌝ ∗
          sp.accepted c.γ c.r b (toCmdId x)) $$ [Het Htok]
      · iunfold swift.ghostUpd
        iintro %W' Hpp
        cases hra : rv.2.2.1
        · imod (swift.accept_dstep_pre c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
            (toCmdId x) fw.dep rv Hids.2.2.1 Hids.2.2.2.2.2 hra W') $$ [Het Htok Hpp]
            with ⟨Het, Htok, Hpost, #Ha⟩
          · iframe Hinv Hcfg Hninv Het Htok Hpre' Hpp; iright; iexact HN2
          imodintro; iframe Het Hpost; iexists _; iframe Htok Ha; ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
        · icases Hra1 with (%Hf | #Ha)
          · first | cases Hf | (rw [hra] at Hf; cases Hf)
          imod (swift.reaccept_dstep c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
            (toCmdId x) rv Hids.2.2.1 Hids.2.2.2.2.2 hra W') $$ [Het Htok Hpp]
            with ⟨Het, Htok, Hpost⟩
          · iframe Hinv Hcfg Hninv Het Htok Hpp
          imodintro; iframe Het Hpost; iexists _; iframe Htok Ha; ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      iapply fupd_wp
      -- round 47 (46-2): the leader's dependencies are few (`replyPre`'s bound on an adopted `D`)
      ihave HDl := sp.preacc_depWf (γ := c.γ) (γc := c.γc) (γm := c.γm) (γl := c.γl)
        (sp.leaderOf c.N b) b (toCmdId x) fw.dep $$ [Hinv Hpre']
      · iframe Hinv Hpre'
      imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ HDl with %hDl0
      have hDl : (fw.dep.map ofCmdId).length < 2 ^ 62 := by rw [List.length_map]; exact hDl0
      imodintro
      iunfold swift.descCore at Hcore
      icases Hcore with ⟨%wa, %sl, Hwa, Hsl, -⟩
      iunfold swift.descF at Hd
      icases Hd with ⟨Hph', Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop, Hseq, Hmsgs, #Hmb, #HsL, %Hop⟩
      wp_auto
      ghostAcc
      ihave #Hack2 := Hack
      iunfold swift.ackCtx at Hack2
      icases Hack2 with ⟨%sq, %szS', %memS', %bt, %sn, %γs, %csv, #HSQ, #HqS, %HmS, #Hbt, #HbH, #Hsn,
        #Hsb, #Hcs, %Hcodes, -⟩
      wp_apply (wp_EqP (swift.dfld d go!"dep") dv.dep fa.Dep' (DFrac.own 1) DFrac.discard
        DFrac.discard dv.D (fw.dep.map ofCmdId)) $$ [Hdep] as %neq ⟨Hdep, -, -, %Hneq⟩
      · iframe Hdep HD HDep; ipureintro; exact hDnd
      ihave %Hfq := replica.mset.quorumIs_ok $$ HqF
      obtain ⟨iF, rfl⟩ := Hfq
      ihave %Hsq := replica.mset.quorumIs_ok $$ HqS
      obtain ⟨iS, rfl⟩ := Hsq
      wp_auto
      wp_apply (replica.mset.wp_qContains iF szF' memF' me) $$ [$HqF] as %fast -
      try wp_auto
      -- round 54 (D74 (3), 53-1): `SQ` has every replica, so `slow` (and `sendSlowAck`) holds
      wp_apply (swift.wp_qContains_all iS szS' memS' me HmS) $$ [$HqS]
      try wp_auto
      wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw _ c.N hN) $$ [$Hbal $Hrr $HN]
        as Hbal
      try wp_auto
      rw [decide_eq_false hL]
      wp_auto
      cases neq
      · wp_auto
        adoptAdds
      · -- `sendSlowAck`, the same dependencies (53-2: a permutation of the leader's)
        wp_auto
        ihave #Hdw' : swift.depWhy c.γ c.γxm c.N c.r b x ({ dv with phase := W64 2 } : swift.DescV) $$ []
        · iapply (swift.depWhy_foll c.γ c.γxm c.N c.r b x ({ dv with phase := W64 2 } : swift.DescV)
            fw.dep hnL (by
              have h := (Hneq rfl).map toCmdId
              simpa [List.map_map, Function.comp_def] using h))
          iexact HlD
        follAdds ({ dv with phase := W64 2 } : swift.DescV)
            own (cases dl
                 · tailTnd
                 · tailTd)
            ownd (tailTd) gone (tailTgone)
    by_cases hv : v = true
    · ileft; ipureintro; exact Or.inl hv
    by_cases hr : c.r ≠ sp.leaderOf c.N b
    · ileft; ipureintro; exact Or.inr hr
    icases Hstale with (%Hstale | #Hpa)
    rotate_left
    · iright; iright; iexact Hpa
    iright; ileft
    have hstale : sp.bal fa.Ballot' ≠ b :=
      Hstale (by simpa using hv) (by simpa using hr) Hlead
    imodintro
    iunfold swift.closureNop
    iintro %Ψ
    imodintro
    iintro Hown HΨ
    iunfold swift.descOwn at Hown
    icases Hown with ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS,
      HR⟩
    ihave #Hfa := Hl
    iStructNamed Hfa
    wp_apply wp_with_defer as %defer Hdefer
    ihave ⟨%qe', %bw', %st, Hbal, Hst, HsF, HfF, %Hbw', HRb⟩ := swift.setR_openS $$ HR
    try wp_auto
    have hne : bw' ≠ fa.Ballot' := fun h => hstale (h ▸ Hbw'.1)
    by_cases hst : st = W64 0
    · rw [decide_eq_true hst]
      wp_auto
      rw [decide_eq_false hne]
      wp_auto
      ihave HR := HRb $$ Hbal Hst HsF HfF
      iapply HΨ
      iunfold swift.descOwn
      iexists s, f, qS, qF, szS, szF, memS, memF, hd
      iframe HhS HhF HdS HR
    · rw [decide_eq_false hst]
      wp_auto
      ihave HR := HRb $$ Hbal Hst HsF HfF
      iapply HΨ
      iunfold swift.descOwn
      iexists s, f, qS, qF, szS, szF, memS, memF, hd
      iframe HhS HhF HdS HR
  iapply HΦ $$ Hres

end proof

end Perennial.github_com.imdea_software.swiftpaxos
