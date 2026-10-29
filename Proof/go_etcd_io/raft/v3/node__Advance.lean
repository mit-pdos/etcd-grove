/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Advance
public import Proof.go_etcd_io.raft.v3.InvAdvance
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView
import Proof.go_etcd_io.raft.v3.InvApiDec
import all Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

What the proof over raft's internals shows, from which the wrapper (below) derives the spec. Its documentation, as when it was the spec (until 2026-10-28):
-/

/-! Lean-first (no Rocq counterpart).

## `node.Advance()` (node.go:549)

The driver, done with a `Ready` (its entries appended: the storage's receipt), hands it
back to `run` (`advancec <- struct{}{}`, `advanceP`); its token is idle again, at the
committed log handed out so far. (2026-10-29, stage U9a) Or the node stopped (`n.done` fired):
the driver's token idle at the same log, its view of the configuration unchanged.

(D19i part 1, 2026-10-18) And the storage's floor is at least the committed log handed out
(`storFloor`): `run` raises it at the rendezvous (`advInv`), so the application may compact
and snapshot its storage up to what it applied, before `run`'s `rn.Advance` moves `applied`.

(D22 S-d4, 2026-10-21) For the `Ready`'s snapshot `L` (its loan, `nodeDriverBusy`): after a
`Ready` with a snapshot the receipt is the storage at the snapshot with the half of the snapshot
(`advReceipt`, `snapReceipt`), and no floor is raised (`reqWit γ none`); after one without, the
floor's witness -- unless a snapshot was restored since (at a node that takes snapshots, `snapIn`:
`reqWit`'s second case), which a client in raft's no-snapshot mode, in the dynamic mode or at a
node that takes no `MsgSnap` refutes (`reqWit_none`).
-/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
private abbrev node.Advance.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (ds es : List EntryM) (ca : Nat)
    (cfg : CCState) (p : HardStateM) (L : Option SnapLoan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      nodeDriverBusy γ id n ds es p L ∗ advReceipt γ.stor ds.length es L ∗ nodeCfg γ ca cfg ∗
      -- (2026-10-15, stage N) **A1**, in the dynamic mode: every conf entry of the committed log
      -- handed out has been applied (`node.ApplyConfChange`): none past the driver's configuration
      -- index (`issues/raft-advance-before-applyconfchange.md`); (2026-10-28, the decision switch) or
      -- skipped, rejected over decisions recorded (`undecFree`); (raft-final, 2026-10-29, the
      -- design's A1) only after a `Ready` without a snapshot
      □ (⌜L = none⌝ -∗ undecFree γ.raft γ.mode ds ca ds.length) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); (nodeDriverChan γ id n ds p ∗
      -- (2026-10-28, stage U3d) the view of the configuration: after a snapshot `Ready`,
      -- dynamically, the snapshot's (`loanCfg`), which a snapshot `Ready` has only outside the
      -- no-snapshot mode
      nodeCfg γ (loanCfg γ.mode L (ca, cfg)).1 (loanCfg γ.mode L (ca, cfg)).2 ∗
      -- (D19i part 1) the floor's witness for `ds`; (D22 S-d4) after a `Ready` without a snapshot,
      -- unless one was restored since (`reqWit`)
      reqWit γ (reqOf L ds)) ∨
    -- (2026-10-29, stage U9a) or the node stopped (`done` fired first): the driver idle, its view
    -- unchanged
    (nodeStoppedRaw γ ∗ nodeDriverChan γ id n ds p ∗ nodeCfg γ ca cfg) }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `dlv` halves move on past the `Ready` (`run` will recognize its record), one goes
with the receipt on `advancec`; (2026-10-29, stage U9a) or `n.done` fires: the node stopped. -/
private theorem node.Advance.wp_raw : node.Advance.specRaw (GF := GF) (hG := hG) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  intro γ id n ds es ca cfg p' L
  wp_start as ⟨Hbusy, Hrcpt, Hcfg, #HA1⟩
  unfold nodeDriverBusy
  icases Hbusy with ⟨#Hnode, #Hdlb, -, %d, %ce, %p, Hd1, Hd2, Hrof, %Hds, %q0, Hr1, Hr2⟩
  ihave #Hcamlb : monoNatLbOwn γ.cam ca $$ [Hcfg]
  · unfold nodeCfg; icases Hcfg with ⟨-, -, $⟩
  subst Hds
  ihave #Hnode' := Hnode
  open_node Hnode'
  imod dghostVar_update_halves (dlvAfter d ce L, p') γ.dlv (d, p) (d, p) $$ Hd1 Hd2 with ⟨Hd1, Hd2⟩
  wp_auto_lc 3
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `advancec <- struct{}{}` (D19i part 1: `advInv`, the floor raised at the rendezvous)
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.advancec',
      γ.advancec, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply isAdvChan_isChan $$ Hadvancec
    -- (2026-10-28, stage U3d) after a snapshot `Ready` the view goes with the payload and comes
    -- back moved (`capPay`, `capAns`)
    ihave ⟨Hpay, Hback⟩ : capPay γ L (ca, cfg) ∗ (capAns γ (loanReq γ.mode L (ca, cfg)) -∗
        nodeCfg γ (loanCfg γ.mode L (ca, cfg)).1 (loanCfg γ.mode L (ca, cfg)).2 ∗
        ⌜L ≠ none → γ.raft.reNoSnap = false⌝) $$ [Hcfg]
    · cases L with
      | none =>
        isplitr
        · simp only [capPay]; itrivial
        iintro -
        rw [loanCfg_none]
        iframe Hcfg
        ipureintro; intro h; exact absurd rfl h
      | some l =>
        unfold nodeCfg
        icases Hcfg with ⟨Hcap, Hccq, -⟩
        isplitl [Hcap]
        · simp only [capPay]; iexact Hcap
        iintro Hans
        simp only [capAns, loanReq, Option.map_some]
        icases Hans with ⟨Hcap, #Hlb, %Hns⟩
        iframe Hcap Hccq Hlb
        ipureintro; intro _; exact Hns
    iapply adv_send_au γ nv.rn' id nv.advancec' (dlvAfter d ce L) L (ca, cfg) q0
      $$ [$Hlc1 $Hlc2 $Hlc3] Hadvancec [Hd1 Hrof Hrcpt Hpay] Hdlb Hr1 Hr2
    · unfold advanceP
      iexists d, ce, es, p'
      iframe Hd1 Hrof Hrcpt Hpay
      iexists ca
      iframe Hcamlb
      iexact HA1
    inext
    iintro Hfl Hans Hreq
    ihave ⟨Hcfg, %Hns⟩ := Hback $$ Hans
    wp_auto
    iapply HΦ
    ileft
    iframe Hcfg Hfl
    isplitl [Hd2 Hreq]
    · unfold nodeDriverChan
      iframe Hnode Hd2 Hdlb Hreq
    ipureintro; exact Hns
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-n.done` (2026-10-29, stage U9a): the node stopped; the driver idle again, at the log
    -- handed out (both `dlv` halves moved on above, one dropped)
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
    iapply node_done_recv_au γ nv.done' _ $$ Hdone
    iintro #Hst
    wp_auto
    iapply HΦ
    iright
    iframe Hst Hcfg
    unfold nodeDriverChan
    iframe Hnode Hd2 Hdlb
    iexists q0
    iframe Hr1 Hr2
  iapply BigAndL.bigAndL_nil.2
  itrivial
  -/

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (2026-10-28, stage U4a) A log's terms as a client sees it. -/
private theorem strip_terms (L : List EntryM) : (strip L).map LogEntry.term = L.map (·.Term') := by
  simp only [strip, List.map_map]; rfl

/-- A busy token with a snapshot's loan holds the loan's committed log. -/
private theorem busy_dlv (γn : NodeNames) (id : w64) (n : Loc) (ds es : List EntryM)
    (p : HardStateM) (l : SnapLoan) :
    nodeDriverBusy (GF := GF) γn id n ds es p (some l) ⊢
      nodeDriverBusy γn id n ds es p (some l) ∗ ⌜ds = l.dlv⌝ := by
  unfold nodeDriverBusy
  iintro ⟨#Hn, #Hlb, #Hld, %d, %ce, %p0, H1, H2, H3, %Hds, %q, Hq1, Hq2⟩
  isplitl [H1 H2 H3 Hq1 Hq2]
  · iframe Hn Hlb Hld
    iexists d, ce, p0
    iframe H1 H2 H3
    isplitr; · ipureintro; exact Hds
    iexists q; iframe Hq1 Hq2
  · ipureintro; exact Hds

/-- `node.Advance.spec` from the raw triple (2026-10-28, stage U4a; the conf-change decision
switch). A1 from the skips the client recorded (`skippedIn`: a lower bound of the decision map at
which the node's decoder, which decides nothing else, rejects every conf entry past the view,
`undecFree`). After a snapshot `Ready`, the view the raw triple returns is at the loan's committed log
and its fold over the loan's decisions (`loanCfg`, `RNMode.foldCfg`, `loanDec`); the snapshot's
certificate (`snapshotCert_made_impl`) names a committed prefix of the snapshot's index at the
membership `m` after it (`confAtU`, over decisions agreeing with the loan's: `fold_agree`), so the
view is at `m`, and its lists report `m`. -/
private theorem node.wp_Advance_impl
    (hA : EtcdGrove.node.Advance.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.Advance.spec (GF := GF) (hG := hG) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  unfold EtcdGrove.node.Advance.spec EtcdGrove.Cluster EtcdGrove.isCluster EtcdGrove.nodeConfig
    EtcdGrove.nodeDriver EtcdGrove.snapshotCert EtcdGrove.confAt EtcdGrove.nodeStopped
  intro n γ N st es L v Hh Hloan
  iintro %Φ ⟨#Hinit, #Hdc, Hdrv, Hrc, Hcfg, Hsk, Hcert⟩ HΦ
  ihave #Hdc0 := Hdc
  iunfold isClusterU at Hdc
  icases Hdc with ⟨%Hu, -⟩
  obtain ⟨⟨c0, gd, Hmr⟩, -, -⟩ := Hu
  obtain ⟨h0, h1, Hmd0⟩ := Hmr.mode
  have Hns : γ.raft.reNoSnap = false := Hmr.1.2.2.2.1
  -- the skips recorded past the view
  iunfold EtcdGrove.skippedIn at Hsk
  simp only [EtcdGrove.confDecided]
  icases skipped_range_decLb γ st.delivered v.applied st.delivered.length $$ Hsk
    with ⟨%Mk, #HMk, %PMk⟩
  iunfold nodeDriver at Hdrv
  icases Hdrv with ⟨%γn, %id, %ds, %Hf, #Hci, #Hlb0, Hstc, #Hdy, Htok⟩
  obtain ⟨Hnok, Hγs, Hds⟩ := Hf
  have Hmd : γn.mode = .dyn noDec (stOf c0) h0 h1 := by rw [Hnok.2.2.2.1, Hmd0]
  have Hd : γn.mode.isDyn = true := by rw [Hmd]; rfl
  icases Hdy with (%Hc | ⟨#Htb, #Hhc⟩)
  · rw [Hd] at Hc; cases Hc
  icases Htok with (⟨%Hh', -⟩ | ⟨%es0, %L0, %Hh', Htok⟩)
  · rw [Hh] at Hh'; cases Hh'
  rw [Hh] at Hh'
  cases Hh'
  ihave ⟨Htok, #Hn1, -⟩ := busy_isNode_lb γn id n ds es st.hardState L $$ Htok
  ihave %Hdl : ⌜∀ l, L = some l → ds = l.dlv⌝ $$ [Htok]
  · cases L with
    | none => ipureintro; intro l h; cases h
    | some l =>
      icases busy_dlv γn id n ds es st.hardState l $$ Htok with ⟨-, %H⟩
      ipureintro; intro l' h; cases h; exact H
  -- (2026-10-28, the decision switch) the loan's decisions
  ihave #Hld : iprop(∀ l, ⌜L = some l⌝ → decLb γ.raft l.decs ∗ ⌜∀ D, γ.raft.dyn = some D →
      D.fold l.decs l.dlv = some (snapTrip l.snap l.snap.Metadata'.ConfState'.lists).cfgM⌝) $$ [Htok]
  · cases L with
    | none => iintro %l %h; cases h
    | some l =>
      icases nodeDriverBusy_loanDec γn id n ds es st.hardState l $$ Htok with ⟨-, #HlD, %HlDf⟩
      iintro %l' %h
      cases h
      rw [← Hnok.1]
      iframe HlD
      ipureintro; exact HlDf
  iunfold nodeConfig at Hcfg
  icases Hcfg with ⟨%γn2, %id2, %Hf2, #Hn2, #Htab2, Hcf⟩
  icases isNode_id_agree γn γn2 id id2 n $$ Hn1 Hn2 with %Hid
  subst Hid
  icases nodeTabOk_agree γ id γn γn2 $$ Htb Htab2 with %Hnm
  ihave Hcf := nodeCfg_names γn2 γn Hnm.symm _ _ $$ Hcf
  iapply (hA γn id n ds es v.applied (stOf v.membership) st.hardState L) $$ [Htok Hrc Hcf]
  · iframe Hinit Htok Hcf
    isplitl
    · rw [Hγs]; iexact Hrc
    unfold undecFree
    iexists Mk
    rw [Hnok.1]
    iframe HMk
    ipureintro
    intro dec c0' h0' h1' hm
    rw [Hmd] at hm
    cases hm
    intro k' e' hk1 hk2 he hc
    have hl' : st.delivered[k']? = some (LogEntry.ofEntryM e') := by
      rw [← Hds]; unfold strip; rw [List.getElem?_map, he]; rfl
    have hlen : (ds.take k').length = k' := by
      have := (List.getElem?_eq_some_iff.mp he).1
      rw [List.length_take]; omega
    have hk2' : k' < st.delivered.length := by rw [← Hds, strip_length]; exact hk2
    show (Mk.lookup (ds.take k').length).map ccDecOf = some .reject
    rw [hlen, PMk k' _ hk1 hk2' hl' hc]; rfl
  iintro !> Hpost
  icases Hpost with (⟨Hdrv, Hcf, -, #Hw⟩ | ⟨#Hstp, Hdrv, -⟩)
  rotate_left
  · -- (2026-10-29, stage U9a) the node stopped
    ihave ⟨Hdrv, #Hnc⟩ := nodeDriver_isNode γn id n ds st.hardState $$ Hdrv
    iapply HΦ
    iright
    isplitr
    · unfold nodeStopped
      iexists γn, id
      iframe Hnc Hstp
      isplitr
      · ipureintro; exact Hnok
      iright; iexact Htb
    unfold nodeDriver
    iexists γn, id, ds
    isplitr
    · ipureintro; exact ⟨Hnok, Hγs, Hds⟩
    iframe Hci Hlb0 Hstc
    isplitr
    · iright; iframe Htb Hhc
    ileft
    isplitr
    · ipureintro; rfl
    iexact Hdrv
  iapply HΦ
  ileft
  isplitl [Hdrv Hstc]
  · unfold nodeDriver
    iexists γn, id, ds
    isplitr
    · ipureintro; exact ⟨Hnok, Hγs, Hds⟩
    iframe Hci Hlb0 Hstc
    isplitr
    · iright; iframe Htb Hhc
    ileft
    isplitr
    · ipureintro; rfl
    iexact Hdrv
  cases L with
  | none =>
    simp only
    rw [loanCfg_none]
    isplitl [Hcf]
    · unfold nodeConfig
      iexists γn, id
      iframe Hn1 Htb Hcf
      ipureintro; exact ⟨Hnok, Hd, Hf2.2.2⟩
    iunfold reqOf at Hw
    iunfold reqWit at Hw
    icases Hw with ⟨%x, #Hx, %Hle, #Hts⟩
    iexists x
    rw [← Hγs]
    iframe Hx
    isplitr
    · ipureintro
      rw [← Hds, strip_length]; exact Hle
    rw [← Hds, strip_terms]; iexact Hts
  | some l =>
    simp only
    have Hli := Hloan l rfl
    have Hdsl := Hdl l rfl
    subst Hdsl
    icases Hld $$ %l %rfl with ⟨#HlD, %HlDf⟩
    icases ApiImpl.snapshotCert_made_impl γ N _ $$ [Hdc0 Hcert] with ⟨%L', %m, #HL', #Ha, -, %P⟩
    · iframe Hdc0 Hcert
    obtain ⟨HL'len, -, Hcl, Hal⟩ := P
    ihave #Ha' := Ha
    iunfold confAtU at Ha'
    icases Ha' with ⟨%l1, %M1, #H1, #HM1, %P1⟩
    obtain ⟨hk1, c1, g1, hm1, hf1⟩ := P1
    icases isCommittedLogLb_agree_impl γ st.delivered l1 $$ [Hlb0 H1] with %Hcmp
    · iframe Hlb0 H1
    icases decLb_compat γ.raft l.decs M1 $$ [HlD HM1] with %Hcp
    · iframe HlD HM1
    have HD : γ.raft.dyn = some (DynCfg.ofFold noDec (stOf c0) h0) := Hmr.1.2.2.1
    have Hf0 := HlDf _ HD
    rw [Hmr.fold _ HD l.decs l.dlv] at Hf0
    obtain ⟨x, Hx, -⟩ := Option.map_eq_some_iff.1 Hf0
    have Hlen : st.delivered.length = L'.length := by
      rw [← Hds, strip_length, Hli, HL'len]; rfl
    have Hx' : decFold l.decs c0 (st.delivered.take L'.length) = some x := by
      rw [← Hlen, List.take_length, ← Hds]; exact Hx
    have Hxm : x = m := fold_agree Hmr hm1 Hcp Hcmp (by omega) hk1 Hx' hf1
    subst Hxm
    have Hfold : cfgFold (effDec noDec l.decs) (stOf c0) l.dlv = some (stOf x) := by
      rw [cfgFold_decs l.decs c0 Hmr.valid l.dlv, Hx]; rfl
    have Hlc : loanCfg γn.mode (some l) (v.applied, stOf v.membership) =
        (uint.nat l.snap.Metadata'.Index', stOf x) := by
      unfold loanCfg
      simp only
      rw [ite_eq_left Hd, Hmd]
      simp only [RNMode.foldCfg, Hfold, Option.getD_some, Hli]
    rw [Hlc]
    have Hmv : x.Valid := decFold_valid M1 c1 x _ hm1.valid hf1
    iexists x
    isplitl [Hcf]
    · unfold nodeConfig
      iexists γn, id
      iframe Hn1 Htb Hcf
      ipureintro; exact ⟨Hnok, Hd, Hmv.2⟩
    isplitr
    · rw [show uint.nat l.snap.Metadata'.Index' = L'.length from HL'len.symm]
      iexact Ha
    ipureintro
    obtain ⟨c1', c2, c3, c4⟩ := Hcl
    exact ⟨c1', c2, c3, c4, Hal⟩
  -/

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.Advance.wp_proof :
    node.Advance.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_Advance_impl (node.Advance.wp_raw)

end proof

end EtcdGrove
end Perennial
