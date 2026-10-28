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
import Proof.go_etcd_io.raft.v3.InvApiDyn

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
committed log handed out so far. `n.done` is never closed (`Stop` is out of scope).

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
  -- (2026-10-15, stage N) **A1**, in the dynamic mode: every conf entry of the committed log
  -- handed out has been applied (`node.ApplyConfChange`): none past the driver's configuration
  -- index (`issues/raft-advance-before-applyconfchange.md`)
  (γ.mode.isDyn = true → NoConfIn ds ca ds.length) →
  -- (2026-10-28, stage U3d) dynamically, a snapshot's `ConfState` no auto-leave one
  -- (`RawNode.Advance`'s, until U5)
  (∀ l, L = some l → γ.mode.isDyn = true → γ.raft.reNoSnap = false →
    l.snap.Metadata'.ConfState'.AutoLeave' = false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      nodeDriverBusy γ id n ds es p L ∗ advReceipt γ.stor es L ∗ nodeCfg γ ca cfg }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); nodeDriverChan γ id n ds p ∗
      -- (2026-10-28, stage U3d) the view of the configuration: after a snapshot `Ready`,
      -- dynamically, the snapshot's (`loanCfg`), which a snapshot `Ready` has only outside the
      -- no-snapshot mode
      nodeCfg γ (loanCfg γ.mode L (ca, cfg)).1 (loanCfg γ.mode L (ca, cfg)).2 ∗
      ⌜L ≠ none → γ.raft.reNoSnap = false⌝ ∗
      -- (D19i part 1) the floor's witness for `ds`; (D22 S-d4) after a `Ready` without a snapshot,
      -- unless one was restored since (`reqWit`)
      reqWit γ (reqOf L ds) }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `dlv` halves move on past the `Ready` (`run` will recognize its record), one goes
with the receipt on `advancec`; `n.done` never fires. -/
private theorem node.Advance.wp_raw : node.Advance.specRaw (GF := GF) (hG := hG) := by
  intro γ id n ds es ca cfg p' L HA1 Hal
  wp_start as ⟨Hbusy, Hrcpt, Hcfg⟩
  unfold nodeDriverBusy
  icases Hbusy with ⟨#Hnode, #Hdlb, %d, %ce, %p, Hd1, Hd2, Hrof, %Hds, %q0, Hr1, Hr2⟩
  ihave #Hcamlb : monoNatLbOwn γ.cam ca $$ [Hcfg]
  · unfold nodeCfg; icases Hcfg with ⟨-, -, $⟩
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
    iapply adv_send_au γ nv.rn' id nv.advancec' (dlvAfter d ce L) L (ca, cfg) q0
      $$ [$Hlc1 $Hlc2 $Hlc3] Hadvancec [Hd1 Hrof Hrcpt Hpay] Hdlb Hr1 Hr2
    · unfold advanceP
      iexists d, ce, es, p'
      iframe Hd1 Hrof Hrcpt Hpay
      isplitr
      · ipureintro; exact Hal
      iexists ca
      iframe Hcamlb
      ipureintro; exact HA1
    inext
    iintro Hfl Hans Hreq
    ihave ⟨Hcfg, %Hns⟩ := Hback $$ Hans
    wp_auto
    iapply HΦ
    iframe Hcfg Hfl
    isplitl [Hd2 Hreq]
    · unfold nodeDriverChan
      iframe Hnode Hd2 Hdlb Hreq
    ipureintro; exact Hns
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-n.done`: never
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHandshake_isChan $$ Hdone
    iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `node.Advance.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_Advance_impl
    (hA : EtcdGrove.node.Advance.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.Advance.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.Advance.spec EtcdGrove.Cluster EtcdGrove.isStaticCluster EtcdGrove.nodeDriver
  intro n γ N vs so st es L Hh
  iintro %Φ ⟨#Hinit, #Hst, Hdrv, Hrc⟩ HΦ
  iunfold nodeDriver at Hdrv
  icases Hdrv with ⟨%γn, %id, %ds, %Hf, #Hci, #Hlb0, Hstc, #Hdy, Htok⟩
  obtain ⟨Hnok, Hγs, Hds⟩ := Hf
  iunfold isStaticCluster at Hst
  icases Hst with ⟨%Hsn, -⟩
  have Hmd : γn.mode = .static := by rw [Hnok.2.2.2.1, Hsn.2.2.2.2.1, RNMode.all_self]
  icases Hstc with (%Hd | ⟨#Hlink, ⟨%ca, %cfg, Hcfg⟩⟩)
  · exfalso; rw [Hmd] at Hd; cases Hd
  icases Htok with (⟨%Hh', -⟩ | ⟨%es0, %L0, %Hh', Htok⟩)
  · rw [Hh] at Hh'; cases Hh'
  rw [Hh] at Hh'
  cases Hh'
  iapply (hA γn id n ds es ca cfg st.hardState L
    (fun h => by rw [Hmd] at h; cases h) (fun _ _ h _ => by rw [Hmd] at h; cases h)) $$ [Htok Hrc Hcfg]
  · iframe Hinit Htok Hcfg
    rw [Hγs]; iexact Hrc
  iintro !> ⟨Hdrv, Hcfg, -, #Hw⟩
  rw [loanCfg_static (by rw [Hmd]; rfl)]
  iapply HΦ
  isplitl [Hdrv Hcfg]
  · unfold nodeDriver
    iexists γn, id, ds
    isplitr
    · ipureintro; exact ⟨Hnok, Hγs, Hds⟩
    iframe Hci Hlb0 Hdy
    isplitl [Hcfg]
    · iright; iframe Hlink; iexists ca, cfg; iexact Hcfg
    ileft
    isplitr
    · ipureintro; rfl
    iexact Hdrv
  cases L with
  | none =>
    simp only
    iunfold reqOf at Hw
    iunfold reqWit at Hw
    icases Hw with ⟨%x, #Hx, %Hle⟩
    iexists x
    rw [← Hγs]
    iframe Hx
    ipureintro
    rw [← Hds, strip_length]; exact Hle
  | some l => simp only; itrivial

/-- `node.Advance.dynamicSpec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_Advance_dynamic_impl
    (hA : EtcdGrove.node.Advance.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.Advance.dynamicSpec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.Advance.dynamicSpec EtcdGrove.Cluster EtcdGrove.isDynamicCluster EtcdGrove.nodeConfig EtcdGrove.nodeDriver
  intro n γ N c0 decode st es L v Hh Hno
  iintro %Φ ⟨#Hinit, #Hdc, Hdrv, Hrc, Hcfg⟩ HΦ
  iunfold isDynamicCluster at Hdc
  icases Hdc with ⟨%Hdn, -⟩
  iunfold nodeDriver at Hdrv
  icases Hdrv with ⟨%γn, %id, %ds, %Hf, #Hci, #Hlb0, Hstc, #Hdy, Htok⟩
  obtain ⟨Hnok, Hγs, Hds⟩ := Hf
  have Hd := Hdn.isDyn Hnok
  icases Hdy with (%Hc | ⟨#Htb, #Hhc⟩)
  · rw [Hd] at Hc; cases Hc
  icases Htok with (⟨%Hh', -⟩ | ⟨%es0, %L0, %Hh', Htok⟩)
  · rw [Hh] at Hh'; cases Hh'
  rw [Hh] at Hh'
  cases Hh'
  ihave ⟨Htok, #Hn1, -⟩ := busy_isNode_lb γn id n ds es st.hardState L $$ Htok
  iunfold nodeConfig at Hcfg
  icases Hcfg with ⟨%γn2, %id2, %Hf2, #Hn2, #Htab2, Hcf⟩
  icases isNode_id_agree γn γn2 id id2 n $$ Hn1 Hn2 with %Hid
  subst Hid
  icases nodeTabOk_agree γ id γn γn2 $$ Htb Htab2 with %Hnm
  ihave Hcf := nodeCfg_names γn2 γn Hnm.symm _ _ $$ Hcf
  have HA1 : NoConfIn ds v.applied ds.length := by
    have := noConfIn_of_strip ds v.applied ds.length
    rw [Hds] at this
    apply this
    have Hl : ds.length = st.delivered.length := by rw [← Hds, strip_length]
    rw [Hl]; exact Hno
  -- a dynamic cluster is in raft's no-snapshot mode: no snapshot `Ready`
  have Hns : γn.raft.reNoSnap = true := by rw [Hnok.1]; exact Hdn.noSnap
  iapply (hA γn id n ds es v.applied (stOf v.membership) st.hardState L (fun _ => HA1)
    (fun _ _ _ h => by rw [Hns] at h; cases h)) $$ [Htok Hrc Hcf]
  · iframe Hinit Htok Hcf
    rw [Hγs]; iexact Hrc
  iintro !> ⟨Hdrv, Hcf, %HLn, #Hw⟩
  have HL : L = none := by
    cases L with
    | none => rfl
    | some l => have := HLn (by simp); rw [Hns] at this; cases this
  subst HL
  rw [loanCfg_none]
  iapply HΦ
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
  simp only
  isplitl [Hcf]
  · unfold nodeConfig
    iexists γn, id
    iframe Hn1 Htb Hcf
    ipureintro; exact ⟨Hnok, Hd, Hf2.2.2⟩
  iunfold reqOf at Hw
  iunfold reqWit at Hw
  icases Hw with ⟨%x, #Hx, %Hle⟩
  iexists x
  rw [← Hγs]
  iframe Hx
  ipureintro
  rw [← Hds, strip_length]; exact Hle

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

theorem node.Advance.wp_proof_dynamic :
    node.Advance.dynamicSpec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_Advance_dynamic_impl (node.Advance.wp_raw)

end proof

end EtcdGrove
end Perennial
