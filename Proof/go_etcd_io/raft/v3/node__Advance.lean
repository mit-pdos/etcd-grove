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
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

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
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

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
