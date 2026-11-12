/-
Lean-first (no Rocq counterpart). **`node.Advance`'s traced triple, stated** (2026-11-12, trace-check
implementation step 1; the design's §3.1, A5): `node.Advance.tracedSpec` and its instance
`node.Advance.spec_of_traced`, over raft's sealed token `sentTok` (the harness's `trTok`,
`TracedNodeApi.lean`, which re-exports this module). Apart from `TracedNodeApi` because the proof
(`NodeAdvanceTraced.lean`) is reached from raft's `Link.lean`, which the server imports, and
`TracedNodeApi`'s `trTok` clashes with etcd's rafthttp `trTok` there.
-/
module

public import Spec.go_etcd_io.raft.v3.node__Advance

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`node.Advance()`, traced** (the design's §3.1, A5): `node.Advance.spec`'s precondition with the
driver's claim on the messages `ms` of the `Ready` it advances (`readyToksClaim`, from `readyGotT`);
its post, unless the node stopped, also the messages' tokens. **The one proof**
(`node.Advance.tracedSpec_proof`, `NodeAdvanceTraced.lean`, linked in `TracedLinked.lean`):
`node.Advance.spec` is its instance at `ms = []` (`node.Advance.spec_of_traced`). -/
abbrev node.Advance.tracedSpec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (st : NodeDriverState) (es : List EntryM)
    (L : Option SnapLoan) (v : ConfigView) (ms : List QMsg),
  st.handling = some (es, L) →
  (∀ l, L = some l → l.dlv.length = uint.nat l.snap.Metadata'.Index') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isCluster γ N ∗ isNode n γ N id ∗
      nodeDriver n γ N st ∗ advReceipt st.storage st.delivered.length es L ∗ nodeConfig n γ N v ∗
      (match L with
       | none => skippedIn γ st.delivered v.applied st.delivered.length
       | some l => snapshotCert γ N (snapTrip l.snap l.snap.Metadata'.ConfState'.lists)) ∗
      readyToksClaim n γ N ms }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); (nodeDriver n γ N { st with handling := none } ∗
      nodeAppliedLb γ st.key st.delivered.length ∗
      (match L with
      | none => nodeConfig n γ N v
      | some l => ∃ m : Membership,
          nodeConfig n γ N ⟨uint.nat l.snap.Metadata'.Index', m⟩ ∗
          confAt γ (uint.nat l.snap.Metadata'.Index') m ∗
          ⌜confStateIs l.snap.Metadata'.ConfState' m⌝) ∗
      [∗list] q ∈ ms, sentTok γ q.st) ∨
    (nodeStopped n γ N ∗ nodeDriver n γ N { st with handling := none }) }}

open Iris.ProofMode in
/-- **`node.Advance.spec` is `node.Advance.tracedSpec`'s instance** at `ms = []` (A5): the claim by
`readyToksClaim_nil`, the empty list of tokens dropped. Its text is unchanged. -/
theorem node.Advance.spec_of_traced (h : node.Advance.tracedSpec (GF := GF)) :
    node.Advance.spec (GF := GF) (hG := hG) := by
  intro n γ N id st es L v Hh HL
  iintro %Φ Hpre HΦ
  iapply (h n γ N id st es L v [] Hh HL) $$ [Hpre] [HΦ]
  · icases Hpre with ⟨Hi, Hc, Hn, Hd, Hr, Hv, Hm⟩
    ihave Hcl := readyToksClaim_nil (GF := GF) n γ N
    iframe Hi Hc Hn Hd Hr Hv Hm Hcl
  · inext
    iintro Hpost
    iapply HΦ
    icases Hpost with (⟨Hd, Ha, Hm, -⟩ | Hs)
    · ileft; iframe Hd Ha Hm
    · iright; iexact Hs

end spec

end EtcdGrove
end Perennial
