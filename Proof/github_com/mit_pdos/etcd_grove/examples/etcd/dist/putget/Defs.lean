/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the machines' shares of the start, over the interim cross-machine vocabulary

What `putget_safe`'s start (`putget_shares`, `TopLevelRobustness.lean`) hands each machine, over the
interim vocabulary of `etcd/dist/S2Interim.lean` and the cluster start's pieces (`etcd/dist/ClusterStart.lean`;
`notes/putget-dist-plan.md` §12, `notes/etcd-dist-plan.md` §18.3, O1 option B: the start fixes the cluster's
view `c.view`, no publication):

* `memberShare`: the one-member cluster's names `c` as `clusterAllocN` chose them (`ClusterOk`), the
  cluster's facts, the member's slice, and the member's client address set to serve etcd's table for its id
  at the view (`etcdAddrAt`);
* `clientShare`: the member's address fact at the view, auth off, and the client's putget invariant at the
  view's KV names (`etcd_dist.putGetInvK`, the in-process putget's `client.putGetInv` at KV names), at every
  heap over the global ghost state (the client's heap is not the start's; the invariant reads the heap only
  through its global part), allocated by the start (`putGetInvK_alloc`) from the cluster's `etcdKV`.

And `wenv_nonempty`: a watch environment exists (`etcdstart.NewClient.spec` takes one, which the
client's `Put`/`Get` never read). (Until 2026-11-25 the member published its view, `env_publish`, with the
invariant, `putgetPub`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClusterStart
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelDefs
public import Proof.go_etcd_io.etcd.client.v3.PutThenGet
public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Net etcd_dist

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **The heap of the local ghost state `L` at the Go local context `lctx`** (over the global `G`): the
statement's form of a machine's heap (`putgetHeapAt`), at which the program's `go.Semantics` over `lctx`
applies. -/
abbrev heapAt (G : GooseGlobalGS .hasLC GF) (L : GooseLocalGS GF) (lctx : GoLocalContext) :
    HeapGS .hasLC GF :=
  ⟨G, { L with goose_go_local_context := lctx }⟩

end heap

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [lctx : GoLocalContext] [sem : go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **The member's share** of the start (see the file header): the one-member cluster's names `c`
(`clusterAllocN`'s, `ClusterOk` at the peers `[id]`, lease mode `none`, no compaction), the cluster's
facts, the member's slice, its client address set to serve etcd's table for `id` at the view `c.view`. -/
def memberShare (ep : GoString) (c : ClusterNames) (ctxs : List (List w8)) (boot : List LogEntry)
    (id : w64) : IProp GF :=
  iprop(⌜ClusterOk c [id] boot .none false 0 [id]⌝ ∗ clusterFactsOf c ∗
    memberSliceOf c [id] [id] ctxs (LogEntry.toEntries boot 0) id ∗ etcdAddrAt ep c.view id)

/-- **The member machine's share, once its addresses pass its check** (2026-11-24): `Member` returns at
once unless `peer` and `client` are valid (`AddrOk`) and distinct, so the start owes it `memberShare` only
then. -/
def memberShareIf (peer ep : GoString) (c : ClusterNames) (ctxs : List (List w8))
    (boot : List LogEntry) (id : w64) : IProp GF :=
  iprop(⌜Net.addrOk peer = true ∧ Net.addrOk ep = true ∧ peer ≠ ep⌝ -∗ memberShare ep c ctxs boot id)

/-- **The client's share** (persistent; see the file header): the member's address fact at the view `Γ`,
auth off, and the client's putget invariant at `Γ`'s KV names, at every local ghost state over `G`. -/
def clientShare (ep : GoString) (Γ : DistView) (mid : w64) : IProp GF :=
  iprop(etcdAddrAt ep Γ mid ∗ ⌜Γ.auth = false⌝ ∗
    ∃ γf : GName, ∀ L : GooseLocalGS GF, putGetInvK (hG := heapAt G L lctx) Γ.kv γf go!"k" go!"v")

instance clientShare_persistent (ep : GoString) (Γ : DistView) (mid : w64) :
    Persistent (clientShare (GF := GF) ep Γ mid) := by
  unfold clientShare; infer_instance

/-- **The client machine's share, once its address passes its check** (2026-11-24): `Client` returns at
once unless its address is valid (`AddrOk`). -/
def clientShareIf (ep : GoString) (Γ : DistView) (mid : w64) : IProp GF :=
  iprop(⌜Net.addrOk ep = true⌝ -∗ clientShare ep Γ mid)

end shares

section allocG
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors}
variable [lctx : GoLocalContext] [sem : go.Semantics] [G : GooseGlobalGS .hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

open Iris.ProofMode in
/-- **The client's putget invariant, allocated over the global ghost state** (`client.putGetInv_alloc_log`'s,
at no machine's heap: the invariant reads the heap only through its global part), at every local ghost
state over `G`. -/
theorem putGetInvK_alloc (γk : KVNames) (σ : KVState) (key val : GoString) :
    etcdKV (GF := GF) γk σ ⊢ |={⊤}=> ∃ γf : GName,
      ∀ L : GooseLocalGS GF, putGetInvK (hG := heapAt G L lctx) γk γf key val := by
  iintro Hσ
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γf, Hm, -⟩
  imod inv_alloc client.kvClientN ⊤ (iprop(∃ (σ : KVState) (n : Nat), etcdKV γk σ ∗
      monoNatAuthOwn γf 1 n ∗ ⌜client.putGetOk key val σ n⌝)) $$ [Hσ Hm] with #Hinv
  · inext; iexists σ, 0; iframe Hσ Hm
    ipureintro; exact ⟨KVState.kvs_sorted _, fun h => absurd h (by omega)⟩
  imodintro
  iexists γf
  iintro %L
  iunfold putGetInvK
  iexact Hinv

open Iris.ProofMode in
/-- **A putget invariant at fresh KV names** (no cluster): a fresh KV state variable at the empty state, its
half the invariant's (`putGetInvK_alloc`), at KV names default but for it. For a start whose configuration
the programs refuse: its client's share needs an invariant, at a view no member serves. -/
theorem putGetInvK_alloc_fresh (key val : GoString) :
    ⊢ |={⊤}=> ∃ (γk : KVNames) (γf : GName), ∀ L : GooseLocalGS GF,
        putGetInvK (hG := heapAt G L lctx) γk γf key val := by
  istart
  imod (ghostVar_alloc (GF := GF) ({ compacted := 0, base := ∅, changes := [] } : KVState)) with ⟨%γ, Hv⟩
  ihave ⟨Hv1, -⟩ := (ghostVar_split_half γ 1 _).1 $$ Hv
  imod (putGetInvK_alloc { (default : KVNames) with st := γ }
      ({ compacted := 0, base := ∅, changes := [] } : KVState) key val) $$ [Hv1] with ⟨%γf, #Hinv⟩
  · iunfold etcdKV
    iexact Hv1
  imodintro
  iexists _, γf
  iexact Hinv

end allocG

/-- Fills a goal of data with defaults (`default`, `True`, `1`, under binders, field by field): for
`wenv_nonempty`'s watch environment, whose fields `Put`/`Get` never read. -/
syntax "putget_fill" : tactic
macro_rules
  | `(tactic| putget_fill) => `(tactic| first
    | exact default
    | exact iprop(True)
    | exact (1 : Qp)
    | (intro _; putget_fill)
    | (constructor <;> putget_fill))

section wenv
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **An etcd model whose propositions are all `False`** (its laws hold vacuously): the watch
environment's model in `wenv_nonempty`, never read. -/
def wenvFalseModel : EtcdModel GF where
  etcdState _ _ _ := iprop(False)
  etcdState_agree := by intros; exact false_sep.1.trans false_elim
  etcdState_revs := by intros; exact false_elim
  etcdState_keys := by intros; exact false_elim
  etcdState_vals := by intros; exact false_elim
  etcdState_create_persist := by intros; exact false_sep.1.trans false_elim
  etcdState_modrev_det := by intros; exact false_sep.1.trans false_elim
  etcdState_modrev_persist := by intros; exact false_sep.1.trans false_elim
  etcdReachedAt _ := iprop(False)
  etcdReachedAt_timeless := by intros; infer_instance
  etcdReadAt _ := iprop(False)
  etcdReadAt_persistent := by intros; infer_instance
  etcdReadAt_timeless := by intros; infer_instance
  etcdRevToken _ := iprop(False)
  etcdRevToken_excl := by intros; exact false_sep.1.trans false_elim
  EtcdStep _ _ _ _ := iprop(False)
  EtcdStep_persistent := by intros; infer_instance
  EtcdStep_timeless := by intros; infer_instance
  etcdStep_transfer := by intros; exact false_sep.1.trans false_elim
  etcdStep_compose := by intros; exact false_sep.1.trans false_elim
  etcdStep_restrict := by intros; exact false_elim
  etcdStep_delete_present := by intros; exact false_sep.1.trans false_elim

/-- **A watch environment exists**: `etcdstart.NewClient.spec` holds at every one, and the client's
`Put`/`Get` read none of it; the client machine's proof picks one (defaults field by field, the model
`wenvFalseModel`; a store name from the mvcc API's law, `names_nonempty`, since `MvccName` is sealed). -/
theorem wenv_nonempty (hne : mvcc.api.names_nonempty.law) : Nonempty (client.WEnv GF) := by
  haveI : Inhabited mvcc.api.MvccName := Classical.inhabited_of_nonempty hne.1
  have hA : Nonempty (apply.AEnv GF) := ⟨by putget_fill⟩
  have hW : Nonempty (v3rpc.SrvW GF) := ⟨by putget_fill⟩
  obtain ⟨E⟩ := hA
  obtain ⟨W⟩ := hW
  exact ⟨⟨⟨null, E, null, 0, 0, 0, null, 0⟩, [], [], null, null, [], null, wenvFalseModel,
    fun _ => iprop(True), fun _ => ([], ⟨null, E, null, 0, 0, 0, null, 0⟩), 0, default, W,
    fun _ => W⟩⟩

end wenv


end etcd_putget_dist
end EtcdGrove
end Perennial

end
