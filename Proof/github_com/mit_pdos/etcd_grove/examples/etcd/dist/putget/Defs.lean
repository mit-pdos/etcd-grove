/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the machines' shares of the start, over the interim cross-machine vocabulary

What `putget_safe`'s start (`putget_start`, `TopLevelRobustness.lean`) hands each machine, over the
interim vocabulary of `etcd/dist/S2Interim.lean` (`notes/putget-dist-plan.md` §12):

* `memberShare`: the member's client address set to serve etcd's KV calls for the publication name
  `γE` and the member id (`etcdAddrAt`), its half of the publication token, the publication invariant;
* `clientShare`: the same address fact and the publication invariant;
* `putgetPub`: what the member publishes with its view for the client: the client's invariant
  (`client.putGetInv`, the in-process putget's) at read names whose KV state variable is the view's,
  at every heap over the global ghost state (the client's heap is not the member's; `putGetInv`
  reads the heap only through its global part, `putGetInv_heap`);
* `memberPubOk`: the member's obligation on a `Pub` (what `Member.spec` takes): a putget invariant
  gives `Pub` of the view of its KV state variable.

And `wenv_nonempty`: a watch environment exists (`etcdstart.NewClient.spec` takes one, which the
client's `Put`/`Get` never read).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
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

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **The member's share** of the start: its client address set to serve etcd's KV calls for `γE`
and its member id (`etcdAddrAt`), its half of the publication token, the publication invariant. -/
def memberShare (client : GoString) (γE : GName) (mid : w64) (Pub : EnvView → IProp GF) :
    IProp GF :=
  iprop(etcdAddrAt client γE mid ∗ envPubHalf γE ∗ envPubInv γE Pub)

/-- **The member machine's share, once its addresses pass its check** (2026-11-24): `Member` returns at
once unless `peer` and `client` are valid (`AddrOk`) and distinct, so the start owes it `memberShare` only
then. -/
def memberShareIf (peer client : GoString) (γE : GName) (mid : w64) (Pub : EnvView → IProp GF) :
    IProp GF :=
  iprop(⌜Net.addrOk peer = true ∧ Net.addrOk client = true ∧ peer ≠ client⌝ -∗
    memberShare client γE mid Pub)

/-- **The client's share** (persistent): the member's address fact and the publication invariant. -/
def clientShare (client : GoString) (γE : GName) (mid : w64) (Pub : EnvView → IProp GF) :
    IProp GF :=
  iprop(etcdAddrAt client γE mid ∗ envPubInv γE Pub)

/-- **The client machine's share, once its address passes its check** (2026-11-24): `Client` returns at
once unless its address is valid (`AddrOk`). -/
def clientShareIf (client : GoString) (γE : GName) (mid : w64) (Pub : EnvView → IProp GF) :
    IProp GF :=
  iprop(⌜Net.addrOk client = true⌝ -∗ clientShare client γE mid Pub)

instance clientShare_persistent (client : GoString) (γE : GName) (mid : w64)
    (Pub : EnvView → IProp GF) : Persistent (clientShare client γE mid Pub) := by
  unfold clientShare; infer_instance

end shares

section pub
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **The member's obligation on `Pub`** (persistent; `Member.spec`'s, at the member's heap): a putget
invariant gives `Pub` of the view of its KV state variable. -/
def memberPubOk [hG : HeapGS .hasLC GF] [sem : go.Semantics] (Pub : EnvView → IProp GF) :
    IProp GF :=
  iprop(□ ∀ (γr : ReadNames) (γf : GName),
    client.putGetInv γr γf go!"k" go!"v" -∗ Pub ⟨γr.kv.st⟩)

instance memberPubOk_persistent [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    (Pub : EnvView → IProp GF) : Persistent (memberPubOk Pub) := by
  unfold memberPubOk; infer_instance

/-- **The heap of the local ghost state `L` at the Go local context `lctx`** (over the global `G`): the
statement's form of a machine's heap (`putgetHeapAt`), at which the program's `go.Semantics` over `lctx`
applies. -/
abbrev heapAt (G : GooseGlobalGS .hasLC GF) (L : GooseLocalGS GF) (lctx : GoLocalContext) :
    HeapGS .hasLC GF :=
  ⟨G, { L with goose_go_local_context := lctx }⟩

variable [lctx : GoLocalContext] [sem : go.Semantics]

/-- **`putGetInv` reads the heap only through its global part** (and the Go semantics): at two local
ghost states over the same global one and Go local context, it is the same proposition. -/
theorem putGetInv_heap (G : GooseGlobalGS .hasLC GF) (L L' : GooseLocalGS GF) (γr : ReadNames)
    (γf : GName) (k v : GoString) :
    client.putGetInv (GF := GF) (hG := heapAt G L lctx) γr γf k v =
      client.putGetInv (hG := heapAt G L' lctx) γr γf k v :=
  rfl

variable [G : GooseGlobalGS .hasLC GF]

/-- **What the member publishes with its view** (see the file header): the client's invariant at
read names whose KV state variable is the view's, at every local ghost state over the global one (at
the Go local context `lctx`). -/
def putgetPub (ν : EnvView) : IProp GF :=
  iprop(∃ (γr : ReadNames) (γf : GName), ⌜γr.kv.st = ν.st⌝ ∗
    ∀ L : GooseLocalGS GF, client.putGetInv (hG := heapAt G L lctx) γr γf go!"k" go!"v")

open Iris.ProofMode in
/-- **`putgetPub` meets the member's obligation**, at any local ghost state. -/
theorem memberPubOk_putgetPub (L : GooseLocalGS GF) :
    ⊢ memberPubOk (hG := heapAt G L lctx) putgetPub := by
  unfold memberPubOk putgetPub
  imodintro
  iintro %γr %γf #Hinv
  iexists γr, γf
  isplitr
  · ipureintro; rfl
  iintro %L'
  rw [putGetInv_heap G L' L]
  iexact Hinv

end pub

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
