/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the machines' shares of the start, against phase 7 S2's draft names

What `putget_safe`'s start (`putget_start`, `TopLevelRobustness.lean`) hands each machine, over the
placeholder `S2Draft` (`S2Draft.lean`; `notes/putget-dist-plan.md`, sections 8 and 10):

* `memberShare`: the member's client address set to serve etcd's table at `γE` (`grpcAddrAt`), its half of
  the publication token, the publication invariant;
* `clientShare`: etcd's KV registrations before the view (`kvRegsPub`), the publication invariant;
* `putgetPub`: what the member publishes with its view for the client: the client's invariant
  (`client.putGetInv`, the in-process putget's) at the view's read names, at every heap over the global
  ghost state (the client's heap is not the member's; `putGetInv` reads the heap only through its global
  part, `putGetInv_heap`);
* `memberPubOk`: the member's obligation on a `Pub` (what `Member.spec` takes): a putget invariant at a
  view's read names gives `Pub` of the view.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.S2Draft
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelDefs
public import Proof.go_etcd_io.etcd.client.v3.PutThenGet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **The member's share** of the start: its client address set to serve etcd's table at `γE`
(`grpcAddrAt`), its half of the publication token, the publication invariant. -/
def memberShare (S : S2Draft GF) (client : GoString) (γE : GName) (mid : w64)
    (Pub : S.EnvView → IProp GF) : IProp GF :=
  iprop(S.grpcAddrAt client (S.etcdSvc γE mid) ∗ S.envPubHalf γE ∗ S.envPubInv γE Pub)

/-- **The client's share**: etcd's KV registrations before the view (`kvRegsPub`), the publication
invariant. -/
def clientShare (S : S2Draft GF) (client : GoString) (γE : GName) (mid : w64)
    (Pub : S.EnvView → IProp GF) : IProp GF :=
  iprop(S.kvRegsPub client γE mid ∗ S.envPubInv γE Pub)

end shares

section pub
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **The member's obligation on `Pub`** (persistent; `Member.spec`'s, at the member's heap): a putget
invariant at a view's read names gives `Pub` of the view. -/
def memberPubOk [hG : HeapGS .hasLC GF] [sem : go.Semantics] [HasExt netExt] [π : NetProtoGS]
    (S : S2Draft (G := hG.goose_globalGS) GF) (Pub : S.EnvView → IProp GF) : IProp GF :=
  iprop(□ ∀ (ν : S.EnvView) (γf : GName),
    client.putGetInv (S.viewRd ν) γf go!"k" go!"v" -∗ Pub ν)

instance memberPubOk_persistent [hG : HeapGS .hasLC GF] [sem : go.Semantics] [HasExt netExt]
    [π : NetProtoGS] (S : S2Draft (G := hG.goose_globalGS) GF) (Pub : S.EnvView → IProp GF) :
    Persistent (memberPubOk S Pub) := by
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

variable [HasExt netExt] [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **What the member publishes with its view** (see the file header): the client's invariant at the
view's read names, at every local ghost state over the global one (at the Go local context `lctx`). -/
def putgetPub (S : S2Draft GF) (ν : S.EnvView) : IProp GF :=
  iprop(∃ γf : GName, ∀ L : GooseLocalGS GF,
    client.putGetInv (hG := heapAt G L lctx) (S.viewRd ν) γf go!"k" go!"v")

open Iris.ProofMode in
/-- **`putgetPub` meets the member's obligation**, at any local ghost state. -/
theorem memberPubOk_putgetPub (L : GooseLocalGS GF) (S : S2Draft GF) :
    ⊢ memberPubOk (hG := heapAt G L lctx) S (putgetPub S) := by
  unfold memberPubOk putgetPub
  imodintro
  iintro %ν %γf #Hinv
  iexists γf
  iintro %L'
  rw [putGetInv_heap G L' L]
  iexact Hinv

end pub

end etcd_putget_dist
end EtcdGrove
end Perennial

end
