/-
**The client's putget invariant, allocated at a log's state** (`putGetInv_alloc_log`; moved here from
`ClientPutGet.lean`, a linking module, 2026-11-23, so that proofs of programs that allocate it --
`putget_safe`'s member, `Proof/.../examples/etcd/dist/putget/Member.lean` -- import it without a linking
module: CLAUDE.md, "Import tiers"). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PutThenGet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The client's invariant at a log's state** (allocated with the put not fired; every log's
state is sorted by key, `mvcc.stateAfter_sorted`): from the client's `etcdKV` at `kvStateOf l`
(the bootstrap log's model, as the server's allocation gives it, `srvBootOut`). -/
theorem putGetInv_alloc_log (γr : ReadNames) (l : mvcc.Log) (key val : GoString) (Em : CoPset) :
    etcdKV (GF := GF) γr.kv (kvStateOf l) ⊢ |={Em}=> ∃ γf : GName, putGetInv γr γf key val := by
  iintro Hσ
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γf, Hm, -⟩
  imod inv_alloc kvClientN Em (iprop(∃ (σ : KVState) (n : Nat), etcdKV γr.kv σ ∗
      monoNatAuthOwn γf 1 n ∗ ⌜putGetOk key val σ n⌝)) $$ [Hσ Hm] with #Hinv
  · inext; iexists kvStateOf l, 0; iframe Hσ Hm
    ipureintro; exact ⟨KVState.kvs_sorted _, fun h => absurd h (by omega)⟩
  imodintro
  iexists γf
  iunfold putGetInv
  iexact Hinv

end alloc

end client
end EtcdGrove
end Perennial
