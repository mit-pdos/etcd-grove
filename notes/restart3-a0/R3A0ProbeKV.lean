/-
restart3 A0 probe P1 (unlinked scratch, never landed): R2s-A's backward install cannot be followed by
the server's KV store invariant. `kvStoreInv` (`KVStoreApi.lean:114-120`) holds the authority of the
monotone list `γs.slog` at the store's log, and every floor `kvLogLb γs L` (a fragment of it) is
persistent; the writer can mint a floor at its own log at any time (`kvAus.law`'s last clause). So
once a floor at `log` exists, every later state of the invariant has a log extending `log`: a
restore to a strict prefix (the F1 run: backend 100 -> 70) cannot re-establish the invariant.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace srvApi

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api

set_option linter.unusedSectionVars false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The invariant's authority at any later log extends every floor. -/
theorem probe_P1_floor (γs : KVSNames) (L L' : mvcc.Log) :
    ⊢ monoListAuthOwn (GF := GF) γs.slog 1 L' -∗ kvLogLb γs L -∗ ⌜L <+: L'⌝ := by
  iintro Ha Hl
  iunfold kvLogLb at Hl
  ihave %h := mono_list_auth_lb_valid γs.slog 1 L' L $$ Ha Hl
  ipureintro; exact h.2

/-- A backward restore (to a log `L'` that does not extend the floor `L`) is impossible. -/
theorem probe_P1_noBackward (γs : KVSNames) (L L' : mvcc.Log) (h : ¬ L <+: L') :
    ⊢ monoListAuthOwn (GF := GF) γs.slog 1 L' -∗ kvLogLb γs L -∗ False := by
  iintro Ha Hl
  ihave %h' := probe_P1_floor γs L L' $$ Ha Hl
  exact absurd h' h

/-- And the floor at the writer's log always exists: the writer's facts (`kvAus.law`'s last clause)
give `kvLogLb γs log` at its current state, before any restore. -/
theorem probe_P1_writerFloor (hA : kvAus.law (GF := GF) (hG := hG)) (kv : GoInterface) (γ : MvccName)
    (γr : ReadNames) (on : Bool) (γs : KVSNames) (log : mvcc.Log) (c : Int) :
    ⊢ kvStoreInv (GF := GF) kv γ γr on γs -∗ wSt γs log c ={⊤}=∗ wSt γs log c ∗ kvLogLb γs log := by
  iintro Hinv Hw
  ihave ⟨-, -, -, -, -, -, -, #Hf⟩ := hA kv γ γr on γs $$ Hinv
  imod Hf $$ %log %c Hw with ⟨Hw, #Hlb, -, -, -⟩
  imodintro
  iframe Hw Hlb

end srvApi
end EtcdGrove
end Perennial
