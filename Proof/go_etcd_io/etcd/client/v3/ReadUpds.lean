/-
The members' read updates, persistent (`readUpds_box`): moved out of `ClientPutGet.lean`
(2026-11-18), whose calls are over the client's linked results, so that a definition naming it
imports no linked result (CLAUDE.md, "Import tiers").
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PutThenGet
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.ReplyValues

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section family
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The members' read updates, persistent** (each is: a read update, or none). -/
theorem readUpds_box (ms : List (SrvAt GF)) (Q : KVState → IProp GF) :
    ([∧list] x ∈ ms, iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu (GF := GF) x.γr.kv Q)) ⊢
      □ ([∧list] x ∈ ms, iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q)) := by
  haveI : Persistent ([∧list] x ∈ ms,
      iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu (GF := GF) x.γr.kv Q)) :=
    BigAndL.bigAndL_persistent fun {_ _} _ => inferInstance
  exact intuitionistic_alias

end family

end client
end EtcdGrove
end Perennial
