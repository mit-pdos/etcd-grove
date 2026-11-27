/-
**linkvtxn's linked calls, as hypotheses** (the import tiers, 2026-11-18): the statements of
`CallsLinked.lean`'s `client_List_st` and `txn_Commit_st`, each as `<name>.law : Prop`, which a
function's proof (`callList`, `callTxn`, the kubernetes client's) takes as a hypothesis instead of
importing `CallsLinked`; `<name>_law_holds` (`CallsLinked.lean`) proves it, and the `Link`s pass it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Calls

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver mvcc
open client (srvStart srvStart_both kvRegs_range kvRegs_txn)

section laws1
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `client_List_st`'s statement (`CallsLinked.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `client_List_st_law_holds` proves it. -/
abbrev client_List_st.law : Prop :=
  ∀ (cl : Loc) (ms : List (client.SrvAt GF))
      (V : client.WEnv GF) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl : GoSlice)
      (Q : KVState → IProp GF) (hsz : opSizeOk (opGetModel listFrom [withRangeM listTo])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (isNewClient cl (ms.map client.SrvAt.addr) V ∗
          ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ([∗list] x ∈ ms, srvStart x) ∗
          ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [withRangeM listTo] ∗
          □ ([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q)) }}
        (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
            go!"Get")) (Val #(GoInterface.ok ci))) (Val #listFrom)) (Val #sl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
            □ Q σ ∗ ⌜m.kvs = σ.kvs.filter (fun v => inRange listFrom listTo v.key) ∧
              m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev⌝) ∨
            ⌜err ≠ GoInterface.nil⌝) }}

/-- `txn_Commit_st`'s statement (`CallsLinked.lean`, a linking module), as a hypothesis of the
proofs that use it (the import tiers); `txn_Commit_st_law_holds` proves it. -/
abbrev txn_Commit_st.law : Prop :=
  ∀ (tp : Loc) (ms : List (client.SrvAt GF))
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
      (Q : KVState → IProp GF) (cs : List (linkv.MCmp GoString GoString))
      (t e : List (linkv.MOp GoString GoString)) (hb : b.model = clientTxn cs t e)
      (hne : t ++ e ≠ []) (hsz : txnSizeOk (txnWireOf b.model)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (txnObjAt tp (ms.map client.SrvAt.addr) ci cd b ∗
          ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ([∗list] x ∈ ms, srvStart x) ∗
          client.txnWriteOnce tp (ms.map client.SrvAt.addr) ∗
          ([∧list] x ∈ ms, callUpd x.γr.kv (.txn cs t e) Q)) }}
        (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
          (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗
            callRes (.txn cs t e) Q σ ∗
            ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
                (linkv.txnOf cs t e)).1 ∧
              client.opRespsRel false ((linkv.txnOf cs t e).branch m.succeeded)
                (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (linkv.txnOf cs t e)).2.2
                m.resps ∧
              m.hdr.revision = W64 ((if (linkv.MIn.txn cs t e).isWrite then
                (kvOpStep (opIn (.txn cs t e)) σ).rev else σ.rev : Nat) : Int) ∧
              kvRevFits σ.rev ∧
              -- (2026-10-31, `notes/vallen.md`) the state's values are short (the reply's log's)
              ∀ v ∈ σ.kvs, v.value.length ≤ etcdKeyMax⌝) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ kvErr err)) }}

end laws1

end etcd_txnlin
end EtcdGrove
end Perennial
