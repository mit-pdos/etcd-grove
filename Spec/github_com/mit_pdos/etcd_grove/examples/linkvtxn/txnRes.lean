/- Lean-first (no Rocq counterpart).

`txnRes(ops, resps)` (linkvtxn.go): a new slice of a transaction's results, from its branch's
operations `ops` (decoding to `mops`) and the reply's responses (`opRespsMsg ps ms`, which answer
the operations as the server ran them, with results `rs`: `opRespsRel`): the model's results
(`linkv.resOf`), as `call` builds them (`encRes`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev txnRes.spec : Prop :=
  ∀ (osl : GoSlice) (ops : List TOp) (mops : List (linkv.MOp GoString GoString)) (rsl : GoSlice)
    (ps : List Loc) (rs : List TxnOpResult) (ms : List OpRespM),
  decAll decTOp ops = some mops → client.opRespsRel false (mops.map linkv.tOpOf) rs ms →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      osl ↦*□ ops ∗ rsl ↦*□ ps ∗ opRespsMsg ps ms }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.txnRes)) (Val #osl))
      (Val #rsl))
  {{ (out : GoSlice), RET #out; out ↦* ((rs.map linkv.resOf).map encRes) ∗
      ownSliceCap TRes out (DFrac.own 1) }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
