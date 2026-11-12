/-
`restoreIntoIndex` (`kvstore.go`; translated 2026-10-23, the restore plan's R0). Lean-first (no
Rocq counterpart); see `InvRestore.lean` and `IdxPriv.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRestore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `restoreIntoIndex(lg, idx)` (a non-nil logger, `idx` an empty tree index no one else can
reach, `ownIdxPriv`; the restore plan, R3) for the bucket entries `ents` (`RestoreEntsOk`: in
increasing revision order, as `restore` reads them), whose keys the goroutine reads through `Rd`
under its own token `Tok`: returns `rkvc` and `revc` and starts the goroutine that rebuilds the
index. The caller is `rkvc`'s producer (`rkvProt`: the `i`-th value is the `i`-th entry's
restored form; closed after all of them) and `revc`'s consumer: its one value
(`revProt`) is the last entry's main revision, with the rebuilt index (`idxRestore ents`), the
token and a time receipt per entry. -/
abbrev mvcc.restoreIntoIndex.spec : Prop :=
  ∀ (lg ti : Loc) (ents : List mvcc.KvEnt) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF)
    (e0 : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ ⌜lg ≠ null⌝ ∗
      mvcc.ownIdxPriv ti [] ∗ mvcc.rdCap Rd Tok ∗ Tok ∗ ⌜mvcc.RestoreEntsOk ents⌝ ∗
      globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e0 }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.restoreIntoIndex)) (Val #lg))
      (Val #(interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti)))
  {{ (rkvc revc : Loc), RET (PairV #rkvc #revc);
      ∃ (γ γr : SpscNames),
        isSpsc γ rkvc (mvcc.rkvProt Rd ents) (fun sent => iprop(⌜sent.length = ents.length⌝)) ∗
        spscProducer γ ([] : List revKeyValue) ∗
        isSpsc γr revc (mvcc.revProt ti Tok ents) (fun _ => iprop(False)) ∗
        spscConsumer γr ([] : List w64) }}

end spec

end EtcdGrove
end Perennial
