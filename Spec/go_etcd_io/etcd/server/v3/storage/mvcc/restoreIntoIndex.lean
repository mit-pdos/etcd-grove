/-
`restoreIntoIndex(lg, idx)` (`kvstore.go:434`). Internal: `restore`. Starts the goroutine that
rebuilds the index from the restored entries it receives on `rkvc`, and reports the last revision
on `revc`.

**Proof sketch**: two `make(chan …)`; `go` the loop, holding `ownIdxPriv ti`, its cache of key
indexes (pointers into the private index: `ownIdxPriv_lookup`); per entry (`rkvIs`): `KeyIndex`
(a hit) or a fresh key index; `BytesToRev` (`RestoreEntsOk`: parses; `verify.Verify`'s revision
check holds: increasing); `tombstone` (its `ErrRevisionNotFound` logged) or `put` (revisions
increasing: no `Panic`), or `restoreTombstone`/`restore` and `Insert`; after the close, `revc <-
currentRev` (the deferred send), `revConsumer`'s result (`idxRestore ents`, `lastMain ents`).

**Changes** from `specs-ref`'s file: the two channels' protocols opaque (`rkvProducer`,
`revConsumer`, with the laws `rkvSend`, `revRecv`) in place of `isSpsc` over `rkvProt`/`revProt`;
the readers' capability (`rdCap`) gone; the entries' key bytes are the storage's, lent to the
goroutine until it reports (`rkvIs` at a fraction, `rkvProducer`'s loans, back by `revRecv`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `restoreIntoIndex(lg, idx)` over an empty private index, for the entries `ents` its caller will
send: the producer's side of `rkvc` and the consumer's of `revc`. -/
def restoreIntoIndex.spec : Prop :=
  ∀ (lg ti : Loc) (ents : List KvEnt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ Zap.isLogger lg ∗
      ownIdxPriv ti (fun _ => none) ∗ ⌜RestoreEntsOk ents⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.restoreIntoIndex)) (Val #lg))
      (Val #(interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti)))
  {{ (rkvc revc : Loc), RET (PairV #rkvc #revc);
      rkvProducer rkvc ents 0 iprop(True) ∗ revConsumer revc rkvc ti ents }}

end spec
end Mvcc
end EtcdGrove
end Perennial
