/- Lean-first (no Rocq counterpart).

`openStorage(boot, b)` (storage.go): the storage of a replica whose file holds `b`: when `b` is the
bytes `encode` wrote of contents `f` that `openStorage` accepts (`KdFileOk`), `good` and a new,
registered storage, detached (`memStorFresh`: no node reads it yet) and holding `f`'s contents
(`kdContents (some f)`: its compaction point at the log's start, the entries after it, the end, the
snapshot, the hard state), whose image holds `f`, with its bootstrap conf state `boot`: what `Cluster.start`
hands `RestartNode` (`restartStorage`, through the storage's frame). (2026-11-01, stage II (j), S3:
the writers' lower bound of the stored snapshot at its index, which its detached `ApplySnapshot`/
`CreateSnapshot` give.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev openStorage.spec : Prop :=
  ∀ (bp : Loc) (boot : ConfStateM) (b : GoSlice) (dq : DFrac) (f : StorFile),
  KdFileOk f →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ kdStorInv ∗ ownCSM bp DFrac.discard boot ∗
      b ↦*{dq} encStor f }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.openStorage)) (Val #bp)) (Val #b))
  {{ (s : Loc) (good : Bool), RET (PairV #s #good); ⌜good = true⌝ ∗
      ∃ (ms ip : Loc) (γs : MemStorNames) (e0 : EntryM),
        kdStorRec s ms γs ∗ kdStorBoot s bp boot ∗ memStorLock ms γs ∗
        memStorFresh ms γs (uint.nat f.prev) (if f.snap.Metadata'.Index' = W64 0 then memSnapEmpty else f.snap) ∗
        memStorMeta ms γs f.hs ∗ s.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip f ∗
        ⌜e0.Term' = f.prevTerm⌝ ∗ memLog γs (uint.nat f.prev) DFrac.discard [e0] ∗
        memLog γs (uint.nat f.prev + 1) (DFrac.own 1) f.ents ∗
        memEnd γs (uint.nat f.prev + f.ents.length + 1) ∗
        memCompacted γs (uint.nat f.prev) ∗ memSnapLb γs (uint.nat f.snap.Metadata'.Index') ∗
        b ↦*{dq} encStor f }}

end spec

end kvdurable
end EtcdGrove
end Perennial
