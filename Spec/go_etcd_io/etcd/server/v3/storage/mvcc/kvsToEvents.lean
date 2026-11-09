/-
`kvsToEvents(lg, c, revs, vals)` (internal): unmarshals each value (`lg.Panic` on failure: the
premise excludes it), keeps those whose key `c` contains, as events (a tombstone a delete with its
revision patched in).

**Proof sketch.** `proto.Unmarshal` (2a's proto boundary: an encoding decodes to its message,
fresh), `c.contains` (`watcherGroup.contains.spec`), `isTombstone`, `BytesToRev` (3e's), `append`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def kvsToEvents.spec : Prop :=
  ∀ (lg : Loc) (wg : Loc) (v : watcherGroup) (dq dq' : DFrac) (G : List (Loc × MRange))
    (revs vals : GoSlice) (rs vs : List GoSlice) (rb vb : List GoString)
    (ents : List (Nat × Bool × KeyValueM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ Zap.isLogger lg ∗ wg ↦{dq} v ∗ wgOwn v dq' G ∗ revs ↦*□ rs ∗ vals ↦*□ vs ∗
      ([∗list] x; b ∈ rs; rb, x ↦*□ b) ∗ ([∗list] x; b ∈ vs; vb, x ↦*□ b) ∗
      ⌜List.Forall₂ (fun r e => revEnc r e.1 e.2.1) rb ents ∧
        List.Forall₂ (fun bs e => kvEnc bs e.2.2) vb ents⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.kvsToEvents)) (Val #lg))
      (Val #(interface.mkOk (go.GoType.PointerType watcherGroup.ty) #wg))) (Val #revs)) (Val #vals))
  {{ (evs : GoSlice), RET #evs; wg ↦{dq} v ∗ wgOwn v dq' G ∗
      ∃ (ps : List Loc), evs ↦* ps ∗
        [∗list] p; e ∈ ps; ((ents.filter (fun x => decide (∃ y ∈ G, y.2.watchMem x.2.2.key))).map
          (fun x => entryEv x.1 x.2.1 x.2.2)), evOwn p e }}

end spec

end Mvcc
end EtcdGrove
end Perennial
