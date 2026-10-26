/-
**Raft's linked results, without raft's proofs** (2026-10-26, raft's signature, stage 1;
`notes/decisions.md`, "Package signatures"): the results of `Link.lean` that proofs outside raft's
linking files use as lemmas, re-exported under `RaftLink` (`open RaftLink` gives them their
names). This module imports `Link.lean` non-publicly: a client sees each result's statement (its
public spec), not the proofs, so it does not reach raft's internals (`etc/api-check.py
etc/api/raft.txt`). A client's own `Link.lean`, `Results.lean` or `Adequacy.lean` may import
raft's `Link.lean` itself.
-/
module

public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries
public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.StartNode
import Proof.go_etcd_io.raft.v3.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftLink

open Iris Iris.BI go_etcd_io.raft.v3

section linksLC
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem wp_StartNode [StorageModel GF] :
    StartNode.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_StartNode

theorem wp_RestartNode [StorageModel GF] :
    RestartNode.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_RestartNode

end linksLC

section links
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem wp_NewMemoryStorage [StorageModel GF] :
    NewMemoryStorage.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_NewMemoryStorage

theorem wp_IsEmptyHardState  :
    IsEmptyHardState.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_IsEmptyHardState

theorem wp_IsEmptySnap  :
    IsEmptySnap.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_IsEmptySnap

theorem MemoryStorage.wp_Append [StorageModel GF] :
    MemoryStorage.Append.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_Append

theorem MemoryStorage.wp_Entries [AllG GF] [StorageModel GF] :
    MemoryStorage.Entries.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_Entries

theorem MemoryStorage.wp_FirstIndex [AllG GF] [StorageModel GF] :
    MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_FirstIndex

theorem MemoryStorage.wp_LastIndex [AllG GF] [StorageModel GF] :
    MemoryStorage.LastIndex.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_LastIndex

theorem MemoryStorage.wp_Term [AllG GF] [StorageModel GF] :
    MemoryStorage.Term.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_Term

end links

end RaftLink
end EtcdGrove
end Perennial
