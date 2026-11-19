/-
**`NewStorage`'s contract proved** (wal-link L3, 2026-11-19; `notes/wal-link-l3-statements.md` §2, §4): the
storage `serverstorage.NewStorage(lg, h.w, ss)` returns meets the WAL contract (`isWalStorage st h ss`), each
law from the storage method's spec over the real WAL (`Spec/.../storage/storage__*.lean`, at the server's
message model `walSrvP`/`walSrvMr` and the open WAL `h`'s file-system instances), the records' atomic
updates turned into layer 1's (`walRecs` is the fold of layer 1's history, `storage/WalRecs.lean`). Until
L3 `rnNewStorageOk` was a premise of every closed theorem. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi
public import Spec.go_etcd_io.etcd.server.v3.storage.NewStorage
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Save
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__SaveSnap
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Sync
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Release

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The storage methods' specs at the open WAL `h`'s instances** (the server's message model): what
`rnNewStorageOk_holds` takes of the storage package (each a linked `wp_proof` of `storage/`). -/
def walStorSpecs (h : WalH GF) : Prop :=
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj; haveI := h.sat
  storage.storage.Save.spec (GF := GF) (Sio := h.Sio) walSrvP walSrvMr ∧
    storage.storage.SaveSnap.spec (GF := GF) (Sio := h.Sio) walSrvP walSrvMr ∧
    storage.storage.Sync.spec (GF := GF) (Sio := h.Sio) walSrvP walSrvMr ∧
    storage.storage.Close.spec (GF := GF) (Sio := h.Sio) walSrvP walSrvMr ∧
    storage.storage.Release.spec (GF := GF) (Sio := h.Sio) walSrvP walSrvMr

/-- **`Sync`'s law** from the storage's `Sync` (no error under `h.cov`; the length bound at `0` from the
share). -/
theorem walSync_law (h : WalH GF) (hS : walStorSpecs h) (p ss : Loc) (q : Qp) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ storage.storageOver p h.w ss ⊢
      {{ storage.walOpen h q ∗
          walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h }}
        (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) go!"Sync" #p))
          (Val #()))
      {{ (err : GoInterface), RET #err; storage.walOpen h q ∗
          walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h }} := by
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj; haveI := h.sat
  obtain ⟨-, -, hSync, -, -⟩ := hS
  iintro ⟨#Hpkg, #Hover⟩
  iintro !> %Φ ⟨Ho, Hrd⟩ HΦ
  iunfold storage.walOpen at Ho
  icases Ho with ⟨Hws, #Harea, #Hlen⟩
  iunfold walStorRd at Hrd
  icases Hrd with ⟨%p', %Hp', Hrd⟩
  have hp : p' = p := by
    have := ((interface_mkOk_inj _ _ _ _).1 Hp').2
    exact (go.intoVal_inj this).symm
  subst hp
  wp_apply (hSync p' ss h.R h.jr h.r h.w h.dir h.γ q 0) $$ [Hrd Hws] as %err ⟨Hrd, Hpost⟩
  · iframe Hover Hrd Harea Hws Hlen
    ipureintro; exact Or.inl h.cov
  icases Hpost with (⟨-, Hws, -⟩ | %Hbad)
  · iapply HΦ
    iunfold storage.walOpen
    iframe Hws Harea Hlen
    iunfold walStorRd
    iexists p'
    iframe Hrd
    ipureintro; rfl
  · exact absurd h.cov Hbad.2

end proof

end EtcdGrove
end Perennial
