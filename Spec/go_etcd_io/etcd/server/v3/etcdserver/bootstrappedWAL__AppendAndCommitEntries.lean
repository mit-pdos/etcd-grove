/-
`(*bootstrappedWAL).AppendAndCommitEntries(ents)` (`server/v3/etcdserver/bootstrap.go:793`,
extracted as a helper method in `etcd-io/etcd#22655`). Lean-first.

Appends `ents` to `wal.ents`, persists `ents` (with an empty `HardState{}`) via `wal.w.Save`,
and, if `len(wal.ents) != 0`, updates `wal.st.Commit` in memory to `wal.ents[len(wal.ents)-1].Index`
(`hsAfterAppend hs es entsM`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBootWAL

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

abbrev bootstrappedWAL.AppendAndCommitEntries.spec : Prop :=
  ∀ (w : Loc) (bw : bootstrappedWAL) (ents : GoSlice) (dq : DFrac)
    (hs : HardStateM) (es entsM : List EntryM),
  (es.length : Int) + (entsM.length : Int) < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Hwal" ∷ w ↦ bw ∗
      "Hst" ∷ hsPts bw.st' (DFrac.own 1) hs ∗
      "Hents" ∷ entsPts bw.ents' (DFrac.own 1) es ∗
      "Hcap" ∷ ownSliceCap Loc bw.ents' (DFrac.own 1) ∗
      "Harg" ∷ entsPts ents dq entsM ∗
      "#Hsave" ∷ bootWalSaveOk bw.w' }}
    (App (Val (w @!! go.GoType.PointerType bootstrappedWAL.ty @!! go!"AppendAndCommitEntries"))
      (Val #ents))
  {{ RET #();
      ∃ ents' : GoSlice,
        w ↦ { bw with ents' := ents' } ∗
        hsPts bw.st' (DFrac.own 1) (hsAfterAppend hs es entsM) ∗
        entsPts ents' (DFrac.own 1) (es ++ entsM) ∗
        ownSliceCap Loc ents' (DFrac.own 1) ∗
        entsPts ents dq entsM }}

end spec

end EtcdGrove
end Perennial
