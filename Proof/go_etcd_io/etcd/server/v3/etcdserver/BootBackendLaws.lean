/-
**`bootstrapBackend`'s two laws** (claim #34 step 4, 2026-11-25: moved here from
`bootstrapBackend.lean`, a proof module no spec may import, so that the server's link can name them as
specs, `Spec/.../etcdserver/bootstrapBackend{ExistFree,MetaSnap}.lean`). Definitions only. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **TEMPORARY (a gap): `fileutil.Exist` of a free name answers `false`** (`bootstrap.go:260`).
True of Go: `os.Stat` of a name naming nothing fails (`ENOENT`), so `Exist` returns `false`. Not
taken from `Exist.spec` here: that spec is stated at the file extension's instances (section
variables), the free name's claim at the program's (`backend.onFs`); the proof is `Exist.spec` with
`os.Stat.wp_absentS` at `theFs`'s instances (`fileFreeF`'s claim is `wp_absentS`'s premise). -/
abbrev bootstrapBackend.existFree.law : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      backend.fileFree p }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Exist)) (Val #p))
  {{ RET #false; backend.fileFree p }}

/-- **TEMPORARY (a gap): the meta reads of a backend opened at the apply protocol's names**
(`bootOk`'s `#HmetaSnap`, the trusted J8a-4 premise `notes/decisions.md` approved: "a sound trusted
premise at the open"), at any names `γ` whose protocol invariant is allocated. `bootstrapBackend.spec`
states it in its post (`bootBackendRows`), so its proof must make it; no callee's spec gives it
(the real backend's `ReadTx` is not proved to meet `metaReadTx` at `readView`). The same text is
`srvMetaSnap cl γ` (`InvRunRes.lean`). (keepfix (c), S2: at the cluster `cl`, the lock resource `metaTMR cl π`, and
the raft-term key the one opened with.) -/
abbrev bootstrapBackend.metaSnap.law : Prop :=
  ∀ (cl : Cluster) (γA : ApplyNames), inv applyN (consInv (GF := GF) γA) ⊢
    □ (∀ (π : ApplyPhys) (γB : backend.BNames) (P : backend.BParams) (D : backend.Data),
        ⌜ciKeys P ∧ metaIs D π.m0 ∧ metaRaftTermOf D = π.rk0 ∧ π.bwb = γB.wb ∧ π.bopn = γB.opn⌝ -∗
        backend.hkOwn γB (backend.hkData P D) -∗ backend.bFresh γB -∗
        backend.hkOwn γB (backend.hkData P D) ∗ backend.bFresh γB ∗
        □ ∀ (W : IProp GF) (b : Loc),
          backend.isBackend γB P W (batchLockInv (γA.withPh π) (metaTMR cl π γB P)) b -∗
          isMetaBackend (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) (⊤ \ ↑applyN)
            (readView (γA.withPh π)))

end laws

end EtcdGrove
end Perennial
