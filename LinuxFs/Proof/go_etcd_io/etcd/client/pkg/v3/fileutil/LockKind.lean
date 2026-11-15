/-
**`fileutil`'s locks are of one kind** (2026-11-15, the lock semantics, `notes/wal-units/locks.md`):
`fileutil.lockKind k1 ∗ fileutil.lockKind k2 ⊢ ⌜k1 = k2⌝`. Both read the package variables
`linuxLockFile`/`linuxTryLockFile` (persistent points-tos, so they agree), which hold `ofdLockFile` or
`flockLockFile` (`fileutil.lockFn`); the two function values differ because their bodies do
(`FuncUnfold`: a function's value is its body; one calls `FcntlFlock`, the other `Flock`). So the WAL's
locks (`openWALFiles`'s `TryLockFile`, `LockFile`) and the purger's (`TryLockFile`) are of one kind,
and `osLock_excl` relates them.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Fs

section law
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- The two lock functions are different values (their bodies differ). -/
theorem fileutil.lockFn_inj (o1 o2 : Bool) (h : fileutil.lockFn o1 = fileutil.lockFn o2) :
    o1 = o2 := by
  have hv : ∀ o, #(fileutil.lockFn o) =
      (if o then go_etcd_io.etcd.client.pkg.v3.fileutil.ofdLockFile.impl
        else go_etcd_io.etcd.client.pkg.v3.fileutil.flockLockFile.impl) := by
    intro o
    cases o
    · exact (FuncUnfold.func_unfold (f := go_etcd_io.etcd.client.pkg.v3.fileutil.flockLockFile)
        (type_args := []))
    · exact (FuncUnfold.func_unfold (f := go_etcd_io.etcd.client.pkg.v3.fileutil.ofdLockFile)
        (type_args := []))
  have h' : #(fileutil.lockFn o1) = #(fileutil.lockFn o2) := by rw [h]
  rw [hv, hv] at h'
  cases o1 <;> cases o2 <;> simp only at h' ⊢ <;>
    simp [go_etcd_io.etcd.client.pkg.v3.fileutil.ofdLockFile.impl,
      go_etcd_io.etcd.client.pkg.v3.fileutil.flockLockFile.impl] at h'

/-- **`fileutil`'s locks are of one kind** (see the file header). -/
theorem fileutil.lockKind_agree (k1 k2 : LockKind) :
    fileutil.lockKind (GF := GF) k1 ∗ fileutil.lockKind (GF := GF) k2 ⊢ ⌜k1 = k2⌝ := by
  unfold fileutil.lockKind
  iintro ⟨⟨%o1, %h1, H1, -⟩, ⟨%o2, %h2, H2, -⟩⟩
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ H1 H2
  ipureintro
  rw [h1, h2, fileutil.lockFn_inj o1 o2 Heq]

end law

end EtcdGrove
end Perennial
