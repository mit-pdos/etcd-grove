/-
`wal.vseErrIs` (`errors.Is(err, os.ErrNotExist)` returns, `ValidSnapshotEntries`' retry test) of an error on
which `errors.Is` returns for every pointer target (`errIsTerm`): `os.ErrNotExist` holds an `*errorString`
(`os.errNotExist_ptr_of_pkgInit`, the part's `os` fact since 2026-11-14, `wal-vsnap4`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.validSnapshotEntries
public import Proof.errors.ErrIsTerm

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The retry test returns on an error with `errIsTerm`.** -/
theorem wal.vseErrIs_of_term (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.os ∗ errIsTerm (GF := GF) err ⊢ wal.vseErrIs err := by
  iintro ⟨#Hos, #Ht⟩
  ihave ⟨%x, #Hx⟩ := os.errNotExist_ptr_of_pkgInit $$ Hos
  unfold wal.vseErrIs
  iintro !> %nx #Hnx
  icombine Hnx Hx gives %he
  subst he
  unfold errIsTerm
  ihave #Hq := Ht $$ %_ %(errorString_ptr x)
  iintro !> %Φ - HΦ
  wp_apply Hq $$ [] as %b -
  iapply HΦ
  itrivial

end lemmas

end EtcdGrove
end Perennial

end
