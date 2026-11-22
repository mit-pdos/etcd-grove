/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/datadir/ToSnapDir.lean` (bkarea, 2026-11-22), over
`filepath.Join`'s spec and `ToMemberDir`'s.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.datadir.ToSnapDir
public import Spec.path.filepath.Join
public import Proof.path.CleanIdem
public import Spec.go_etcd_io.etcd.server.v3.storage.datadir.ToMemberDir
@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.datadir.Assumptions]

theorem datadir.ToSnapDir.wp_proof (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_ToMemberDir : datadir.ToMemberDir.spec (GF := GF) (hG := hG)) :
    datadir.ToSnapDir.spec (GF := GF) (hG := hG) := by
  intro d hd
  wp_start
  wp_auto
  wp_apply wp_ToMemberDir d hd
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) [path.joinModel [d, go!"member"], go!"snap"]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  have hl := path.joinModel_pair_length d go!"member" (by decide)
  wp_apply wp_Join _ [path.joinModel [d, go!"member"], go!"snap"] _ (by simp at hl ⊢; omega)
    $$ [$Hsl] as %r ⟨%hr, -⟩
  rw [path.joinModel_triple d _ _ (by decide) (by decide)] at hr
  subst hr
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
