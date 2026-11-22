/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/datadir/ToMemberDir.lean` (bkarea, 2026-11-22), over
`filepath.Join`'s spec.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.datadir.ToMemberDir
public import Spec.path.filepath.Join
public import Proof.path.CleanIdem

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

theorem datadir.ToMemberDir.wp_proof (wp_Join : filepath.Join.spec (GF := GF) (hG := hG)) :
    datadir.ToMemberDir.spec (GF := GF) (hG := hG) := by
  intro d hd
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := GoString) [d, go!"member"]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_apply wp_Join _ [d, go!"member"] _ (by simp; omega) $$ [$Hsl] as %r ⟨%hr, -⟩
  subst hr
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
