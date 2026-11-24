/-
Proof of `Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__SnapDir.lean` (claim #34, stage 3,
2026-11-23): `SnapDir()` is `filepath.Join(c.MemberDir(), "snap")`; joining in two steps is joining
in one (`path.joinModel_triple`), `config.snapDirOf d` by definition.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__SnapDir
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__MemberDir
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
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

theorem config.ServerConfig.SnapDir.wp_proof (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_MemberDir : config.ServerConfig.MemberDir.spec (GF := GF) (hG := hG)) :
    config.ServerConfig.SnapDir.spec (GF := GF) (hG := hG) := by
  intro c dq d hd
  wp_start as Hf
  wp_auto
  wp_apply wp_MemberDir c dq d hd $$ [$Hf] as Hf
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) [path.joinModel [d, go!"member"], go!"snap"]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  have hl := path.joinModel_pair_length d go!"member" (by decide)
  wp_apply wp_Join _ [path.joinModel [d, go!"member"], go!"snap"] _ (by simp [_root_.Perennial.strings.joinMax] at hl ⊢; omega)
    $$ [$Hsl] as %r ⟨%hr, -⟩
  rw [path.joinModel_triple d _ _ (by decide) (by decide)] at hr
  subst hr
  unfold config.snapDirOf
  iapply HΦ
  iexact Hf

end proof

end EtcdGrove
end Perennial
