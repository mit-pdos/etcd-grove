/-
Proof of `Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__MemberDir.lean` (claim #34, stage 3,
2026-11-23): `MemberDir()` is `datadir.ToMemberDir(c.DataDir)`, whose spec returns
`filepath.Join(d, "member")`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__MemberDir
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
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

theorem config.ServerConfig.MemberDir.wp_proof
    (wp_ToMemberDir : datadir.ToMemberDir.spec (GF := GF) (hG := hG)) :
    config.ServerConfig.MemberDir.spec (GF := GF) (hG := hG) := by
  intro c dq d hd
  wp_start as Hf
  wp_auto
  wp_apply wp_ToMemberDir d hd
  (try wp_auto)
  iapply HΦ
  iexact Hf

end proof

end EtcdGrove
end Perennial
