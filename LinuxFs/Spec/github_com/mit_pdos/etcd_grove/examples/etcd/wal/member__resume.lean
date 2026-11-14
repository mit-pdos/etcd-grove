/- Lean-first (no Rocq counterpart).

`(*member).resume(c)` (`examples/etcd/wal/wal.go`): the member's raft-like fields set from the read
`c` (`Resume.lean`): a fresh `terms` map. Its fields' old values are any.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Resume

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev member.resume.spec : Prop :=
  ∀ (m : Loc) (vc : contents) (c : TContents) (t vo cm b l : w64) (tm : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      contentsRep vc c ∗
      m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"commit"] ↦ cm ∗
      m.[member, go!"base"] ↦ b ∗ m.[member, go!"last"] ↦ l ∗ m.[member, go!"terms"] ↦ tm }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"resume")) (Val #vc))
  {{ RET #(); m.[member, go!"term"] ↦ tResumeTerm c ∗ m.[member, go!"vote"] ↦ c.hs.vote' ∗
      m.[member, go!"commit"] ↦ tResumeCommit c ∗ m.[member, go!"base"] ↦ c.baseIdx ∗
      m.[member, go!"last"] ↦ tResumeLast c ∗
      ∃ tm' : Loc, m.[member, go!"terms"] ↦ tm' ∗ tm' ↦$ tResumeTerms c }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
