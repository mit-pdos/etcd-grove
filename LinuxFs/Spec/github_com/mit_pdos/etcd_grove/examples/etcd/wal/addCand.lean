/- Lean-first (no Rocq counterpart).

`addCand(cs, img, unl, pur)` (`examples/etcd/wal/wal.go`): the candidate `(img, unl, pur)` added to the
owned candidate slice, its bounds merged (max) into the first candidate with an equal history
(`tAddCand`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Check

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
abbrev addCand.spec : Prop :=
  ∀ (s si : GoSlice) (cs : List TCand) (img : List TOp) (unl pur : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      candsOwn s cs ∗ opsRep si img }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.addCand)) (Val #s))
      (Val #si)) (Val #unl)) (Val #pur))
  {{ (s' : GoSlice), RET #s'; candsOwn s' (tAddCand img unl pur cs) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
