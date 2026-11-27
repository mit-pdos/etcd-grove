/- Lean-first (no Rocq counterpart).
`decTRes(d)` (`examples/etcd/dist/kvremote`): reads a transaction operation's result: the decoder's bytes were its encoding (`tResBytes`)
followed by the rest, which it keeps, every read so far having succeeded; or its flag is false
(`decPost`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
open github_com.mit_pdos.etcd_grove.examples.lib.txnwork

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]

/-- See the file header. -/
abbrev decTRes.spec : Prop :=
  ∀ (d : Loc) (bs : List w8) (ok : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote ∗ ownDec d bs ok }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decTRes)) (Val #d))
  {{ (x : TRes), RET #x; decPost d bs ok tResBytes x }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
