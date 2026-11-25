/- Lean-first (no Rocq counterpart).
`encCmp(e, x)` (`examples/etcd/dist/kvremote`): appends a comparison's encoding, every field in order in `enc`'s
encodings (`cmpBytes`), to the encoder's bytes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]

/-- See the file header. -/
abbrev encCmp.spec : Prop :=
  ∀ (e : Loc) (bs : List w8) (x : Cmp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote ∗ ownEnc e bs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encCmp)) (Val #e)) (Val #x))
  {{ RET #(); ownEnc e (bs ++ cmpBytes x) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
