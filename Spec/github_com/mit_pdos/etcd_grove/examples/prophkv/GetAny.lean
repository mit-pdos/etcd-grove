/- Lean-first (no Rocq counterpart).

`GetAny(kv, k)` (`examples/prophkv`), **logically atomic**: the caller's atomic update of the
abstract state fires once, with the answer `GetAny` returns, which is `k`'s value at that point.
`GetAny` reads `k` twice and returns one of the two answers, chosen at random after both reads;
its proof fires the update at the read whose answer is returned, which it knows at the first read
from a prophecy of the choice, added to the Go code by a prophecy patch
(`etc/proph-patches/prophkv/`). The spec does not mention the prophecy.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.prophkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prophkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.prophkv

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.prophkv.Assumptions]

/-- See the file header. -/
abbrev GetAny.spec : Prop :=
  ∀ (kv : Loc) (γ : GName) (k : GoString) (Q : GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.prophkv ∗
      isKV kv γ ∗
      AU <{ ∃∃ (m : GMap GoString GoString), kvState γ m }> @ ⊤, ∅
        <{ kvState γ m, COMM Q ((m !! k).getD go!"") }> }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.prophkv.GetAny)) (Val #kv))
      (Val #k))
  {{ (r : GoString), RET #r; Q r }}

end spec

end prophkv
end EtcdGrove
end Perennial
