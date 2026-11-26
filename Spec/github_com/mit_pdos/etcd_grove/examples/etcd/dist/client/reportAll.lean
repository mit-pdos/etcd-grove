/- Lean-first (no Rocq counterpart).

`reportAll(nodes, ins, codec, d)` (`examples/etcd/dist/client/nodes.go`): **`remote.Report` at every
client machine `nodes[c]` with the input `ins[c]`, all at once** (#50 N10a; `CallAll` of
`remote.Report(a, in, codec, d)`).

**The triple:** at a service `S` whose codec `cd` is (`wireOk`), with the slot map (`mapCtx`), the
addresses `ns` and the Go inputs `xs` (as many, read-only), and per index `c`: node `ns[c]`'s
protocols (`svcAddr`) and one call's unit (`budUnit`), the input `xs[c]` describing the model input
`inp c` (`S.ivAt`) and the slot's update `S.upd (inp c) (Φ c)` (for a report, `P (inp c)` and the
continuation `Φ c`); `reportAll` returns `outs` and `oks` of `len(nodes)` elements, and at each index
`Report`'s answer: `oks[c]` false, or true with `outs[c]` describing an output `o` with `Φ c o` (or an
answer that is no output, `S.unkAns`, none for a report). The level token is threaded; the thread
bound is `CallAll`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev reportAll.spec : Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS] {I O : Type} [Pos.Countable I] [Pos.Countable O]
    (S : RSvc GF I O) (nodes insl : GoSlice) (ns : List GoString) (xs : List GoInterface)
    (inp : Nat → I) (Φ : Nat → O → IProp GF) (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec) (d : w64),
  threadBound GF ≤ 2 ^ 30 → xs.length = ns.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ nodes ↦*□ ns ∗ insl ↦*□ xs ∗ mapCtx (Gg := hG.goose_globalGS) (I := I) ∗
      wireOk S cd ∗
      [∗list] c ∈ List.range ns.length, ∃ (a : GoString) (x : GoInterface),
        ⌜ns[c]? = some a ∧ xs[c]? = some x⌝ ∗ svcAddr (Gg := hG.goose_globalGS) S a ∗
        budUnit (Gg := hG.goose_globalGS) a ∗ S.ivAt x (inp c) ∗ S.upd (inp c) (Φ c) }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reportAll))
      (Val #nodes)) (Val #insl)) (Val #cd)) (Val #d))
  {{ (outs oks : GoSlice), RET (PairV #outs #oks); levelTok 0 ∗
      ⌜sint.Z outs.len = ns.length ∧ sint.Z oks.len = ns.length⌝ ∗
      [∗list] c ∈ List.range ns.length, ∃ (v : GoInterface) (ok : Bool),
        typedPointsto (sliceIndexRef GoInterface ((c : Nat) : Int) outs) v (DFrac.own 1) ∗
        typedPointsto (sliceIndexRef Bool ((c : Nat) : Int) oks) ok (DFrac.own 1) ∗
        (⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ((∃ o, S.ovAt v o ∗ Φ c o) ∨ ⌜S.unkAns (inp c) v⌝))) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
