/-
**A `*bufio.Writer` holding nothing** (net/http's server, 2026-11-23: the writers of its pools,
`newBufioWriterSize`/`putBufioWriter`, and of a connection before its first response, which
`Hijack` resets): `bufio.rawWriter bw sz` is the writer's struct with a buffer of `sz > 0` bytes
and nothing buffered (`n` zero), its destination and error any. Lean-first.
-/
module

public import Proof.bufio.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
def bufio.rawWriter (bw : Loc) (sz : Nat) : IProp GF :=
  iprop(∃ (v : _root_.Perennial.bufio.Writer) (bs : List w8), bw ↦ v ∗ v.buf' ↦* bs ∗
    ⌜bs.length = sz ∧ 0 < sz ∧ v.n' = W64 0⌝)

end defs

end EtcdGrove
end Perennial
