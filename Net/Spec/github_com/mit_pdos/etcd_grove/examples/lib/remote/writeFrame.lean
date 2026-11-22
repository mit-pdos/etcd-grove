/-
`writeFrame(c, body)`: writes `body`'s frame (`frame`, `Wire.lean`) on the end `s` of `cn`
(`writeAll`), for a writer that has written `W0` and may write the frame after it. It returns `true`
only with the whole frame written; whatever it returns, the writer has written a prefix of it.
A body is at most `maxLen` bytes (both callers check it: `8 + len(body)` then fits an `int`).
Proved in `Net/Proof/.../lib/remote/writeFrame.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Wire
public import Perennial.Proof.io.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev writeFrame.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (P : Proto GF) (W0 : List w8)
    (body : GoSlice) (bd : List w8) (dq : DFrac) (ed : GoInterface),
  bd.length ≤ maxLen →
  {{ net.isConn (GF := GF) c cn s a ∗ body ↦*{dq} bd ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      sendTok (Gg := hG.goose_globalGS) cn s P W0 ∗ □ P cn (W0 ++ frame bd) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.writeFrame)) (Val #c)) (Val #body))
  {{ (ok : Bool), RET #ok; ∃ w, body ↦*{dq} bd ∗ sendTok (Gg := hG.goose_globalGS) cn s P (W0 ++ w) ∗
      ⌜w <+: frame bd ∧ (ok = true → w = frame bd)⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
