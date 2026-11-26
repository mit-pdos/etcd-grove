/-
`readFrame(c)`: reads one frame on the end `s` of `cn` (`readFull` of its header, then of its
body), for a reader that has read `R`. It returns `true` with the body `bd` of a frame it read
whole (at most `maxLen` bytes); whatever it returns, the reader has read `got` after `R`.
Proved in `Net/Proof/.../lib/remote/readFrame.lean`.
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
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev readFrame.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (P : Proto GF) (R : List w8)
    (eof ed : GoInterface),
  {{ net.isConn (GF := GF) c cn s a ∗ globalAddr io.EOF ↦□ eof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ recvTokL (Gg := hG.goose_globalGS) cn s P R }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.readFrame)) (Val #c))
  {{ (b : GoSlice) (ok : Bool), RET (PairV #b #ok); ∃ got, recvTokL (Gg := hG.goose_globalGS) cn s P (R ++ got) ∗
      (⌜ok = false⌝ ∨ ∃ bd, ⌜ok = true ∧ got = frame bd ∧ bd.length ≤ maxLen⌝ ∗ b ↦* bd) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
