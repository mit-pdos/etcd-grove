/-
`readFull(c, buf)` on the end `s` of the connection `cn`, whose reader (`recvTokL`,
`GooseLang/Ext/Net/Proto.lean`) has read `R` with protocol `P`: `c.Read`s into the rest of `buf`
until it is full or a read fails or meets EOF (`net.Conn.Read.spec` with the law `read_au`;
`wire.ReadFull`'s loop). It returns `true` only with `buf` full of the bytes read (`got = bs'`);
whatever it returns, the reader has read `got` after `R`, and `buf` starts with `got`.
Proved in `Net/Proof/.../lib/remote/readFull.lean`.
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
abbrev readFull.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (P : Proto GF) (R : List w8)
    (buf : GoSlice) (bs0 : List w8) (eof ed : GoInterface),
  {{ net.isConn (GF := GF) c cn s a ∗ buf ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ recvTokL (Gg := hG.goose_globalGS) cn s P R }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.readFull)) (Val #c)) (Val #buf))
  {{ (ok : Bool), RET #ok; ∃ (got bs' : List w8), recvTokL (Gg := hG.goose_globalGS) cn s P (R ++ got) ∗ buf ↦* bs' ∗
      ⌜bs'.length = bs0.length ∧ got <+: bs' ∧ (ok = true → got = bs')⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
