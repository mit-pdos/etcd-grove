/-
`ioutil.NewLimitedBufferReader(r, n)` (rafthttp stage 4, D38b): the pipeline handler reads a
request's body through it. Its `Read` caps each read at `n` bytes (`n` is not decremented: a cap
per read, not a limit on the total), so the reader it returns keeps `r`'s prefix contract
(`http.prefixReaderOk`). Lean-first.
-/
module

public import Proof.net.http.Boundary
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`NewLimitedBufferReader(rd, n)`** of a reader of `B`, at a positive cap: a reader of `B`
in the same states. -/
abbrev ioutil.NewLimitedBufferReader.spec : Prop :=
  ∀ (rd : GoInterface) (Src : List w8 → IProp GF) (B : List w8) (e : GoInterface) (n : w64),
  0 < sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil ∗
      http.prefixReaderOk rd Src B e }}
    (App (App (Val (@! ioutil.NewLimitedBufferReader)) (Val #rd)) (Val #n))
  {{ (rd' : GoInterface), RET #rd'; http.prefixReaderOk rd' Src B e }}

end spec

end EtcdGrove
end Perennial
