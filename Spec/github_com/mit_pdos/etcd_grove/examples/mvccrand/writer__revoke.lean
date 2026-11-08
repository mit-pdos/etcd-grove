/- Lean-first (no Rocq counterpart).

`w.revoke(i)` (`examples/mvccrand/mvccrand.go`): with no live lease drawn (`genLease`'s `0`),
nothing; else the lease `id`'s keys deleted in one revision by the lessor's `Revoke` (the model's
keys on it, in key order, as `end`'s pending revision), every result checked (`Revoke` succeeded; the
hook ran with the index `i`; `Lookup(id)` is `nil` after). The writer, between operations
(`writerOwn`, `writerLe`), ends between operations at the live leases `L` less `id` (`L` itself when
none was drawn: no live lease is `0`); the hook saved `i` if a lease was revoked (`hookPost`), else
nothing ran (`hookPre`, unchanged).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriterLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev writer.revoke.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (B : KBReal) (f : GoFunc) (q : Qp) (σ : MvccState)
    (Hs : List HRev) (L : List w64) (n : w64) (k : Nat) (T R : IProp GF) (i s : w64),
  {{ writerCtx w wv γ (etcdStorage B) f ∗ writerOwn wv γ (etcdStorage B) q σ Hs L ∗ writerLe w wv γ B f L n k T R ∗
      hookPre wv i s }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"revoke")) (Val #i))
  {{ RET #(); ∃ (σ' : MvccState) (Hs' : List HRev) (id : w64),
      writerOwn wv γ (etcdStorage B) q σ' Hs' (L.filter (· != id)) ∗
      writerLe w wv γ B f (L.filter (· != id)) n k T R ∗ (hookPost wv i ∨ hookPre wv i s) }}

end spec

end mvccrand
end EtcdGrove
end Perennial
