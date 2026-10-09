/-
Port of election_proof/spec_rand_Int.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvBig

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `crypto/rand.Int(rand.Reader, max)` returns a uniform value in `[0, max)`, and
no error, for the package's own `Reader`.

**Trust boundary**: `crypto/rand` is not translated, and it is not raft. Stating
the triple for the reader the package installed (`globalAddr crypto.rand.Reader ↦□
rdr`) is what folds `lockedRand.Intn`'s `if err != nil { panic }` away.

Perennial (`00b3c10ea`) models `crypto/rand.Int` and proves `crypto.rand.wp_Int`, with
this pre- and postcondition but only for `mz < 2^63` (its model reads one magnitude
word and panics beyond), so it does not prove this triple, which holds for every
`0 < mz`; this stays an `axiom` (`Proof/crypto/rand/Int.lean`). -/
abbrev rand.Int.spec : Prop :=
  ∀ (rdr : GoInterface) (max : Loc) (mz : Int),
  0 < mz →
  {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.rand ∗
     globalAddr crypto.rand.Reader ↦□ rdr ∗ ownBigInt max mz }}
    (App (App (Val #(functions crypto.rand.Int' [])) (Val #rdr)) (Val #max))
  {{ (v : Loc) (z : Int), RET (PairV #v #interface.nil);
     ownBigInt max mz ∗ ownBigInt v z ∗ ⌜0 ≤ z ∧ z < mz⌝ }}

end spec

end EtcdGrove
end Perennial
