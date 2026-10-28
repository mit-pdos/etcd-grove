/-
`credentials.NewPerRPCCredentialBundle()` (`client/v3/credentials/credentials.go`; the auth plan's
E2d). Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/client/v3/credentials/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.credentials.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- `NewPerRPCCredentialBundle()`: a token bundle (`tokenBundleAt`) whose tokens are `""` or meet
any `P` the caller picks (`tokenBundleInv`; the auth plan's C1: its token starts `""`). -/
abbrev credentials.NewPerRPCCredentialBundle.spec : Prop :=
  ∀ (P : GoString → IProp GF),
  {{ ⌜threadBound GF ≤ 2 ^ 30⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.credentials.NewPerRPCCredentialBundle)) (Val #()))
  {{ (atb : GoInterface), RET #atb; tokenBundleInv (GF := GF) atb P }}

end spec

end EtcdGrove
end Perennial
