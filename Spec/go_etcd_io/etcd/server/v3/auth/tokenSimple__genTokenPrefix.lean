/-
`tokenSimple.genTokenPrefix` (`server/auth/simple_token.go`): names only, the trust boundary (it
draws 16 letters with `crypto/rand.Int` over `rand.Reader`; `crypto/rand` and `math/big` are not
translated). C1's A4 (2026-10-29, the user's choice of the narrow boundary). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Proof.go_etcd_io.etcd.server.v3.auth.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `t.genTokenPrefix()`: 16 letters of `letters` (`[a-zA-Z]`, so no space: `tokPrefixOk`; C1's
A4, 2026-10-31, user-approved) and no error. Faithful at the pinned toolchain (go1.27.3):
`rand.Int(rand.Reader, max)` fails only when its reader does, and since Go 1.24 the default
`crypto/rand.Reader`'s `Read` never returns an error (an OS failure, or with boringcrypto a failed
read, crashes the program instead); `letters[bInt.Int64()]` is in range (`rand.Int` is in
`[0, max)`, `max = len(letters)`); the receiver is not read. The margin: true while no code
reassigns `crypto/rand.Reader` (none in etcd's non-test code). -/
abbrev auth.tokenSimple.genTokenPrefix.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }}
    (App (Val (p @!! go.GoType.PointerType tokenSimple.ty @!! go!"genTokenPrefix")) (Val #()))
  {{ (s : GoString) (err : GoInterface), RET (PairV #s #err);
      ⌜err = GoInterface.nil ∧ auth.tokPrefixOk s⌝ }}

end spec

end EtcdGrove
end Perennial
