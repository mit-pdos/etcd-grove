/-
`cr.releaseConn()` (the model's `server.go`) after a hijack, in the main phase (`crLeft`: the main
thread's half of `γ.ph` at "main", the fields): under the mutex (whose invariant then holds only the
background reader's token), the reader's `conn` set to `nil`. Proved in
`Net/Proof/net/http/connReader__releaseConn.lean`.
-/
module

public import Net.Proof.net.http.ConnReader

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev connReader.releaseConn.spec : Prop :=
  ∀ (cr : Loc) (γ : CrNames) (cn : Nat) (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF),
  {{ crIs cr γ cn P hs Z ∗ crLeft cr γ hs }}
    (App (Val (cr @!! go.GoType.PointerType net.http.connReader.ty @!! go!"releaseConn")) (Val #()))
  {{ RET #(); crLeft cr γ hs }}

end spec

end net.http
end Perennial
