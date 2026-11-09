/-
## `http.Error(w, msg, code)` (net/http's trust boundary: assumed)

Why true: `Error` deletes `Content-Length`, sets `Content-Type` and `X-Content-Type-Options`,
calls `WriteHeader(code)` and writes `msg` with a newline (`fmt.Fprintln`); `code` in `200`-`999`
(Go panics outside `100`-`999` and does not commit a `1xx`).
-/
module

public import Spec.net.http.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Http

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Answers an error**: status `code` and the message, if the protocol allows them. -/
def Error.spec : Prop :=
  ∀ (w : GoInterface) (R : HReq) (τ : GName) (P : Proto GF) (hs : List (GoString × GoString)) (msg : GoString) (code : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ respW w R τ P none hs [] ∗ ⌜200 ≤ uint.nat code ∧ uint.nat code ≤ 999⌝ ∗ □ (∀ hs', P.resp R τ code hs' (msg ++ [W8 10])) }}
    (App (App (App (Val (@! _root_.Perennial.net.http.Error)) (Val #w)) (Val #msg)) (Val #code))
  {{ RET #(); ∃ hs' bs, respW w R τ P (some code) hs' bs }}

end spec
end Http
end EtcdGrove
end Perennial
