/-
## `http.NewRequest(method, url, body)` (net/http's trust boundary: assumed)

Why true: `NewRequest` parses the URL (`url.Parse`; a URL from `url.Parse` with an `http`/`https`
scheme and a host prints and parses back: `urlOk`), checks the method (a token), and builds a request
with an empty header map, the URL's host and path, and the body (a `*bytes.Buffer` gets its length
and `GetBody`); it fails only on a bad method or URL, which the premises rule out.
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

/-- **A request** of method `GET` or `POST` to `u`'s string, with body `bd` (or none). -/
def NewRequest.spec : Prop :=
  ∀ (meth : GoString) (u : _root_.Perennial.net.url.URL) (bd : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ ⌜urlOk u ∧ (meth = go!"GET" ∨ meth = go!"POST")⌝ }}
    (App (App (App (Val (@! _root_.Perennial.net.http.NewRequest)) (Val #meth)) (Val #(urlStr u))) (Val #bd))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); ⌜err = interface.nil⌝ ∗ reqOwn r ⟨meth, u.Host', u.Path', []⟩ bd }}

end spec
end Http
end EtcdGrove
end Perennial
