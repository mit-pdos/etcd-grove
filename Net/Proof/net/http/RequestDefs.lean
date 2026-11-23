/-
The vocabulary of the specs of net/http's request reading (`readRequest` and what it calls, the model
`models/net/http`), beside `Defs.lean`'s:

* `pathByte c`: `c` is a byte the model's `modelPathByte` accepts, one net/url leaves alone in a path
  (RFC 3986's unreserved bytes and `$&+,/:;=@`);
* `reqPath s`: `s` starts with `/` and has only such bytes: the request URIs on which the model's
  `modelParseRequestURI` computes `url.ParseRequestURI`'s result itself (the URL with path `s`);
* `parseReqLine l`: what `parseRequestLine(l)` returns, the method, the request URI and the protocol
  (the two `modelCutByte`s at `' '`) and `true`, or empties and `false`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

namespace net.http

/-- See the file header. -/
def pathByte (c : w8) : Bool :=
  decide ((97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
    (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨
    c ∈ [W8 45, W8 95, W8 46, W8 126, W8 36, W8 38, W8 43, W8 44, W8 47, W8 58, W8 59, W8 61, W8 64])

/-- See the file header. -/
def reqPath (s : List w8) : Prop := s.head? = some (W8 47) ∧ ∀ c ∈ s, pathByte c = true

/-- See the file header. -/
def parseReqLine (l : List w8) : List w8 × List w8 × List w8 × Bool :=
  let c1 := cutByte l (W8 32)
  let c2 := cutByte c1.2.1 (W8 32)
  if c1.2.2 && c2.2.2 then (c1.1, c2.1, c2.2.1, true) else ([], [], [], false)

end net.http
end Perennial
