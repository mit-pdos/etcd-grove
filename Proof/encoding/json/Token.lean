/-
Lean-first (no Rocq counterpart).

`json.Marshal` of a continue token (stage 7e-2, `notes/k8s-7e-2-draft.md` §5.4): its output as an
opaque function of the token's two varying fields (`storage.EncodeContinue`'s
`&continueToken{APIVersion: "meta.k8s.io/v1", ResourceVersion: rv, StartKey: start}`). No property of
it is used (no injectivity: JSON replaces invalid UTF-8 by U+FFFD, `notes/k8s-7e-2-attack.md` T14).
-/
module

public import Perennial.Std.ByteString

@[expose] public section

namespace Perennial
namespace encoding.json

/-- `json.Marshal(&continueToken{APIVersion: "meta.k8s.io/v1", ResourceVersion: rv, StartKey:
start})`'s bytes. Opaque. -/
opaque tokJson : w64 → GoString → GoString

end encoding.json
end Perennial
