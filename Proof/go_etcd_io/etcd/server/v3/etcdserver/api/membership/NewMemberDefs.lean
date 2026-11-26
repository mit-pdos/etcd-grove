/- Lean-first (no Rocq counterpart).

# `membership.NewMember`'s spec vocabulary: a peer URL of only a scheme and a host

`urlHttp p` is the `url.URL` value of the Go literal `url.URL{Scheme: "http", Host: p}` (every other
field zero): the one peer URL `deployment.memberIDs` builds for a member, `types.URLs{{Scheme: "http",
Host: m.Peer}}`.
-/
module

public import GeneratedProof.net.url

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace membership

/-- `url.URL{Scheme: "http", Host: p}`. -/
def urlHttp [GooseExts] (p : GoString) : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := p }

end membership
end EtcdGrove
end Perennial

end
