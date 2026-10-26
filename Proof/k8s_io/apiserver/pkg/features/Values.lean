/-
Lean-first (no Rocq counterpart).

# `k8s.io/apiserver/pkg/features`'s constants (the trust boundary)

The package is translated names-only (`Code/k8s_io/apiserver/pkg/features.toml`), so its constants
are axiomatized values (`Code/k8s_io/apiserver/pkg/features.lean`). A program step that binds one
(`let x := features.F`) needs it not to be a panic value (`pure_beta`'s premise), which holds of a
real Go constant: `AllowUnsafeMalformedObjectDeletion` is the `featuregate.Feature` (a string)
`"AllowUnsafeMalformedObjectDeletion"`. `store.Delete` binds it as the argument of the feature
gate's `Enabled`.
-/
module

public import Code.k8s_io.apiserver.pkg.features

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace features

/-- **`AllowUnsafeMalformedObjectDeletion` is a value, not a panic** (the trust boundary; see the
file header). -/
axiom AllowUnsafeMalformedObjectDeletion_notPanic [GooseExts] [GoGlobalContext] :
    k8s_io.apiserver.pkg.features.AllowUnsafeMalformedObjectDeletion.isPanic = false

end features
end EtcdGrove
end Perennial
