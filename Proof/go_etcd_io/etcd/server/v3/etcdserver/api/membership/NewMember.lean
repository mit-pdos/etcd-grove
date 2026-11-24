/-
The trust boundary: `membership.NewMember` (names only since 2026-11-24, etcd-dist D2: its
`computeMemberID` uses `crypto/sha1`, whose translation imports Perennial's `hash` and
`internal/byteorder`, which collide with this repository's local translations of them).

**Interim**, retired by translating `computeMemberID` once the local `hash`/`internal/byteorder`
translations are unified onto Perennial's (`crypto/sha1` imports Perennial's `hash`). Review:
`notes/axiom-review/membership-NewMember.md`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMember

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

/-- Interim trust-boundary axiom (see the file header). -/
axiom membership.NewMember.wp_proof : membership.NewMember.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
