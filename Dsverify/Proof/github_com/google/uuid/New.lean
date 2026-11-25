/-
**Trust-boundary axiom, environment claim** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; google/uuid
v1.3.1, translated names only in the part): `uuid.New()` returns some `UUID`
(`github_com.google.uuid.New.spec`, `Dsverify/Proof/github_com/imdea_software/swiftpaxos/lib/
LibSpecs.lean`). Go: `New` is `Must(NewRandom())`; with the pool disabled (the default; nothing in
the kit calls `EnableRandPool`) and the package's reader `rander` left as `crypto/rand.Reader`
(nothing calls `SetRand`), `NewRandom` is `io.ReadFull(rand.Reader, uuid[:])`, which `Must` turns
into a panic if it fails. go1.27.3's `crypto/rand.Reader.Read` never returns an error (it fills the
buffer or ends the process with a runtime fatal error, `crypto/rand/rand.go:41-67`).
**Environment claim**: the OS's randomness does not fail (else the process dies, which no
`Robust` execution covers). Until dsv-fix4 swiftpaxos's statement premise `SwiftOsRandom`
(`Dsverify/Proof/github_com/imdea_software/swiftpaxos/Hyps.lean`), its field verbatim. Review:
`notes/axiom-review/dsv-fix4/google-uuid.md`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibSpecs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section ax
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **Trust-boundary axiom, environment claim** (the file header). -/
axiom github_com.google.uuid.New.wp_proof : github_com.google.uuid.New.spec (GF := GF)

end ax

end Perennial
