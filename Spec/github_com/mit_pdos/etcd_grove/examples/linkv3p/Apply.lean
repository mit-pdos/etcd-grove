/- Lean-first (no Rocq counterpart).

`Apply(clis, input)` (`examples/linkv3p/linkv3p.go`; the partition plan's S3a, 2026-10-20): one
operation through a client of `clis` picked at random (`primitive.RandomUint64 % len(clis)`),
`linkv.Apply(clis[i], input)`. Logically atomic against the instance's model as linkv's `Apply`
(`Spec/.../linkv/Apply.lean`, whose header explains the triple), in the form `lintest`'s
`applySpec` takes for the closure `Check` passes: the same triple, over the slice of clients
(read-only, non-empty) with linkv's `Apply.spec`'s premises for each client (`clientOk`,
`Defs.lean`: `New`'s one-attempt client, etcd's `Put` and `Range` at its member's endpoint, the
instance's invariant at that member's KV names). Stated under the cache package's assumptions and
`errors.As`'s target, as linkv's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev Apply.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (γ : linkv.LinkvNames) (cls : GoSlice)
    (clis : List Loc),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → clis ≠ [] →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p -∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv -∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 -∗
    cls ↦*□ clis -∗ ([∗list] cl ∈ clis, clientOk γ cl) -∗
    iprop(∀ i : GoInterface,
      {{ linkv.linkvInOk i }} <<{ ∀∀ S, linkv.linkvState γ S }>>
        (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.Apply)) (Val #cls))
          (Val #i)) @@ linkv.linkvE
      <<{ ∃∃ S' o, linkv.linkvState γ S' ∗
            ⌜(linkv.linkvS (GF := GF)).M.step S (i, o) = some S'⌝ }>>
      {{ RET #o; linkv.linkvS.ioOk i o }})

end spec

end linkv3p
end EtcdGrove
end Perennial
