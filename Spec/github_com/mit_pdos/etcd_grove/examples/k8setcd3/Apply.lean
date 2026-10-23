/- Lean-first (no Rocq counterpart).

`Apply(s, input)` (k8setcd3.go): one operation through the store `s`, logically atomic against
the driver's model (`k8setcd3S g0`: `pM (kSpec g0) decOp`, from the seeded store `g0`), in the
form `lintest`'s `applySpec` takes for the closure `Check` passes,
`func(input any) any { return Apply(s, input) }`:

  `{{ kInOk i }} <<{ ∀∀ S, kState γ g0 S }>> Apply(s, i) @@ drvE
     <<{ ∃∃ S' o, kState γ g0 S' ∗ ⌜(k8setcd3S g0).M.step S (i, o) = some S'⌝ }>>
     {{ RET #o; ioOk i o }}`

over the library's state `kState γ g0 S` (the history's ghost variable, whose other half is in the
instance's invariant `kInv γ c g0 γr.kv` at each member: `Proof/.../k8setcd3/Inv.lean`). The input
is one `Gen` may return (`kInOk`).

Premises: the store `s` (`isStore sp c`) holds the driver's objects (`c.S = driverSpec`) under
the driver's prefixes (`"/registry"`, `"/objs"`), the packages' facts, and `errors.As`'s target
(the client's context lemma).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI k8s github_com.anishathalye.porcupine
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)
open go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev Apply.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    (γ : KNames) (sp : Loc) (c : StoreCfg GF DObj) (g0 : GSt),
  c.S = driverSpec → c.pathPrefix = go!"/registry" → c.resourcePrefix = go!"/objs" →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 -∗
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 -∗
    k8s.isStore sp c -∗ ([∗list] sv ∈ c.ms, kInv γ c g0 sv.γr.kv) -∗ ⌜c.ms ≠ []⌝ -∗
    iprop(∀ i : GoInterface,
      {{ kInOk i }} <<{ ∀∀ S, kState γ g0 S }>>
        (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.Apply))
          (Val #(interface.mkOk (go.GoType.PointerType
            k8s_io.apiserver.pkg.storage.etcd3.store.ty) #sp))) (Val #i)) @@ drvE
      <<{ ∃∃ S' o, kState γ g0 S' ∗ ⌜(k8setcd3S (GF := GF) g0).M.step S (i, o) = some S'⌝ }>>
      {{ RET #o; (k8setcd3S (GF := GF) g0).ioOk i o }})

end spec

end k8setcd3
end EtcdGrove
end Perennial
