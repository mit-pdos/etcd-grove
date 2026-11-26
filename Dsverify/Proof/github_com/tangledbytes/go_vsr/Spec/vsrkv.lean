/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/vsrkv.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
Cross-package specs of `examples/vsrkv`: the `*Store` as the model's store (`isStore`), `New`,
`(*Store).Handle` (the model's `VsrModel.handle`), and the method value `store.Handle` as the
replica's `SrvHandler` (`srvOk`: a `func(string) string` taking the model's step on a resource
`P` of the store).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrkv.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Model.Basic

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : vsrkv.Assumptions]

/-- The `*Store` `st` holds the store `m` (exclusive): its map's entries are `m`'s. -/
def vsrkv.isStore (st : Loc) (m : VsrModel.Store) : IProp GF :=
  iprop(∃ (mp : GoMap) (mm : GMap GoString GoString), st ↦ vsrkv.Store.mk mp ∗
    ownMap mp (DFrac.own 1) mm ∗ ⌜∀ k, mm !! k = m k⌝)

instance vsrkv.isStore_timeless (st : Loc) (m : VsrModel.Store) :
    Timeless (vsrkv.isStore (GF := GF) (hG := hG) st m) := by
  unfold vsrkv.isStore; infer_instance

/-- The function value `h` (a `func(string) string`) applies an operation to the store that `P`
holds: from `P m`, `h(op)` returns `handle m op`'s reply with `P` of its store (persistent). -/
def vsrkv.srvOk (h : GoFunc) (P : VsrModel.Store → IProp GF) : IProp GF :=
  iprop(□ ∀ (op : GoString) (m : VsrModel.Store),
    {{ P m }} (App (Val #h) (Val #op))
    {{ RET #(VsrModel.handle m op).2; P (VsrModel.handle m op).1 }})

instance vsrkv.srvOk_persistent (h : GoFunc) (P : VsrModel.Store → IProp GF) :
    Persistent (vsrkv.srvOk (hG := hG) h P) := by
  unfold vsrkv.srvOk; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : vsrkv.Assumptions]

set_option goose.wp.extras true

/-- `New()`: an empty store. -/
abbrev vsrkv.New.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrkv }}
    (App (Val (@! vsrkv.New)) (Val #()))
  {{ (st : Loc), RET #st; vsrkv.isStore st (fun _ => none) }}

/-- `st.Handle(op)`: the model's step (`VsrModel.handle`): its reply, and the new store. -/
abbrev vsrkv.Store.Handle.spec : Prop :=
  ∀ (st : Loc) (m : VsrModel.Store) (op : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrkv ∗
      vsrkv.isStore st m }}
    (App (Val (st @!! go.GoType.PointerType vsrkv.Store.ty @!! go!"Handle")) (Val #op))
  {{ RET #(VsrModel.handle m op).2; vsrkv.isStore st (VsrModel.handle m op).1 }}

/-- The method value `st.Handle` is a handler of `isStore st` (the package initialized). -/
abbrev vsrkv.Store.Handle_value.spec : Prop :=
  ∀ (st : Loc),
  isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrkv ⊢
    vsrkv.srvOk (methods (go.GoType.PointerType vsrkv.Store.ty) go!"Handle" #st)
      (vsrkv.isStore st)

end spec

end Perennial.github_com.tangledbytes.go_vsr.examples
