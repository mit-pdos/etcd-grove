module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model
public import Proof.go_etcd_io.bbolt.internal.freelist.ArrayModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.Allocate(txid, n)`: the first run of `n` consecutive free ids (the one ending first),
now allocated by `txid`, its first id returned; `0` if there is none. -/
abbrev array.Allocate.spec : Prop :=
  ∀ (a s : Loc) (σ : FLState) (txid n : w64), 0 < sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL (arrayImpl (GF := GF) a) s σ }}
    (App (App (Val (a @!! go.GoType.PointerType array'.ty @!! go!"Allocate")) (Val #txid)) (Val #n))
  {{ (r : w64), RET #r;
      ⌜r = W64 0 ∧ ∀ i, ¬ runEnd σ.free (sint.nat n) i⌝ ∗ ownFL (arrayImpl a) s σ ∨
      ∃ (i : Nat), ⌜runEnd σ.free (sint.nat n) i ∧ (∀ i' < i, ¬ runEnd σ.free (sint.nat n) i') ∧
        σ.free[i + 1 - sint.nat n]? = some r⌝ ∗
        ownFL (arrayImpl a) s (σ.allocate txid r (sint.nat n)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
