/- Lean-first (no Rocq counterpart). `Open(path)` (`examples/bboltfs/minibolt.go`): opens (or creates) the database at `path`, an allowed path, given the whole of its `OsMeta` and, if it exists, all of its bytes, which `fileOk` accepts. On success, an open database (`isDB`), its committer token at the current txid and high water mark, a lower bound of the txid, and every reader token. On an error, the file is closed, and its `OsMeta` is that of the path after an open (it may have been created) with a size that `init` may have changed; its bytes are lost to the caller (a crash proof would keep them). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. -/
abbrev Open.spec : Prop :=
  ∀ (path : GoString) (mo : Option OsMeta) (xs : List (w8 × Bool)),
  (∀ m, mo = some m → xs.length = m.size ∧ m.maps = ∅ ∧ fileOk xs) →
  {{ osInv (GF := GF) ∗ osMeta (GF := GF) path (DFrac.own 1) mo ∗
      (match mo with
       | none => emp
       | some _ => osBytes (GF := GF) path 0 (DFrac.own 1) xs) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.Open)) (Val #path))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err);
      (⌜err = interface.nil⌝ ∗ ∃ (γ : DBNames) (t n : Nat),
          isDB (GF := GF) γ db ∗ dbOwner (GF := GF) γ t n ∗ dbLast (GF := GF) γ t ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            dbReader (GF := GF) γ db)) ∨
      (⌜err ≠ interface.nil ∧ db = null⌝ ∗ ∃ mo', osMeta (GF := GF) path (DFrac.own 1) mo') }}

end spec

end bboltfs
end EtcdGrove
end Perennial
