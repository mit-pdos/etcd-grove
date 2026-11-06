/- Lean-first (no Rocq counterpart). `db.init()` (`examples/osfs/bboltfs/minibolt.go`): lays out `initBytes` (`Pages.lean`) in the file's first four pages, before it is mapped: all four pages with the metas zero (`WriteAt` at 0, which may extend the file), `Fdatasync`, then meta 1 (`WriteAt` at 4096), `Fdatasync`, then meta 0 (`WriteAt` at 0), `Fdatasync`; then `filesz` is at least four pages. The client holds the whole of the file's `OsMeta` `m` (no mapping, no byte lost by a failed sync: `m.ok`) and all of its bytes `xs`. On success, the first four pages are `initBytes` and the rest as before, all clean, and the size and the bytes durable (the `OsMeta` records them); on an error, some `OsMeta` of the file is left (its bytes are lost to the caller, which fails). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Pages
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Store
public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- The file after `init`: `initBytes` over the first four pages, the rest as before, clean. -/
def initFile (xs : List (w8 × Bool)) : List (w8 × Bool) :=
  (initBytes ++ (xs.map Prod.fst).drop 16384).map (·, true)

/-- See the file header. -/
abbrev DB.init.spec : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (i : Ino) (dqf dq : DFrac) (m : OsMeta) (xs : List (w8 × Bool)),
  m.ok = true → m.maps = ∅ → xs.length = m.size → m.size ≤ 2 ^ 40 →
  {{ osInv (GF := GF) ∗ db.[DB, go!"file"] ↦□ f ∗ db.[DB, go!"filesz"] ↦ W64 m.size ∗
      os.ownFile (GF := GF) f fd p dqf ∗ osFd (GF := GF) fd dq ⟨i, true, true⟩ ∗
      osMeta (GF := GF) i (DFrac.own 1) m ∗ osBytes (GF := GF) i 0 (DFrac.own 1) xs }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"init")) (Val #()))
  {{ (err : GoInterface), RET #err;
      os.ownFile (GF := GF) f fd p dqf ∗ osFd (GF := GF) fd dq ⟨i, true, true⟩ ∗
      ((⌜err = interface.nil⌝ ∗
          db.[DB, go!"filesz"] ↦ W64 (max m.size 16384) ∗
          osMeta (GF := GF) i (DFrac.own 1)
            ({ m with size := max m.size 16384, lo := max m.size 16384,
                           hi := max m.size 16384, dur := durOf 0 (initFile xs) }) ∗
          osBytes (GF := GF) i 0 (DFrac.own 1) (initFile xs)) ∨
       (⌜err ≠ interface.nil⌝ ∗ ∃ (sz : w64) (m' : OsMeta),
          db.[DB, go!"filesz"] ↦ sz ∗ osMeta (GF := GF) i (DFrac.own 1) m')) }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
