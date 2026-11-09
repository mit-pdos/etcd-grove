/- Lean-first (no Rocq counterpart). `db.init()`'s crash-aware spec: `DB.init.spec`
(`DB__init.lean`) over the crash invariant of the database file (`csInv`, `Proof/os/CrashSt.lean`)
whose states satisfy minibolt's crash obligation (`dbOk`: every crash is `Good`), over a semantics
whose `pwrite`s land page cuts (`FsStepSat NoTearStep`). The client holds its part of the file,
idle, nothing frozen (`csOwnF γ (some (i, ⟨m, xs, 0, 0, .idle⟩))`), in place of the whole `OsMeta`
and bytes. Premise beyond `DB.init.spec`'s: the file is as `Open` found it before `init`
(`initIdle`: at most 1 GiB since the last sync, one version of each sector, fresh sectors known from
at most its last page on, no valid slot on disk in a page that holds a byte of it). Post: on success
the file is `initFile xs`, all clean and durable (the `OsMeta` as `DB.init.spec`'s); on an error,
some state of the file. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__init
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashImg
public import Spec.os.CrashSt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open Fs

/-- The `OsMeta` after `init` (as `DB.init.spec`'s): the size at least four pages, all of it
durable and known, one version of each sector, the fresh sectors known `r`. -/
def initDoneMeta [GooseExts] (m : OsMeta) (xs : List (w8 × Bool)) (r : Option Nat) : OsMeta :=
  { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384,
           dur := durOf 0 (initFile xs), vk := some [], dz := none, fr := r }

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [FsStepSat NoTearStep]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- See the file header. -/
abbrev DB.init.specCrash : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (dqf dq : DFrac) (N : Namespace) (P : GoString)
    (R : Roots) (γ : GName) (i : Ino) (m : OsMeta) (xs : List (w8 × Bool)),
  m.ok = true → m.maps = ∅ → m.size ≤ 2 ^ 30 → initIdle m xs → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N P R γ Good dbOk ∗
      db.[DB, go!"file"] ↦□ f ∗ db.[DB, go!"filesz"] ↦ W64 m.size ∗
      os.ownFile (GF := GF) f fd p dqf ∗ osFd (GF := GF) fd dq ⟨i, true, true⟩ ∗
      csOwnF (GF := GF) γ (some (i, ⟨m, xs, 0, 0, .idle⟩)) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"init")) (Val #()))
  {{ (err : GoInterface), RET #err;
      os.ownFile (GF := GF) f fd p dqf ∗ osFd (GF := GF) fd dq ⟨i, true, true⟩ ∗
      ((⌜err = interface.nil⌝ ∗
          db.[DB, go!"filesz"] ↦ W64 (max m.size 16384) ∗ ∃ r : Option Nat,
          csOwnF (GF := GF) γ (some (i, ⟨initDoneMeta m xs r, initFile xs, 0, 0, .idle⟩))) ∨
       (⌜err ≠ interface.nil⌝ ∗ ∃ (sz : w64) (s' : CSt),
          db.[DB, go!"filesz"] ↦ sz ∗ csOwnF (GF := GF) γ (some (i, s')))) }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
