/- Lean-first (no Rocq counterpart). `db.init()`'s crash-aware spec: `DB.init.spec`
(`DB__init.lean`) over the crash invariant of the database file (`csInv`, `Proof/os/CrashSt.lean`)
whose states satisfy minibolt's crash obligation (`dbOk`: every crash is `Good`, under P1). The
client holds its part of the file, idle, nothing frozen (`csOwnF γ (some (i, ⟨m, xs, 0, 0,
.idle⟩))`), in place of the whole `OsMeta` and bytes. Premise beyond `DB.init.spec`'s: the file is
as `Open` found it before `init` (`initIdle`: at most 1 GiB since the last sync, and both meta
slots, past the size included, known clean and invalid). Post: on success the file is
`initFile xs`, all durable, its `OsMeta` `DB.init.spec`'s (`initDoneMeta`); on an error, some
state of the file. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__init
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashImg
public import LinuxFs.Spec.os.CrashSt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open Fs

/-- The `OsMeta` after `init` (as `DB.init.spec`'s): synced, at the size `init` leaves. -/
def initDoneMeta (m : OsMeta) : OsMeta :=
  ({ m with size := max m.size 16384, cz := pwCz m 0 16384 16384 } : OsMeta).synced

/-- The file as `Open` hands it to `init` (the state `⟨m, xs, 0, 0, .idle⟩`): its bytes `xs`, its
size and crash bounds at most 1 GiB, and each meta slot known clean (its bytes' candidates, past
the size included) and invalid. -/
structure initIdle [GooseExts] (m : OsMeta) (xs : List ByteG) : Prop where
  len : xs.length = m.size
  hi : m.hi ≤ 2 ^ 30
  slots : ∀ j < 2, ∃ X : List w8, X.length = 64 ∧ ¬ metaValid (decode X : Meta) ∧
    ∀ k < 64, (⟨m, xs, 0, 0, .idle⟩ : CSt).kc (4096 * j + 16 + k) = some [(X.getD k 0, 0)]

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- See the file header. -/
abbrev DB.init.specCrash : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (dqf dq : DFrac) (N : Namespace) (P : GoString)
    (R : Roots) (γ : GName) (i : Ino) (m : OsMeta) (xs : List ByteG),
  m.maps = ∅ → m.size ≤ 2 ^ 30 → initIdle m xs → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N P R γ Good dbOk ∗
      db.[DB, go!"file"] ↦□ f ∗ db.[DB, go!"filesz"] ↦ W64 m.size ∗
      os.ownFile (GF := GF) f fd p dqf ∗ osFd (GF := GF) fd dq ⟨i, true, true⟩ ∗
      csOwnF (GF := GF) γ (some (i, ⟨m, xs, 0, 0, .idle⟩)) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"init")) (Val #()))
  {{ (err : GoInterface), RET #err;
      os.ownFile (GF := GF) f fd p dqf ∗ osFd (GF := GF) fd dq ⟨i, true, true⟩ ∗
      ((⌜err = interface.nil⌝ ∗
          db.[DB, go!"filesz"] ↦ W64 (max m.size 16384) ∗
          csOwnF (GF := GF) γ (some (i, ⟨initDoneMeta m, initFile xs, 0, 0, .idle⟩))) ∨
       (⌜err ≠ interface.nil⌝ ∗ ∃ (sz : w64) (s' : CSt),
          db.[DB, go!"filesz"] ↦ sz ∗ csOwnF (GF := GF) γ (some (i, s')))) }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
