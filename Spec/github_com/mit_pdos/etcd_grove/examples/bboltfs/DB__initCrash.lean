/- Lean-first (no Rocq counterpart). `db.init()`'s crash-aware spec: `DB.init.spec`
(`DB__init.lean`) over the crash invariant of the database file (`csInv`, `Proof/os/CrashSt.lean`)
whose states satisfy minibolt's crash obligation (`CrashOkS (P1 p) p Good`: every image a crash
may leave is `goodImg`). The client holds its part of the file, idle, nothing frozen
(`csOwn p γ (some ⟨m, xs, 0, 0, .idle⟩)`), in place of the whole `OsMeta` and bytes. Premises
beyond `DB.init.spec`'s: the file is as `Open` found it before `init` (`initIdle`: no valid slot
on disk nor in the page cache, `m.hi ≤ 2^30`), and the bytes of both meta slots are clean in `xs`
(at boot every byte is), so that a write torn over a slot leaves an invalid slot
(`cacheOk_wreach`). Post: on success the file is `initFile xs`, all clean and durable (the
`OsMeta` as `DB.init.spec`'s); on an error, some state of the file. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__init
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.CrashImg
public import Spec.os.CrashSt

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

/-- The meta slots' bytes are clean. -/
def slotsClean (xs : List (w8 × Bool)) : Prop :=
  ∀ i < 2, ∀ k < 64, ∀ x, xs[4096 * i + 16 + k]? = some x → x.2 = true

/-- The `OsMeta` after `init` (as `DB.init.spec`'s): the size at least four pages, all of it
durable and known. -/
def initDoneMeta (m : OsMeta) (xs : List (w8 × Bool)) : OsMeta :=
  { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384,
           dur := durOf 0 (initFile xs), durHi := max m.size 16384 }

/-- See the file header. -/
abbrev DB.init.specCrash : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (dqf dq : DFrac) (N : Namespace) (γ : GName)
    (m : OsMeta) (xs : List (w8 × Bool)),
  m.ok = true → m.maps = ∅ → m.size ≤ 2 ^ 30 → initIdle m xs → slotsClean xs →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N p γ (CrashOkS (P1 p) p Good) ∗
      db.[DB, go!"file"] ↦□ f ∗ db.[DB, go!"filesz"] ↦ W64 m.size ∗
      os.ownFile (GF := GF) f fd p dqf ∗ osFd (GF := GF) fd dq ⟨p, true, true⟩ ∗
      csOwn (GF := GF) p γ (some ⟨m, xs, 0, 0, .idle⟩) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"init")) (Val #()))
  {{ (err : GoInterface), RET #err;
      os.ownFile (GF := GF) f fd p dqf ∗ osFd (GF := GF) fd dq ⟨p, true, true⟩ ∗
      ((⌜err = interface.nil⌝ ∗
          db.[DB, go!"filesz"] ↦ W64 (max m.size 16384) ∗
          csOwn (GF := GF) p γ (some ⟨initDoneMeta m xs, initFile xs, 0, 0, .idle⟩)) ∨
       (⌜err ≠ interface.nil⌝ ∗ ∃ (sz : w64) (s' : CSt),
          db.[DB, go!"filesz"] ↦ sz ∗ csOwn (GF := GF) p γ (some s'))) }}

end spec

end bboltfs
end EtcdGrove
end Perennial
