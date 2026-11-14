/- Lean-first (no Rocq counterpart).

# The invariant laws `ReadAll` reads its WAL through (W3/W5 of `notes/wal-fsext-plan.md`, fourteenth session)

One statement, `WalReadState` (a hypothesis of `WAL.ReadAll.wp_proof` until the invariant's owner
proves it; no `sorry`), of two parts, both read at a program step, holding the WAL's key and the empty program half of the
tails' authority (`walReadTie`'s: no tail registered, so no change in flight on the WAL's files,
`walTailsRes_none`), and give what `readAll_success` (`ReadAllPure.lean`) takes.

* `WalTailIdle`: a WAL whose tail no handle has registered has its last segment's stream all written
  (`lay.wr` its length) and no resize window open on it (`TailExact`). Not in `walInvBody` yet: a
  generation's crash gives it (`CrashStart`: `wr = so = z0 = |stream|`), `Create`'s commit (`htail`), and a
  handle's unregistration would (`Close` after its sync: W10). A `Save` that fails leaves its tail
  registered (the handle is lost with the lock token), so the law does not constrain a WAL with a
  half-written record. Without it `ReadAll` could succeed with the history's last records missing (the
  reader stops at the zeros past `wr`).
* `WalPinnedSegs`: the segments a handle pinned (`walReadTie`'s `gs`, the program's halves held) are the
  layout's from some position on (purges remove only earlier, unlocked, segments; nothing appends or cuts
  without the tail registered).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The WAL as `ReadAll` reads it** (hypothesis; see the file header): its state `d`, the invariant's
layout and directory names, the tail idle (`WalTailIdle`), the cuts positive, and the pinned segments the
layout's from `kk` on (`WalPinnedSegs`). -/
def WalReadState (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : Prop :=
  ∀ (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (gs : List SegG),
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      walTailsFrag (W := W) ∅ -∗
      walOutFrag (W := W) ⟨gs.map (·.ino), [(j, .except X)], [dir]⟩ -∗
      ([∗list] g ∈ gs, osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) -∗
      ∃ (d : WalDur) (lay : WalLay) (hj : NamesH) (kk : Nat),
        ⌜s.wal !! dir = some d ∧ lay.j = j ∧ WalAbsD C Mr d lay hj.cur ∧ TailExact lay ∧
          lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧ (∀ b ∈ lay.cuts, 0 < b) ∧
          lay.segs.drop kk = gs⌝ ∗
        walInvBody (L := L) (W := W) C Mr R jr r s ∗ walTailsFrag (W := W) ∅ ∗
        walOutFrag (W := W) ⟨gs.map (·.ino), [(j, .except X)], [dir]⟩ ∗
        ([∗list] g ∈ gs, osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
          osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs)

end laws

end WalFs
end EtcdGrove
end Perennial
