/-
**The bodies of the WAL's axioms whose posts name a past state** (W4a.1 revision 1, 2026-11-12; the
delta review's M1 and its consistency check (4), `notes/decisions.md`, "WAL W4a.1 revision 1").
Proved: nothing here is trusted.

The WAL is names-only (`Spec/go_etcd_io/etcd/server/v3/storage/wal/`): each function's spec is an
axiom, and an axiomatized body is read as one that performs the abstract-disk extension's steps.
An axiom is consistent with the extension when such a body exists (the approved W4 Draft's §1.6).
For each post that gives a fact about a past state (`walNamed`, `walSyncedLb`), the lemmas below
are that body, as the steps in order, each with the resource it uses: a model of the axiom's ghost
behaviour, derived from the proved step specs of `GooseLang/Ext/AbsDisk/Specs.lean` alone.

* `Create` (`walCreate_body`): `"WalCreate"` is the commit (the atomic update's `walAbsent` turned
  into `walDiskAt dir (walDurFresh md)`); then, the update consumed, `"WalNamed"` from the handle's
  length fact alone (`wp_WalNamedLen`), giving `walNamed`. The client's copy keeps `named = false`
  as a lower bound, so the two do not contradict each other (B1).
* `Save` and `SaveSnapshot` (`walAppendSync_body`, with the operation each writes): `"WalAppend"`
  is the commit; then `"WalSync"` of the new length from the handle's fact (`walOpenW_lenLb`,
  `wp_WalSyncLen`), giving `walSyncedLb` (M1: before revision 1 this step needed the `walDiskAt`
  the commit had handed to the client).
* `Sync` (`walSync_body`): `"WalSync"` from the handle's fact.
* `Close`'s first conjunct (`walClose_commit`): inside the access the body performs `"WalSync"` of
  the history's length with the accessed `walDiskAt` and commits it unchanged (the mark a lower
  bound, `walDiskAt_weaken`), giving `walSyncedLb dir |H|`; then `wp_WalCloseHandle` (the token).
* `ReadAll` (`walReadAll_sync_named`): a plain triple that holds `walDiskAt` throughout; its sync and
  name steps use it (shown for the two steps that give its past-state facts).

**What the lemmas do not show** (the re-review's m-b). With `wp_WalSyncLen`, any `walSyncedLb n`
backed by a `walLenLb n` has a body, so the faithfulness of each sync claim rests on Go: a real body
performs `"WalSync"` only at a Go fsync point (`Save` under `walMustSync` or at a cut, `SaveSnapshot`,
`Sync`, `Close`, `ReadAll`'s F-Z); `walAppendSync_body` shows the sync unconditionally, and `Save`'s
body performs it only on that branch (otherwise the model's mark would exceed Go's synced prefix). A
body's length argument (`|d.H|` from the accessed `d`, fixed before the atomic step) is determined
because the handle (`walOpenW`, with the generation's lock token) excludes every other writer of `H`:
the body tracks the length itself.

Also not modelled: how a body computes a step's argument (an operation from its heap
arguments, a length it tracks), as the Draft argued for every argument (`walCode`'s docstring); the
lemmas take the argument the axiom names. And the reads (`ValidSnapshotEntries`, `ReadAll`'s result,
`Exist`): every step returns `#()`, so a read's result is argued logically, a function of the state
the accessed resource names.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section bodies
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt] [go_gctx : GoGlobalContext]
  [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **`Create`'s body**: the commit at `"WalCreate"`, then `"WalNamed"` from the handle alone. The
post is `Create`'s success post. -/
theorem walCreate_body (w : Loc) (r dir : GoString) (md : List w8) (Q : IProp GF)
    (hdir : walAreaDir r dir) :
    walArea (L := hG.goose_localGS) r ∗ walUnlockedTok (L := hG.goose_localGS) ∗
      AU <{ walAbsent (L := hG.goose_localGS) dir }> @ ⊤, ∅
        <{ walDiskAt (L := hG.goose_localGS) dir (walDurFresh md), COMM Q }>
    ⊢ WP (ExternalOp absDiskExt.name "WalCreate" (Val (PairV (#dir) (#md)))) {{ _v,
        WP (ExternalOp absDiskExt.name "WalNamed" (Val (#dir))) {{ _u,
          Q ∗ walOpenW (L := hG.goose_localGS) w dir ∗ walNamed (L := hG.goose_localGS) dir ∗
          walLenLb (L := hG.goose_localGS) w dir 0 ∗ walSyncedLb (L := hG.goose_localGS) dir 0 ∗
          walPurgeW (L := hG.goose_localGS) w dir }} }} := by
  iintro ⟨#HA, Hu, HAU⟩
  iapply wp_WalCreate w r dir md hdir
  iframe HA Hu
  ihave HAC := aupd_aacc $$ HAU
  iunfold atomic_acc at HAC
  imod HAC with HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at HAC
  icases HAC with ⟨Ha, Hcl⟩
  imodintro
  iframe Ha
  iintro Hd Hw Hpw %s' #Hp %hs
  icases Hcl with ⟨-, Hcommit⟩
  inext
  imod Hcommit $$ Hd with HQ
  imodintro
  icases walOpenW_lenLb w dir s' (walDurFresh md) 0 hs (Nat.zero_le _) $$ Hw Hp with ⟨Hw, #Hl⟩
  iapply wp_WalNamedLen w dir 0
  iframe Hl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose #Hn
  inext
  imod Hclose
  imodintro
  iframe HQ Hw Hn Hpw
  unfold walSyncedLb
  iexists s', _
  iframe Hp
  ipureintro; exact ⟨hs, Nat.le_refl _⟩

/-- **`Save`'s and `SaveSnapshot`'s body** (the operation `o` they write): the commit at
`"WalAppend"`, then `"WalSync"` of the new length from the handle alone. The post gives what their
success posts give: `Q d`, the handle, its length fact, and the sync's fact (`Save` performs the
sync when it must, `SaveSnapshot` always). -/
theorem walAppendSync_body (w : Loc) (dir : GoString) (o : WalOpG WalEnt) (P : WalDur → Prop)
    (Q : WalDur → IProp GF) :
    walOpenW (L := hG.goose_localGS) w dir ∗
      AU <{ ∃∃ d : WalDur, walDiskAt (L := hG.goose_localGS) dir d ∗ ⌜P d⌝ }> @ ⊤, ∅
        <{ walDiskAt (L := hG.goose_localGS) dir { d with H := d.H ++ [o] }, COMM Q d }>
    ⊢ WP (ExternalOp absDiskExt.name "WalAppend" (Val (PairV (#dir) (#(walCode o))))) {{ _v,
        ∃ d : WalDur, Q d ∗ walOpenW (L := hG.goose_localGS) w dir ∗
          walLenLb (L := hG.goose_localGS) w dir (d.H.length + 1) ∗
          WP (ExternalOp absDiskExt.name "WalSync" (Val (PairV (#dir) (#(walCode (d.H.length + 1))))))
            {{ _u, walSyncedLb (L := hG.goose_localGS) dir (d.H.length + 1) }} }} := by
  iintro ⟨Hw, HAU⟩
  ihave HAC := aupd_aacc $$ HAU
  iunfold atomic_acc at HAC
  iapply wp_WalAppendAcc dir o
  imod HAC with HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at HAC
  icases HAC with ⟨%d, ⟨Hd, %HP⟩, Hcl⟩
  imodintro
  iexists d
  iframe Hd
  iintro Hd %s' #Hp %hs
  icases Hcl with ⟨-, Hcommit⟩
  inext
  imod Hcommit $$ Hd with HQ
  imodintro
  obtain ⟨d', hd', hle⟩ := hs
  have hlen : d.H.length + 1 ≤ d'.H.length := by rw [← hle.1]; simp
  icases walOpenW_lenLb w dir s' d' (d.H.length + 1) hd' hlen $$ Hw Hp with ⟨Hw, #Hl⟩
  iexists d
  iframe HQ Hw Hl
  iapply wp_WalSyncLen w dir (d.H.length + 1)
  iframe Hl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose #Hs
  inext
  imod Hclose
  imodintro
  iexact Hs

/-- **`Sync`'s body**: `"WalSync"` from the handle's length fact alone. -/
theorem walSync_body (w : Loc) (dir : GoString) (n : Nat) :
    walLenLb (L := hG.goose_localGS) w dir n
    ⊢ WP (ExternalOp absDiskExt.name "WalSync" (Val (PairV (#dir) (#(walCode n))))) {{ _u,
        walSyncedLb (L := hG.goose_localGS) dir n }} := by
  iintro #Hl
  iapply wp_WalSyncLen w dir n
  iframe Hl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose #Hs
  inext
  imod Hclose
  imodintro
  iexact Hs

/-- **`Close`'s commit** (its first conjunct, logically atomic): at the access, with the accessed
`walDiskAt dir d`, the body performs `"WalSync"` of `|d.H|` and commits the same `d`, so the client's
`Q d` comes with `walSyncedLb dir |d.H|`. Stated at the access (`d` given): the body's argument is
the length it tracks. -/
theorem walClose_commit (dir : GoString) (d : WalDur) (Ψ : IProp GF)
    (Φ : val → IProp GF) :
    (|={⊤,∅}=> walDiskAt (L := hG.goose_localGS) dir d ∗
        (walDiskAt (L := hG.goose_localGS) dir d ={∅,⊤}=∗ Ψ)) ∗
      (Ψ -∗ walSyncedLb (L := hG.goose_localGS) dir d.H.length -∗ Φ #())
    ⊢ WP (ExternalOp absDiskExt.name "WalSync" (Val (PairV (#dir) (#(walCode d.H.length)))))
        {{ Φ }} := by
  iintro ⟨Hacc, HΦ⟩
  iapply wp_WalSync dir d.H.length d (Nat.le_refl _)
  imod Hacc with ⟨Hd, Hcommit⟩
  imodintro
  iframe Hd
  iintro Hd %s' #Hp %hs
  obtain ⟨d', hd', hle⟩ := hs
  ihave Hd := walDiskAt_weaken dir d { d with m := max d.m d.H.length }
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_max_left _ _, id⟩ $$ Hd
  inext
  imod Hcommit $$ Hd with HΨ
  imodintro
  iapply HΦ $$ HΨ
  unfold walSyncedLb
  iexists s', d'
  iframe Hp
  ipureintro
  exact ⟨hd', Nat.le_trans (Nat.le_max_right _ _) hle.2.2.2.2.2.2.1⟩

/-- **`ReadAll`'s sync and name steps** (a plain triple: it holds `walDiskAt` throughout): the
`"WalSync"` of `|H|` (F-Z), then `"WalNamed"` that also makes the handle ready to append (F-N4),
giving its past-state facts. -/
theorem walReadAll_sync_named (w : Loc) (dir : GoString) (s : w64 × w64) (d : WalDur) :
    walDiskAt (L := hG.goose_localGS) dir d ∗ walOpening (L := hG.goose_localGS) w dir s
    ⊢ WP (ExternalOp absDiskExt.name "WalSync" (Val (PairV (#dir) (#(walCode d.H.length))))) {{ _v,
        WP (ExternalOp absDiskExt.name "WalNamed" (Val (#dir))) {{ _u,
          walDiskAt (L := hG.goose_localGS) dir { { d with m := max d.m d.H.length } with named := true } ∗
          walOpenW (L := hG.goose_localGS) w dir ∗ walPurgeW (L := hG.goose_localGS) w dir ∗
          walNamed (L := hG.goose_localGS) dir ∗ walSyncedLb (L := hG.goose_localGS) dir d.H.length }} }} := by
  iintro ⟨Hd, Ho⟩
  iapply wp_WalSync dir d.H.length d (Nat.le_refl _)
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iframe Hd
  iintro Hd %s1 #Hp1 %hs1
  inext
  imod Hclose
  imodintro
  iapply wp_WalNamedOpen w dir s { d with m := max d.m d.H.length }
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iframe Hd Ho
  iintro Hd ⟨Hw, Hpw⟩ %s2 #Hp2 %hs2
  inext
  imod Hclose
  imodintro
  iframe Hd Hw Hpw
  obtain ⟨d1, hd1, hle1⟩ := hs1
  obtain ⟨d2, hd2, hle2⟩ := hs2
  isplitl
  · unfold walNamed
    iexists s2, d2; iframe Hp2; ipureintro; exact ⟨hd2, hle2.2.2.2.2.2.2.2 rfl⟩
  · unfold walSyncedLb
    iexists s1, d1; iframe Hp1; ipureintro
    exact ⟨hd1, Nat.le_trans (Nat.le_max_right _ _) hle1.2.2.2.2.2.2.1⟩

end bodies

end EtcdGrove
end Perennial
