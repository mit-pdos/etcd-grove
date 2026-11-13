/- Lean-first (no Rocq counterpart).

# `Create`'s parent fsync: the WAL becomes named (W4, `notes/wal-fsext-plan.md`, "W4 implementation log")

After `Create`'s rename of `nm.tmp` onto `nm` (the entry `x`, the last writer of `nm` in the program's
claim `h` on names `N ∋ nm`, holding the WAL's directory `J`), the parent's fsync gives `osCommitLb n`
with `x < n`. Then every crash keeps the rename, so the WAL's crash condition holds with `named`
raised (`crashOk_named_of_lastWrite`), and the WAL state takes the step to `named = true`, a past state
of which is `walNamed dir`.

* `walsOk_mono`: the invariant's pure facts at a bigger commit bound.
* `walsOk_named`: ... and with the WAL in `dir` named.
* `walInvBody_named`: the step on the invariant's contents, with the program's claim (a fraction) and
  the commit bound; the claim is matched with the invariant's (`WalsCreateOk`: one of its claims
  holds `nm`; two claims of one directory holding a name are one, `NamesCoh.disj`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamedPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashPure

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

theorem crashOk_mono {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {cl : List Claim}
    {n0 n : Nat} (hn : n0 ≤ n) (h : CrashOk C Mr d lay cl n0) : CrashOk C Mr d lay cl n :=
  fun m' fo hr => h m' fo (regionCrashed_mono hn hr)

/-- **The invariant's pure facts at a bigger commit bound.** -/
theorem walsOk_mono {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n)
    (h : WalsOk C Mr R jr s Ls cl n0) : WalsOk C Mr R jr s Ls cl n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun dir d hd => ?_, h2, h3, h4, fun dir nm hin hn' m' hr => h5 dir nm hin hn' m'
    (regionCrashed_mono hn hr), fun dd hdd m' hr => h6 dd hdd m' (regionCrashed_mono hn hr)⟩
  obtain ⟨lay, nm, hj, hl, hin, hjr, hnm, hc, ha, hok⟩ := h1 dir d hd
  exact ⟨lay, nm, hj, hl, hin, hjr, hnm, hc, ha, crashOk_mono hn hok⟩

/-- The static relation does not depend on `named`. -/
theorem walAbsD_named {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (b : Bool) (h : WalAbsD C Mr d lay ents) : WalAbsD C Mr { d with named := b } lay ents := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- The step raising `named` of the WAL in `dir`. -/
def setNamed (s : AbsDiskState) (dir : GoString) : AbsDiskState :=
  absDiskUpd s dir (fun d => { d with named := true })

/-- **The invariant's pure facts with the WAL in `dir` named**, its name's last writer (holding a
directory) committed. -/
theorem walsOk_named {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n0 n : Nat} (hn : n0 ≤ n)
    (hok : WalsOk C Mr R jr s Ls cl n0) {dir nm : GoString} {d : WalDur}
    (hd : s.wal !! dir = some d) (hin : InArea s.area dir nm) {N : NameSet} {h : NamesH} {x : Nat}
    {e : LogEntry} {E : Ents} {J : Ino} (hc : (jr, N, h) ∈ cl) (hN : N.Mem nm)
    (hl : LastWrite h jr nm x e E) (hx : x < n) (hJ : E !! nm = some (.dir J)) :
    WalsOk C Mr R jr (setNamed s dir) Ls cl n := by
  have hok' := walsOk_mono hn hok
  have hw : (setNamed s dir).wal = <[dir := { d with named := true }]> s.wal :=
    absDiskUpd_wal s dir _ d hd
  have harea : (setNamed s dir).area = s.area := absDiskUpd_area s dir _
  have hdirs : (setNamed s dir).dirs = s.dirs := by
    unfold setNamed absDiskUpd; rw [hd]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hok'
  refine ⟨fun dir' d' hd' => ?_, fun dir' hn' => h2 dir' ?_, h3, h4, ?_, ?_⟩
  · rw [hw] at hd'
    by_cases he : dir' = dir
    · subst he
      rw [GMap.lookup_insert_eq] at hd'
      cases hd'
      obtain ⟨lay, nm', hj, hlay, hin', hjr, hnm, hcl, ha, -⟩ := h1 dir' d hd
      have hnmeq : nm' = nm := inArea_name hin' hin
      subst hnmeq
      have hok0 := (hok.1 dir' d hd)
      obtain ⟨lay0, nm0, hj0, hlay0, hin0, hjr0, hnm0, -, -, hco⟩ := hok0
      rw [hlay] at hlay0; cases hlay0
      refine ⟨lay, nm', hj, hlay, by rw [harea]; exact hin', hjr, hnm, hcl, walAbsD_named true ha, ?_⟩
      refine crashOk_named_of_lastWrite C Mr d lay cl n0 n hn hco (N := N) (h := h) (x := x) (e := e)
        (E := E) (J := J) (by rw [hjr]; exact hc) (by rw [hnm]; exact hN)
        (by rw [hjr, hnm]; exact hl) hx (by rw [hnm]; exact hJ)
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hd'
      obtain ⟨lay, nm', hj, hlay, hin', rest⟩ := h1 dir' d' hd'
      exact ⟨lay, nm', hj, hlay, by rw [harea]; exact hin', rest⟩
  · rw [hw] at hn'
    by_cases he : dir' = dir
    · subst he; rw [GMap.lookup_insert_eq] at hn'; cases hn'
    · rwa [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hn'
  · intro dir' nm' hin' hn' m' hr J' hJ'
    rw [harea] at hin'
    rw [hw] at hn'
    by_cases he : dir' = dir
    · subst he; rw [GMap.lookup_insert_eq] at hn'; cases hn'
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hn'
      exact h5 dir' nm' hin' hn' m' hr J' hJ'
  · intro dd hdd m' hr
    rw [hdirs] at hdd
    exact h6 dd hdd m' hr

theorem absLe_setNamed (s : AbsDiskState) (dir : GoString) : absLe s (setNamed s dir) :=
  absLe_upd s dir _ (fun d => ⟨Nat.le_refl _, Nat.le_refl _, fun _ => rfl⟩)

theorem walMapLe_setNamed (G : GMap GoString WalDur) (s : AbsDiskState) (dir : GoString)
    (hG : walMapLe G s.wal) : walMapLe G (setNamed s dir).wal :=
  walMapLe_upd G s dir _ (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, fun _ => rfl⟩) hG

end pure

end WalFs
end EtcdGrove
end Perennial

end
