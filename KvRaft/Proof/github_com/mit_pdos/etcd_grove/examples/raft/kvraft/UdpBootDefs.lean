/-
# kvraft-udp's boot counter: its file, crash-aware (2026-11-24)

`notes/kvraft-udp-proof-plan.md`, "The boot counter". Each process of replica `id` takes a boot number one
more than the last process's (`nextBoot`), from the durable file `kvBootFileName dir id`
(`BootFileOf`), written with `durable.Write` before the number is used, so that no two processes of
the replica share one, across crashes. The ghost state says so with `udpHi γu id hi` (`UdpDefs.lean`:
the names' invariant has every counter `(id, b)` at `b ≤ hi`), which lives in the generation's **boot
file invariant** `udpBootInv γu id bn`, tied to the file: `hi` is at most what every contents a crash
may leave hold (`BootOk hi s`, over `durable`'s client state `s`: `cur`, and `alt` during a write's
window). So:

* `nextBoot` reads `n` (`cur`, so `hi ≤ n`), writes `n + 1`: at the rename (`cur := n+1, alt := n`)
  `BootOk` still holds; at the directory's sync (`alt := none`) it bumps `hi` to `n + 1` and, in the
  same atomic update, allocates the process's counter `(id, n + 1) ↦ 0` (fresh: every counter of `id`
  is at most the old `hi ≤ n`), returning `udpCtr γu id (n+1) 0`. A crash before the sync leaves `cur`
  or `alt`, both at least `hi`; after it, `cur = n + 1 = hi`.
* The writer's half `ghostVar bn.wr ½ s` (the other half is the invariant's) pins `s` for the
  handle's holder between the read and the write, as kvraft's `kdWriter`.
* The crash obligation opens the invariant with its token `bn.tk` and closes it on its crashed side,
  taking `udpHi` and the state; `durable`'s crash lemma gives the next generation contents `v = cur ∨
  alt = some v`, both holding a number at least `hi` (`udp_boot_crash`); the next generation's boot
  allocates a new invariant (`udp_boot_alloc`).

* `udpBootStart γu id dir bn qc`: what `nextBoot` (and `openUDP`, `startNodeUDP`) takes: `durable`'s
  and `os`'s invariants for the file `bn.df` (named `BootFileOf(dir, id)`), the handle, a fraction of
  the directory's call permission (the replica's storage file is in the same directory: the boot
  shares the root's call permission with `kvStart`), the invariant and the writer's half outside a
  window.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TopBoot
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.UdpDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

/-- **The boot counter's file state `s` bounds `hi`** (see the file header): every contents a crash
may leave hold a number at least `hi`. -/
def BootOk (hi : w64) (s : DurFs.DurSt) : Prop :=
  (∃ n, bootVal s.cur n ∧ uint.nat hi ≤ uint.nat n) ∧
  ∀ old, s.alt = some old → ∃ n, bootVal old n ∧ uint.nat hi ≤ uint.nat n

/-- A generation's boot file names: `durable`'s names, the file, its roots; the writer's variable; the
invariant's crash token. -/
structure UdpBootNames where
  γd : DurFs.DurGS
  df : DurFs.DFile
  fR : Fs.Roots
  wr : GName
  tk : GName

/-- The boot invariant's namespace. -/
def udpBootN : Namespace := (nroot .@ "kvraft_udp") .@ "boot"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

/-- The boot invariant's body (see the file header). -/
def udpBootBody (γu : UdpNames) (id : w64) (bn : UdpBootNames) : IProp GF :=
  iprop(∃ s : DurFs.DurSt, DurFs.durSt bn.γd s ∗ ghostVar bn.wr (1 : Qp).half s ∗
    ((∃ hi, udpHi γu id hi ∗ ⌜BootOk hi s⌝) ∨ crashed ∗ token bn.tk))

/-- **Replica `id`'s boot file invariant**, of this generation (see the file header). -/
def udpBootInv (γu : UdpNames) (id : w64) (bn : UdpBootNames) : IProp GF :=
  inv (udpBootN .@ uint.nat id) (udpBootBody γu id bn)

instance udpBootInv_persistent γu id bn : Persistent (udpBootInv (GF := GF) γu id bn) := by
  unfold udpBootInv; infer_instance

/-- **What `nextBoot` takes** (see the file header). -/
def udpBootStart (γu : UdpNames) (id : w64) (dir : GoString) (bn : UdpBootNames) (qc : Qp) :
    IProp GF :=
  iprop(∃ cur : Option GoString,
    Fs.osInv ∗ Fs.osSharedInv bn.fR ∗ DurFs.durInv bn.γd bn.df ∗ DurFs.durHandle bn.γd bn.df bn.fR ∗
    Fs.osCallPerm (Fs.callKey bn.fR bn.df.d) qc ∗ udpBootInv γu id bn ∗
    ghostVar bn.wr (1 : Qp).half (⟨cur, none⟩ : DurFs.DurSt) ∗
    ⌜bn.df.Ok ∧ bn.df.name = kvBootFileName dir id⌝)

/-- **What a process's UDP side starts from** (`openUDP`'s, `startNodeUDP`'s): every valid address of
`M` with its invariant (`udpAddrsInv`) and the boot counter's file. -/
def udpProcStart (F : KvFacts GF) (γu : UdpNames) (id : w64) (dir : GoString) (M : GMap w64 GoString) :
    IProp GF :=
  iprop(udpAddrsInv F γu M ∗ ∃ (bn : UdpBootNames) (qc : Qp), udpBootStart γu id dir bn qc)

/-- What a generation's crash keeps of its boot file: the invariant, its token, `durable`'s invariant
and crash token. -/
def udpBootKeep (γu : UdpNames) (id : w64) (bn : UdpBootNames) : IProp GF :=
  iprop(udpBootInv γu id bn ∗ token bn.tk ∗ DurFs.durInv bn.γd bn.df ∗ DurFs.durCrashTok bn.γd ∗
    Fs.osSharedInv bn.fR)

/-! ## The boot file's laws -/

/-- `nroot.@a`'s mask misses the boot invariants', for `a ≠ "kvraft_udp"`. -/
theorem ndot_sub_udpBoot (a : String) (h : a ≠ "kvraft_udp") (x : Nat) :
    (↑(nroot .@ a) : CoPset) ⊆ ⊤ \ ↑(udpBootN .@ x) := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  have := mask_ndot_ne' nroot a "kvraft_udp" h _ hp
  rw [Iris.Std.LawfulSet.mem_diff] at this
  unfold udpBootN at h'
  exact this.2 (nclose_subseteq _ _ p (nclose_subseteq _ _ p h'))

/-- kvraft-udp's namespace is open inside `durable`'s atomic updates. -/
theorem kvraftUdpN_sub_durAu : (↑(nroot .@ "kvraft_udp") : CoPset) ⊆ DurFs.durAuMask := by
  intro x hx
  have h1 := mask_ndot_ne' nroot "kvraft_udp" "osfs" (by decide) x hx
  have h2 := mask_ndot_ne' nroot "kvraft_udp" "osfsShared" (by decide) x hx
  have h3 := mask_ndot_ne' nroot "kvraft_udp" "durable" (by decide) x hx
  rw [Iris.Std.LawfulSet.mem_diff] at h1 h2 h3
  unfold DurFs.durAuMask Fs.osAuMask
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, h1.2⟩, h2.2⟩, h3.2⟩

/-- The boot invariant is open inside `durable`'s atomic updates. -/
theorem udpBootN_sub_durAu (x : Nat) : (↑(udpBootN .@ x) : CoPset) ⊆ DurFs.durAuMask := by
  intro p hp
  unfold udpBootN at hp
  exact kvraftUdpN_sub_durAu p (nclose_subseteq _ _ p (nclose_subseteq _ _ p hp))

/-- The names' invariant is open inside `durable`'s atomic updates with a boot invariant open. -/
theorem udpMsgN_sub_boot (x : Nat) :
    (↑udpMsgN : CoPset) ⊆ DurFs.durAuMask \ ↑(udpBootN .@ x) := by
  intro p hp
  unfold udpMsgN at hp
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨kvraftUdpN_sub_durAu p (nclose_subseteq _ _ p hp), fun h' => ?_⟩
  have := mask_ndot_ne' (nroot .@ "kvraft_udp") "msgs" "boot" (by decide) p hp
  rw [Iris.Std.LawfulSet.mem_diff] at this
  unfold udpBootN at h'
  exact this.2 (nclose_subseteq _ _ p h')

/-- `bootVal` names one number. -/
theorem bootVal_inj {v : Option GoString} {n m : w64} (hn : bootVal v n) (hm : bootVal v m) :
    n = m := by
  rcases hn with ⟨rfl, rfl⟩ | rfl <;> rcases hm with ⟨h, rfl⟩ | h
  · rfl
  · cases h
  · cases h
  · exact u64Le_inj (Option.some.inj h)

/-- **The rename keeps `BootOk`**: from the file at `n`, its write of `n + 1` (no overflow). -/
theorem bootOk_rename {hi n : w64} {cur : Option GoString} (h : BootOk hi ⟨cur, none⟩)
    (hn : bootVal cur n) (hlt : uint.nat n < uint.nat (n + 1)) :
    BootOk hi ⟨some (u64Le (n + 1)), some cur⟩ := by
  obtain ⟨⟨m, hm, hle⟩, -⟩ := h
  obtain rfl := bootVal_inj hn hm
  refine ⟨⟨n + 1, Or.inr rfl, by omega⟩, fun old e => ?_⟩
  cases e
  exact ⟨n, hn, hle⟩

/-- **The names' facts at the sync** (`udp_boot_bump`): with replica `id`'s bound `hi ≤ n`, the
counter `(id, n + 1)` is fresh, and inserting it at `0` with the bound raised to `n + 1` keeps the
facts. -/
theorem udpMsgOk_bump {M : GMap MsgKey (List w8)} {T : GMap MsgKey Bool} {C : GMap (w64 × w64) w64}
    {H : GMap w64 w64} (hok : UdpMsgOk M T C H) (id hi n : w64) (hH : H !! id = some hi)
    (hn : uint.nat hi ≤ uint.nat n) (hlt : uint.nat n < uint.nat (n + 1)) :
    C !! ((id, n + 1) : w64 × w64) = none ∧
      UdpMsgOk M T (<[((id, n + 1) : w64 × w64) := W64 0]> C) (<[id := n + 1]> H) := by
  obtain ⟨h1, h2, h3⟩ := hok
  have hfresh : C !! ((id, n + 1) : w64 × w64) = none := by
    cases hc : C !! ((id, n + 1) : w64 × w64) with
    | none => rfl
    | some c =>
      obtain ⟨hi', hH', hle⟩ := h3 _ c hc
      simp only at hH' hle
      rw [hH] at hH'
      cases hH'
      omega
  refine ⟨hfresh, ?_, h2, ?_⟩
  · intro k hk
    obtain ⟨c, hc, hle⟩ := h1 k hk
    refine ⟨c, ?_, hle⟩
    have hne : ((id, n + 1) : w64 × w64) ≠ (k.1, k.2.1) := by
      intro e
      rw [e, hc] at hfresh
      cases hfresh
    rw [GMap.lookup_insert_ne _ _ hne]
    exact hc
  · intro fb c hc
    by_cases e : ((id, n + 1) : w64 × w64) = fb
    · subst e
      exact ⟨n + 1, GMap.lookup_insert _ _ _, Nat.le_refl _⟩
    · rw [GMap.lookup_insert_ne _ _ e] at hc
      obtain ⟨hi', hH', hle⟩ := h3 fb c hc
      by_cases e' : id = fb.1
      · rw [← e', hH] at hH'
        cases hH'
        refine ⟨n + 1, ?_, by omega⟩
        rw [← e']
        exact GMap.lookup_insert _ _ _
      · exact ⟨hi', by rw [GMap.lookup_insert_ne _ _ e']; exact hH', hle⟩

/-- **The sync's ghost step** (see the file header): with replica `id`'s bound `hi ≤ n`, the bound
raised to `n + 1` and the process `(id, n + 1)`'s counter allocated at `0`, in the names'
invariant. -/
theorem udp_boot_bump (γu : UdpNames) (id hi n : w64) (hn : uint.nat hi ≤ uint.nat n)
    (hlt : uint.nat n < uint.nat (n + 1)) (E : CoPset) (hE : ↑udpMsgN ⊆ E) :
    ⊢ udpMsgInv (GF := GF) γu -∗ udpHi γu id hi ={E}=∗
      udpHi γu id (n + 1) ∗ udpCtr γu id (n + 1) (W64 0) := by
  iintro #Hinv Hhi
  unfold udpMsgInv
  imod inv_acc hE $$ Hinv with ⟨Hb, Hclose⟩
  imod Hb with ⟨%M, %T, %C, %H, HM, HT, HC, HH, %hok⟩
  unfold udpHi
  ihave %hH := ghost_map_lookup $$ HH Hhi
  obtain ⟨hfresh, hok'⟩ := udpMsgOk_bump hok id hi n hH hn hlt
  imod ghost_map_update (n + 1) $$ HH Hhi with ⟨HH, Hhi⟩
  imod ghost_map_insert ((id, n + 1) : w64 × w64) (W64 0) hfresh $$ HC with ⟨HC, Hc⟩
  imod Hclose $$ [HM HT HC HH] with -
  · inext
    iexists M, T, _, _
    iframe HM HT HC HH
    ipureintro
    exact hok'
  imodintro
  unfold udpCtr
  iframe Hhi Hc

/-- **A generation's boot file invariant, allocated at its boot**, from `durable`'s client state
outside a window at `v`, whose number bounds `hi`. -/
theorem udp_boot_alloc (γu : UdpNames) (id : w64) (γd : DurFs.DurGS) (df : DurFs.DFile)
    (fR : Fs.Roots) (v : Option GoString) (hi n : w64) (hv : bootVal v n)
    (hn : uint.nat hi ≤ uint.nat n) (E : CoPset) :
    ⊢ DurFs.durSt (GF := GF) γd ⟨v, none⟩ -∗ udpHi γu id hi ={E}=∗
      ∃ (wr tk : GName), udpBootInv γu id ⟨γd, df, fR, wr, tk⟩ ∗
        ghostVar wr (1 : Qp).half (⟨v, none⟩ : DurFs.DurSt) ∗ token tk := by
  iintro Hds Hhi
  imod ghostVar_alloc (GF := GF) (⟨v, none⟩ : DurFs.DurSt) with ⟨%wr, Hw⟩
  icases (ghostVar_split_half (GF := GF) wr 1 (⟨v, none⟩ : DurFs.DurSt)).1 $$ Hw with ⟨Hw1, Hw2⟩
  imod token_alloc (GF := GF) with ⟨%tk, Htk⟩
  imod inv_alloc (udpBootN .@ uint.nat id) E (udpBootBody γu id ⟨γd, df, fR, wr, tk⟩)
    $$ [Hds Hw1 Hhi] with #Hinv
  · inext
    iunfold udpBootBody
    iexists ⟨v, none⟩
    iframe Hds Hw1
    ileft
    iexists hi
    iframe Hhi
    ipureintro
    exact ⟨⟨n, hv, hn⟩, fun _ h => by cases h⟩
  imodintro
  iexists wr, tk
  unfold udpBootInv
  iframe Hinv Hw2 Htk

/-- What a crash leaves (`cur`, or `alt`'s contents) holds a number at least `hi`. -/
theorem bootOk_crash {hi : w64} {s : DurFs.DurSt} (h : BootOk hi s) (v : Option GoString)
    (hv : v = s.cur ∨ s.alt = some v) : ∃ n, bootVal v n ∧ uint.nat hi ≤ uint.nat n := by
  rcases hv with rfl | hv
  · exact h.1
  · exact h.2 v hv

/-- **The boot file at a crash**: the invariant opened with its token (its contents are timeless: no
later credit), `durable`'s crash lemma on the boot file inside it (`durInv_crash`, after the files
another crash lemma took, `D`, none at the boot file's names), the invariant closed on its crashed
side. What the next generation finds at the boot file's names, and replica `id`'s `udpHi` bounded by
it. -/
theorem udp_boot_crash (γu : UdpNames) (id : w64) (bn : UdpBootNames) (L' : GooseLocalGS GF)
    (D : List Fs.Ino) (tt : Bool) (V' : Fs.Hist)
    (hD : ∀ i ∈ D, V'.now.entry bn.df.J bn.df.b ≠ some (.file i) ∧
      V'.now.entry bn.df.J bn.df.tb ≠ some (.file i)) :
    ⊢ udpBootKeep (GF := GF) γu id bn -∗ crashed (hC := hG.goose_localGS.goose_crashGS) -∗
      Fs.crashRest (fun _ _ => True) (Fs.gooseOsGS (L := hG.goose_localGS)) (Fs.gooseOsGS (L := L'))
        D tt V' ={⊤}=∗
      ∃ (v : Option GoString) (hi n : w64) (D' : List Fs.Ino),
        ⌜bootVal v n ∧ uint.nat hi ≤ uint.nat n⌝ ∗ udpHi γu id hi ∗
        DurFs.durFound (L := L') bn.df V'.now v ∗ DurFs.durFoundTmp (L := L') bn.df V'.now ∗
        Fs.crashRest (fun _ _ => True) (Fs.gooseOsGS (L := hG.goose_localGS))
          (Fs.gooseOsGS (L := L')) (D' ++ D) tt V' := by
  iintro Hk #Hcr Hrest
  unfold udpBootKeep
  icases Hk with ⟨#Hbi, Htk, #Hdi, Hdc, #Hsh⟩
  unfold udpBootInv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hbi with ⟨Hb, Hclose⟩
  iunfold udpBootBody at Hb
  imod later_exists_except0 $$ Hb with ⟨%s, Hb⟩
  icases Hb with ⟨>Hds, >Hwr, Hb⟩
  icases later_or.1 $$ Hb with (Hb | ⟨-, >Htk'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Htk Htk'
  iunfold udpHi at Hb
  imod later_exists_except0 $$ Hb with ⟨%hi, >Hhi, >%hok⟩
  imod DurFs.durInv_crash (fun _ _ => True) hG.goose_localGS L' bn.γd bn.df bn.fR D tt V' s
    (⊤ \ ↑(udpBootN .@ uint.nat id)) (ndot_sub_udpBoot "durable" (by decide) _)
    (ndot_sub_udpBoot "osfsShared" (by decide) _) hD $$ Hdi Hcr Hdc Hds Hsh Hrest
    with ⟨%v, %D', ⟨%hv, -⟩, Hds, Hf, Ht, Hrest⟩
  imod Hclose $$ [Hds Hwr Htk] with -
  · inext
    iunfold udpBootBody
    iexists s
    iframe Hds Hwr
    iright
    iframe Hcr Htk
  obtain ⟨n, hvn, hn⟩ := bootOk_crash hok v hv
  imodintro
  iexists v, hi, n, D'
  unfold udpHi
  iframe Hhi Hf Ht Hrest
  ipureintro
  exact ⟨hvn, hn⟩

/-- **The boot file at a generation's boot** (2026-11-24, with kvraft's `kvGen` claiming only the
storage file's names, `TopBoot.lean`): from the claim on the boot file's two names (out of what
`kvGen_first`/`kvGen_crash` hand back, `kvDirRest`, by `osNames_take2`: they are not the storage
file's, `kvBoot_names_fresh`), what the generation found there, a share of the root's call permission,
and replica `id`'s `udpHi` bounded by the found contents: `durable`'s boot on the two names
(`DurFs.durBootOnly`) and the boot invariant (`udp_boot_alloc`): `nextBoot`'s `udpBootStart` and what
the crash keeps. -/
theorem udp_gen_boot (γu : UdpNames) (id : w64) (dir : GoString) (f : DurFs.DFile) (R : Fs.Roots)
    (V : Fs.Hist) (v : Option GoString) (hi n : w64) (qc : Qp) (hV : V.2 = []) (hr : (f.d, f.J) ∈ R)
    (hf : f.Ok) (hname : f.name = kvBootFileName dir id) (hv : bootVal v n)
    (hn : uint.nat hi ≤ uint.nat n) :
    ⊢ Fs.osInv (GF := GF) -∗ Fs.osSharedInv R -∗ Fs.osCallPerm (Fs.callKey R f.d) qc -∗
      Fs.osNames f.J (.only [f.b, f.tb]) (DFrac.own 1) (Fs.namesOf V f.J (.only [f.b, f.tb])) -∗
      DurFs.durFound f V.now v -∗ DurFs.durFoundTmp f V.now -∗ udpHi γu id hi ={⊤}=∗
      ∃ bn : UdpBootNames, ⌜bn.df = f ∧ bn.fR = R⌝ ∗ udpBootStart γu id dir bn qc ∗
        udpBootKeep γu id bn := by
  iintro #Hos #Hsh Hcp Hj Hf Ht Hhi
  imod DurFs.durBootOnly _ f R V v ⊤ hV hr (fun _ _ => CoPset.mem_full) $$ Hsh Hj Hf Ht
    with ⟨%γd, #Hdi, Hdh, Hds, Hdc⟩
  imod udp_boot_alloc γu id γd f R v hi n hv hn ⊤ $$ Hds Hhi with ⟨%wr, %tk, #Hbi, Hwr, Htk⟩
  imodintro
  iexists ⟨γd, f, R, wr, tk⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hdh Hcp Hwr]
  · unfold udpBootStart
    iexists v
    iframe Hos Hsh Hdi Hdh Hcp Hbi Hwr
    ipureintro; exact ⟨hf, hname⟩
  · unfold udpBootKeep
    iframe Hbi Htk Hdi Hdc Hsh

end defs

end kvraft
end EtcdGrove
end Perennial
