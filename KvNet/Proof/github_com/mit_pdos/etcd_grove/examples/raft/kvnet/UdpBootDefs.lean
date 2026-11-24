/-
# kvudp's boot counter: its file, crash-aware (2026-11-24)

`notes/kvudp-proof-plan.md`, "The boot counter". Each process of replica `id` takes a boot number one
more than the last process's (`nextBoot`), from the durable file `bootFileName dir id`
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
  handle's holder between the read and the write, as kvnet's `kdWriter`.
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

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Defs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

/-- The file of replica `id`'s boot counter (the program's string): `dir + "/udp-boot-" + itoa(id)`. -/
def bootFileName (dir : GoString) (id : w64) : GoString :=
  dir ++ go!"/udp-boot-" ++ decimalB (uint.nat id)

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
def udpBootN : Namespace := (nroot .@ "kvudp") .@ "boot"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]
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
    ⌜bn.df.Ok ∧ bn.df.name = bootFileName dir id⌝)

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

/-! ## The boot file's laws (phase 2) -/

/-- **A generation's boot file invariant, allocated at its boot**, from `durable`'s client state
outside a window at `v`, whose number bounds `hi`. -/
theorem udp_boot_alloc (γu : UdpNames) (id : w64) (γd : DurFs.DurGS) (df : DurFs.DFile)
    (fR : Fs.Roots) (v : Option GoString) (hi n : w64) (hv : bootVal v n)
    (hn : uint.nat hi ≤ uint.nat n) (E : CoPset) :
    ⊢ DurFs.durSt (GF := GF) γd ⟨v, none⟩ -∗ udpHi γu id hi ={E}=∗
      ∃ (wr tk : GName), udpBootInv γu id ⟨γd, df, fR, wr, tk⟩ ∗
        ghostVar wr (1 : Qp).half (⟨v, none⟩ : DurFs.DurSt) ∗ token tk := by
  sorry

/-- **The boot file at a crash**: the invariant opened with its token (one later credit strips its
contents), `durable`'s client state and the bound, the invariant closed on its crashed side. -/
theorem udp_boot_crash (γu : UdpNames) (id : w64) (bn : UdpBootNames) (E : CoPset)
    (hE : ↑(udpBootN .@ uint.nat id) ⊆ E) :
    ⊢ udpBootInv (GF := GF) γu id bn -∗ token bn.tk -∗ crashed -∗ £ 1 ={E}=∗
      ∃ (s : DurFs.DurSt) (hi : w64), DurFs.durSt bn.γd s ∗ udpHi γu id hi ∗ ⌜BootOk hi s⌝ := by
  sorry

/-- What a crash leaves (`cur`, or `alt`'s contents) holds a number at least `hi`. -/
theorem bootOk_crash {hi : w64} {s : DurFs.DurSt} (h : BootOk hi s) (v : Option GoString)
    (hv : v = s.cur ∨ s.alt = some v) : ∃ n, bootVal v n ∧ uint.nat hi ≤ uint.nat n := by
  rcases hv with rfl | hv
  · exact h.1
  · exact h.2 v hv

end defs

end raft_kvnet
end EtcdGrove
end Perennial
