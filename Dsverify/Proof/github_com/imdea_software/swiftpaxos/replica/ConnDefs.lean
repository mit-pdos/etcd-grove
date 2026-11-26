/-
The definitions, specs and lemmas of `Conn.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnAddr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetConn
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Fatal
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Printf
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Results
public import Perennial.Proof.encoding.binary.Results

-- PORT: lab imports dropped: Harness.Proof.net.Listen, Harness.Proof.net.TCPListener__Accept

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [io.Assumptions] [net.rpc.Assumptions]
  [errors.Assumptions] [dlog.Assumptions] [time.Assumptions]
  [strings.Assumptions] [encoding.binary.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- A rejected peer id: log, close the connection, next. -/
local macro "reject" : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨-, -⟩
  try wp_auto
  wp_apply replica.wp_Println wp_Println $$ [Hlg Hq]
  · iframe Hlg Hq
  try wp_auto
  wp_apply net.TCPConn.Close.labProof c cid true $$ [Hown] as %e3 -
  · iframe Hown
  wp_for_post
  iframe
  iexists _, pcsl, pcs, _
  iframe
  ipureintro; exact hbb'))

/-- The promoted `r.Fatal(...)` (the embedded quiet logger's: it returns). -/
theorem replica.wp_Fatal (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (r lg : Loc) (sl : GoSlice) :
    {{ replica.fld r go!"Logger" ↦□ lg ∗ dlog.quiet (GF := netDistGF) lg }}
      (App (Val #(methods (go.GoType.PointerType replica.Replica.ty) go!"Fatal" #r)) (Val #sl))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlg, #Hq⟩
  wp_auto
  wp_apply wp_Fatal $$ [$Hq]
  wp_end

theorem replica.wp_Println (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (r lg : Loc) (sl : GoSlice) :
    {{ replica.fld r go!"Logger" ↦□ lg ∗ dlog.quiet (GF := netDistGF) lg }}
      (App (Val #(methods (go.GoType.PointerType replica.Replica.ty) go!"Println" #r)) (Val #sl))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlg, #Hq⟩
  wp_auto
  wp_apply wp_Println $$ [$Hq]
  wp_end

theorem replica.wp_Printf (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (r lg : Loc) (f : GoString) (sl : GoSlice) :
    {{ replica.fld r go!"Logger" ↦□ lg ∗ dlog.quiet (GF := netDistGF) lg }}
      (App (App (Val #(methods (go.GoType.PointerType replica.Replica.ty) go!"Printf" #r)) (Val #f))
        (Val #sl))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlg, #Hq⟩
  wp_auto
  wp_apply wp_Printf $$ [$Hq]
  wp_end

/-- The 5-byte buffer `bs`: its part `bs[1:]`, and back with any 4 bytes there. -/
theorem replica.bs5_acc (p : Loc) (bb : List w8) (hb : bb.length = 5) :
    (slice.mk p (W64 5) (W64 5) ↦* bb : IProp netDistGF) ⊢
      slice.slice (slice.mk p (W64 5) (W64 5)) w8 (W64 1) (W64 5) ↦*
        subslice (sint.nat (W64 1)) (sint.nat (W64 5)) bb ∗
      (∀ m : List w8, ⌜m.length = 4⌝ -∗
        slice.slice (slice.mk p (W64 5) (W64 5)) w8 (W64 1) (W64 5) ↦* m -∗
        slice.mk p (W64 5) (W64 5) ↦* (bb.take 1 ++ m)) := by
  have hsl5 : sint.Z (slice.mk p (W64 5) (W64 5)).len = 5 := rfl
  obtain ⟨x0, x1, x2, x3, x4, rfl⟩ : ∃ x0 x1 x2 x3 x4 : w8, bb = [x0, x1, x2, x3, x4] := by
    match bb, hb with
    | [x0, x1, x2, x3, x4], _ => exact ⟨x0, x1, x2, x3, x4, rfl⟩
  iintro Hsl
  icases (ownSlice_slice (W64 1) (W64 5) _ _ _ ⟨by decide, by decide, by rw [hsl5]; decide⟩).1
    $$ Hsl with ⟨Hs0, Hs1, Hs2⟩
  iframe Hs1
  iintro %m %Hm Hs1
  obtain ⟨y1, y2, y3, y4, rfl⟩ : ∃ y1 y2 y3 y4 : w8, m = [y1, y2, y3, y4] := by
    match m, Hm with
    | [y1, y2, y3, y4], _ => exact ⟨y1, y2, y3, y4, rfl⟩
  iapply (ownSlice_slice (W64 1) (W64 5) _ _ ([x0, x1, x2, x3, x4].take 1 ++ [y1, y2, y3, y4])
    ⟨by decide, by decide, by rw [hsl5]; decide⟩).2
  iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos
